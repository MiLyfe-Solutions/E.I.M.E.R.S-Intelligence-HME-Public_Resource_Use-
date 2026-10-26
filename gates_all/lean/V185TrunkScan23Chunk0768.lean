import V185TrunkScan23Chunk0767

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4541726 : List Nat := [4, 3, 2, 1, 2, 2, 2, 2, 5]
def baseStart_4541726 : Nat := 118140960795 + 4541726 * 2 ^ 59
def prefixEnd_4541726 : Nat := 4983230072969 + 3 ^ 40 * 4541726 * 2
def baseEnd_4541726 : Nat := 259120937669111412204221

theorem tailTrace_4541726 : CollatzResearch.WordTrace tailWord_4541726 prefixEnd_4541726 259120937669111412204221 := by
  unfold tailWord_4541726
  simp only [CollatzResearch.WordTrace]
  refine ⟨20706294493013730236507629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110433570629406561261374021 20706294493013730236507629)
  ·
    refine ⟨7764860434880148838690361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20706294493013730236507629 7764860434880148838690361)
    ·
      refine ⟨5823645326160111629017771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7764860434880148838690361 5823645326160111629017771)
      ·
        refine ⟨8735467989240167443526657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5823645326160111629017771 8735467989240167443526657)
        ·
          refine ⟨6551600991930125582644993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8735467989240167443526657 6551600991930125582644993)
          ·
            refine ⟨4913700743947594186983745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6551600991930125582644993 4913700743947594186983745)
            ·
              refine ⟨3685275557960695640237809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4913700743947594186983745 3685275557960695640237809)
              ·
                refine ⟨2763956668470521730178357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3685275557960695640237809 2763956668470521730178357)
                ·
                  refine ⟨259120937669111412204221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2763956668470521730178357 259120937669111412204221)
                  ·
                    rfl

theorem cell23_4541726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 2, 2, 5].length) (baseStart_4541726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4541726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4541726 prefixEnd_4541726 := by exact prefixLift 4541726
  have htrace : WordTrace (prefixWord ++ tailWord_4541726) baseStart_4541726 baseEnd_4541726 := by
    simpa [prefixWord, tailWord_4541726, baseEnd_4541726] using wordTrace_append hprefix tailTrace_4541726
  have hstable : (prefixWord ++ tailWord_4541726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4541726).length < 2 ^ (prefixWord ++ tailWord_4541726).sum := by decide
  have hdescent : baseEnd_4541726 < baseStart_4541726 := by decide
  rcases family_descends (prefixWord ++ tailWord_4541726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4541785 : List Nat := [1, 2, 1, 2, 2, 2, 2, 4, 2, 3, 2]
def baseStart_4541785 : Nat := 118140960795 + 4541785 * 2 ^ 59
def prefixEnd_4541785 : Nat := 4983230072969 + 3 ^ 40 * 4541785 * 2
def baseEnd_4541785 : Nat := 2332118734380617979000217

theorem tailTrace_4541785 : CollatzResearch.WordTrace tailWord_4541785 prefixEnd_4541785 2332118734380617979000217 := by
  unfold tailWord_4541785
  simp only [CollatzResearch.WordTrace]
  refine ⟨165652507850896094968458809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110435005233930729978972539 165652507850896094968458809)
  ·
    refine ⟨124239380888172071226344107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165652507850896094968458809 124239380888172071226344107)
    ·
      refine ⟨186359071332258106839516161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124239380888172071226344107 186359071332258106839516161)
      ·
        refine ⟨139769303499193580129637121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186359071332258106839516161 139769303499193580129637121)
        ·
          refine ⟨104826977624395185097227841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139769303499193580129637121 104826977624395185097227841)
          ·
            refine ⟨78620233218296388822920881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104826977624395185097227841 78620233218296388822920881)
            ·
              refine ⟨58965174913722291617190661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78620233218296388822920881 58965174913722291617190661)
              ·
                refine ⟨11055970296322929678223249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58965174913722291617190661 11055970296322929678223249)
                ·
                  refine ⟨8291977722242197258667437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11055970296322929678223249 8291977722242197258667437)
                  ·
                    refine ⟨3109491645840823972000289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8291977722242197258667437 3109491645840823972000289)
                    ·
                      refine ⟨2332118734380617979000217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3109491645840823972000289 2332118734380617979000217)
                      ·
                        rfl

theorem cell23_4541785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 4, 2, 3, 2].length) (baseStart_4541785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4541785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4541785 prefixEnd_4541785 := by exact prefixLift 4541785
  have htrace : WordTrace (prefixWord ++ tailWord_4541785) baseStart_4541785 baseEnd_4541785 := by
    simpa [prefixWord, tailWord_4541785, baseEnd_4541785] using wordTrace_append hprefix tailTrace_4541785
  have hstable : (prefixWord ++ tailWord_4541785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4541785).length < 2 ^ (prefixWord ++ tailWord_4541785).sum := by decide
  have hdescent : baseEnd_4541785 < baseStart_4541785 := by decide
  rcases family_descends (prefixWord ++ tailWord_4541785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4541792 : List Nat := [2, 1, 1, 3, 4, 2, 2, 1, 3, 1, 3]
def baseStart_4541792 : Nat := 118140960795 + 4541792 * 2 ^ 59
def prefixEnd_4541792 : Nat := 4983230072969 + 3 ^ 40 * 4541792 * 2
def baseEnd_4541792 : Nat := 2332122328745199451612685

theorem tailTrace_4541792 : CollatzResearch.WordTrace tailWord_4541792 prefixEnd_4541792 2332122328745199451612685 := by
  unfold tailWord_4541792
  simp only [CollatzResearch.WordTrace]
  refine ⟨82826381580935367581981815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110435175441247156775975753 82826381580935367581981815)
  ·
    refine ⟨124239572371403051372972723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82826381580935367581981815 124239572371403051372972723)
    ·
      refine ⟨186359358557104577059459085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124239572371403051372972723 186359358557104577059459085)
      ·
        refine ⟨69884759458914216397297157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 186359358557104577059459085 69884759458914216397297157)
        ·
          refine ⟨13103392398546415574493217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69884759458914216397297157 13103392398546415574493217)
          ·
            refine ⟨9827544298909811680869913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13103392398546415574493217 9827544298909811680869913)
            ·
              refine ⟨7370658224182358760652435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9827544298909811680869913 7370658224182358760652435)
              ·
                refine ⟨11055987336273538140978653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7370658224182358760652435 11055987336273538140978653)
                ·
                  refine ⟨4145995251102576802866995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11055987336273538140978653 4145995251102576802866995)
                  ·
                    refine ⟨6218992876653865204300493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4145995251102576802866995 6218992876653865204300493)
                    ·
                      refine ⟨2332122328745199451612685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6218992876653865204300493 2332122328745199451612685)
                      ·
                        rfl

theorem cell23_4541792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 1, 3, 1, 3].length) (baseStart_4541792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4541792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4541792 prefixEnd_4541792 := by exact prefixLift 4541792
  have htrace : WordTrace (prefixWord ++ tailWord_4541792) baseStart_4541792 baseEnd_4541792 := by
    simpa [prefixWord, tailWord_4541792, baseEnd_4541792] using wordTrace_append hprefix tailTrace_4541792
  have hstable : (prefixWord ++ tailWord_4541792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4541792).length < 2 ^ (prefixWord ++ tailWord_4541792).sum := by decide
  have hdescent : baseEnd_4541792 < baseStart_4541792 := by decide
  rcases family_descends (prefixWord ++ tailWord_4541792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4541815 : List Nat := [1, 1, 3, 1, 1, 2, 6, 2, 1, 1, 4]
def baseStart_4541815 : Nat := 118140960795 + 4541815 * 2 ^ 59
def prefixEnd_4541815 : Nat := 4983230072969 + 3 ^ 40 * 4541815 * 2
def baseEnd_4541815 : Nat := 2332134138800252861625079

theorem tailTrace_4541815 : CollatzResearch.WordTrace tailWord_4541815 prefixEnd_4541815 2332134138800252861625079 := by
  unfold tailWord_4541815
  simp only [CollatzResearch.WordTrace]
  refine ⟨165653602040787410092050899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110435734693858273394700599 165653602040787410092050899)
  ·
    refine ⟨248480403061181115138076349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165653602040787410092050899 248480403061181115138076349)
    ·
      refine ⟨93180151147942918176778631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 248480403061181115138076349 93180151147942918176778631)
      ·
        refine ⟨139770226721914377265167947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93180151147942918176778631 139770226721914377265167947)
        ·
          refine ⟨209655340082871565897751921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139770226721914377265167947 209655340082871565897751921)
          ·
            refine ⟨157241505062153674423313941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 209655340082871565897751921 157241505062153674423313941)
            ·
              refine ⟨7370695549788453488592841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 157241505062153674423313941 7370695549788453488592841)
              ·
                refine ⟨5528021662341340116444631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7370695549788453488592841 5528021662341340116444631)
                ·
                  refine ⟨8292032493512010174666947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5528021662341340116444631 8292032493512010174666947)
                  ·
                    refine ⟨12438048740268015262000421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8292032493512010174666947 12438048740268015262000421)
                    ·
                      refine ⟨2332134138800252861625079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12438048740268015262000421 2332134138800252861625079)
                      ·
                        rfl

theorem cell23_4541815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 2, 1, 1, 4].length) (baseStart_4541815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4541815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4541815 prefixEnd_4541815 := by exact prefixLift 4541815
  have htrace : WordTrace (prefixWord ++ tailWord_4541815) baseStart_4541815 baseEnd_4541815 := by
    simpa [prefixWord, tailWord_4541815, baseEnd_4541815] using wordTrace_append hprefix tailTrace_4541815
  have hstable : (prefixWord ++ tailWord_4541815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4541815).length < 2 ^ (prefixWord ++ tailWord_4541815).sum := by decide
  have hdescent : baseEnd_4541815 < baseStart_4541815 := by decide
  rcases family_descends (prefixWord ++ tailWord_4541815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4541835 : List Nat := [1, 1, 1, 1, 4, 3, 1, 5, 1, 2, 3]
def baseStart_4541835 : Nat := 118140960795 + 4541835 * 2 ^ 59
def prefixEnd_4541835 : Nat := 4983230072969 + 3 ^ 40 * 4541835 * 2
def baseEnd_4541835 : Nat := 2332144408413342783374987

theorem tailTrace_4541835 : CollatzResearch.WordTrace tailWord_4541835 prefixEnd_4541835 2332144408413342783374987 := by
  unfold tailWord_4541835
  simp only [CollatzResearch.WordTrace]
  refine ⟨165654331500714953507778959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110436221000476635671852639 165654331500714953507778959)
  ·
    refine ⟨248481497251072430261668439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165654331500714953507778959 248481497251072430261668439)
    ·
      refine ⟨372722245876608645392502659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248481497251072430261668439 372722245876608645392502659)
      ·
        refine ⟨559083368814912968088753989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 372722245876608645392502659 559083368814912968088753989)
        ·
          refine ⟨104828131652796181516641373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 559083368814912968088753989 104828131652796181516641373)
          ·
            refine ⟨39310549369798568068740515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 104828131652796181516641373 39310549369798568068740515)
            ·
              refine ⟨58965824054697852103110773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39310549369798568068740515 58965824054697852103110773)
              ·
                refine ⟨5528046005127923634666635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 58965824054697852103110773 5528046005127923634666635)
                ·
                  refine ⟨8292069007691885451999953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5528046005127923634666635 8292069007691885451999953)
                  ·
                    refine ⟨6219051755768914088999965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8292069007691885451999953 6219051755768914088999965)
                    ·
                      refine ⟨2332144408413342783374987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6219051755768914088999965 2332144408413342783374987)
                      ·
                        rfl

theorem cell23_4541835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 5, 1, 2, 3].length) (baseStart_4541835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4541835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4541835 prefixEnd_4541835 := by exact prefixLift 4541835
  have htrace : WordTrace (prefixWord ++ tailWord_4541835) baseStart_4541835 baseEnd_4541835 := by
    simpa [prefixWord, tailWord_4541835, baseEnd_4541835] using wordTrace_append hprefix tailTrace_4541835
  have hstable : (prefixWord ++ tailWord_4541835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4541835).length < 2 ^ (prefixWord ++ tailWord_4541835).sum := by decide
  have hdescent : baseEnd_4541835 < baseStart_4541835 := by decide
  rcases family_descends (prefixWord ++ tailWord_4541835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4541849 : List Nat := [1, 2, 1, 2, 1, 7, 1, 1, 3, 2, 2]
def baseStart_4541849 : Nat := 118140960795 + 4541849 * 2 ^ 59
def prefixEnd_4541849 : Nat := 4983230072969 + 3 ^ 40 * 4541849 * 2
def baseEnd_4541849 : Nat := 2332151597142505728599923

theorem tailTrace_4541849 : CollatzResearch.WordTrace tailWord_4541849 prefixEnd_4541849 2332151597142505728599923 := by
  unfold tailWord_4541849
  simp only [CollatzResearch.WordTrace]
  refine ⟨165654842122664233898788601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110436561415109489265859067 165654842122664233898788601)
  ·
    refine ⟨124241131591998175424091451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165654842122664233898788601 124241131591998175424091451)
    ·
      refine ⟨186361697387997263136137177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124241131591998175424091451 186361697387997263136137177)
      ·
        refine ⟨139771273040997947352102883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186361697387997263136137177 139771273040997947352102883)
        ·
          refine ⟨209656909561496921028154325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139771273040997947352102883 209656909561496921028154325)
          ·
            refine ⟨4913833817847584086597367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 209656909561496921028154325 4913833817847584086597367)
            ·
              refine ⟨7370750726771376129896051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4913833817847584086597367 7370750726771376129896051)
              ·
                refine ⟨11056126090157064194844077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7370750726771376129896051 11056126090157064194844077)
                ·
                  refine ⟨4146047283808899073066529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11056126090157064194844077 4146047283808899073066529)
                  ·
                    refine ⟨3109535462856674304799897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4146047283808899073066529 3109535462856674304799897)
                    ·
                      refine ⟨2332151597142505728599923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3109535462856674304799897 2332151597142505728599923)
                      ·
                        rfl

theorem cell23_4541849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 1, 3, 2, 2].length) (baseStart_4541849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4541849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4541849 prefixEnd_4541849 := by exact prefixLift 4541849
  have htrace : WordTrace (prefixWord ++ tailWord_4541849) baseStart_4541849 baseEnd_4541849 := by
    simpa [prefixWord, tailWord_4541849, baseEnd_4541849] using wordTrace_append hprefix tailTrace_4541849
  have hstable : (prefixWord ++ tailWord_4541849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4541849).length < 2 ^ (prefixWord ++ tailWord_4541849).sum := by decide
  have hdescent : baseEnd_4541849 < baseStart_4541849 := by decide
  rcases family_descends (prefixWord ++ tailWord_4541849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4541869 : List Nat := [1, 5, 2, 2, 1, 1, 3, 2, 1, 2, 3]
def baseStart_4541869 : Nat := 118140960795 + 4541869 * 2 ^ 59
def prefixEnd_4541869 : Nat := 4983230072969 + 3 ^ 40 * 4541869 * 2
def baseEnd_4541869 : Nat := 2332161866755595650349831

theorem tailTrace_4541869 : CollatzResearch.WordTrace tailWord_4541869 prefixEnd_4541869 2332161866755595650349831 := by
  unfold tailWord_4541869
  simp only [CollatzResearch.WordTrace]
  refine ⟨165655571582591777314516661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110437047721727851543011107 165655571582591777314516661)
  ·
    refine ⟨15530209835867979123235937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 165655571582591777314516661 15530209835867979123235937)
    ·
      refine ⟨11647657376900984342426953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15530209835867979123235937 11647657376900984342426953)
      ·
        refine ⟨8735743032675738256820215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11647657376900984342426953 8735743032675738256820215)
        ·
          refine ⟨13103614549013607385230323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8735743032675738256820215 13103614549013607385230323)
          ·
            refine ⟨19655421823520411077845485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13103614549013607385230323 19655421823520411077845485)
            ·
              refine ⟨7370783183820154154192057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19655421823520411077845485 7370783183820154154192057)
              ·
                refine ⟨5528087387865115615644043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7370783183820154154192057 5528087387865115615644043)
                ·
                  refine ⟨8292131081797673423466065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5528087387865115615644043 8292131081797673423466065)
                  ·
                    refine ⟨6219098311348255067599549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8292131081797673423466065 6219098311348255067599549)
                    ·
                      refine ⟨2332161866755595650349831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6219098311348255067599549 2332161866755595650349831)
                      ·
                        rfl

theorem cell23_4541869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_4541869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4541869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4541869 prefixEnd_4541869 := by exact prefixLift 4541869
  have htrace : WordTrace (prefixWord ++ tailWord_4541869) baseStart_4541869 baseEnd_4541869 := by
    simpa [prefixWord, tailWord_4541869, baseEnd_4541869] using wordTrace_append hprefix tailTrace_4541869
  have hstable : (prefixWord ++ tailWord_4541869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4541869).length < 2 ^ (prefixWord ++ tailWord_4541869).sum := by decide
  have hdescent : baseEnd_4541869 < baseStart_4541869 := by decide
  rcases family_descends (prefixWord ++ tailWord_4541869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4541950 : List Nat := [4, 2, 2, 3, 2, 1, 1, 2, 2, 1, 3]
def baseStart_4541950 : Nat := 118140960795 + 4541950 * 2 ^ 59
def prefixEnd_4541950 : Nat := 4983230072969 + 3 ^ 40 * 4541950 * 2
def baseEnd_4541950 : Nat := 2332203458688609833436959

theorem tailTrace_4541950 : CollatzResearch.WordTrace tailWord_4541950 prefixEnd_4541950 2332203458688609833436959 := by
  unfold tailWord_4541950
  simp only [CollatzResearch.WordTrace]
  refine ⟨20707315736912291018526913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110439017263532218765476869 20707315736912291018526913)
  ·
    refine ⟨15530486802684218263895185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20707315736912291018526913 15530486802684218263895185)
    ·
      refine ⟨11647865102013163697921389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15530486802684218263895185 11647865102013163697921389)
      ·
        refine ⟨4367949413254936386720521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11647865102013163697921389 4367949413254936386720521)
        ·
          refine ⟨3275962059941202290040391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4367949413254936386720521 3275962059941202290040391)
          ·
            refine ⟨4913943089911803435060587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3275962059941202290040391 4913943089911803435060587)
            ·
              refine ⟨7370914634867705152590881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4913943089911803435060587 7370914634867705152590881)
              ·
                refine ⟨5528185976150778864443161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7370914634867705152590881 5528185976150778864443161)
                ·
                  refine ⟨4146139482113084148332371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5528185976150778864443161 4146139482113084148332371)
                  ·
                    refine ⟨6219209223169626222498557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4146139482113084148332371 6219209223169626222498557)
                    ·
                      refine ⟨2332203458688609833436959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6219209223169626222498557 2332203458688609833436959)
                      ·
                        rfl

theorem cell23_4541950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_4541950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4541950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4541950 prefixEnd_4541950 := by exact prefixLift 4541950
  have htrace : WordTrace (prefixWord ++ tailWord_4541950) baseStart_4541950 baseEnd_4541950 := by
    simpa [prefixWord, tailWord_4541950, baseEnd_4541950] using wordTrace_append hprefix tailTrace_4541950
  have hstable : (prefixWord ++ tailWord_4541950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4541950).length < 2 ^ (prefixWord ++ tailWord_4541950).sum := by decide
  have hdescent : baseEnd_4541950 < baseStart_4541950 := by decide
  rcases family_descends (prefixWord ++ tailWord_4541950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4541956 : List Nat := [2, 3, 2, 3, 2, 1, 1, 1, 4, 2, 2]
def baseStart_4541956 : Nat := 118140960795 + 4541956 * 2 ^ 59
def prefixEnd_4541956 : Nat := 4983230072969 + 3 ^ 40 * 4541956 * 2
def baseEnd_4541956 : Nat := 2332206539572536809961931

theorem tailTrace_4541956 : CollatzResearch.WordTrace tailWord_4541956 prefixEnd_4541956 2332206539572536809961931 := by
  unfold tailWord_4541956
  simp only [CollatzResearch.WordTrace]
  refine ⟨82829372366638295586466861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110439163155517727448622481 82829372366638295586466861)
  ·
    refine ⟨31061014637489360844925073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82829372366638295586466861 31061014637489360844925073)
    ·
      refine ⟨23295760978117020633693805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31061014637489360844925073 23295760978117020633693805)
      ·
        refine ⟨8735910366793882737635177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23295760978117020633693805 8735910366793882737635177)
        ·
          refine ⟨6551932775095412053226383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8735910366793882737635177 6551932775095412053226383)
          ·
            refine ⟨9827899162643118079839575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6551932775095412053226383 9827899162643118079839575)
            ·
              refine ⟨14741848743964677119759363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9827899162643118079839575 14741848743964677119759363)
              ·
                refine ⟨22112773115947015679639045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14741848743964677119759363 22112773115947015679639045)
                ·
                  refine ⟨4146144959240065439932321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22112773115947015679639045 4146144959240065439932321)
                  ·
                    refine ⟨3109608719430049079949241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4146144959240065439932321 3109608719430049079949241)
                    ·
                      refine ⟨2332206539572536809961931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3109608719430049079949241 2332206539572536809961931)
                      ·
                        rfl

theorem cell23_4541956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_4541956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4541956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4541956 prefixEnd_4541956 := by exact prefixLift 4541956
  have htrace : WordTrace (prefixWord ++ tailWord_4541956) baseStart_4541956 baseEnd_4541956 := by
    simpa [prefixWord, tailWord_4541956, baseEnd_4541956] using wordTrace_append hprefix tailTrace_4541956
  have hstable : (prefixWord ++ tailWord_4541956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4541956).length < 2 ^ (prefixWord ++ tailWord_4541956).sum := by decide
  have hdescent : baseEnd_4541956 < baseStart_4541956 := by decide
  rcases family_descends (prefixWord ++ tailWord_4541956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4541962 : List Nat := [3, 1, 2, 2, 2, 2, 2, 4, 5]
def baseStart_4541962 : Nat := 118140960795 + 4541962 * 2 ^ 59
def prefixEnd_4541962 : Nat := 4983230072969 + 3 ^ 40 * 4541962 * 2
def baseEnd_4541962 : Nat := 259134402272940420720767

theorem tailTrace_4541962 : CollatzResearch.WordTrace tailWord_4541962 prefixEnd_4541962 259134402272940420720767 := by
  unfold tailWord_4541962
  simp only [CollatzResearch.WordTrace]
  refine ⟨41414740892813713549413035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110439309047503236131768093 41414740892813713549413035)
  ·
    refine ⟨62122111339220570324119553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41414740892813713549413035 62122111339220570324119553)
    ·
      refine ⟨46591583504415427743089665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62122111339220570324119553 46591583504415427743089665)
      ·
        refine ⟨34943687628311570807317249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46591583504415427743089665 34943687628311570807317249)
        ·
          refine ⟨26207765721233678105487937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34943687628311570807317249 26207765721233678105487937)
          ·
            refine ⟨19655824290925258579115953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26207765721233678105487937 19655824290925258579115953)
            ·
              refine ⟨14741868218193943934336965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19655824290925258579115953 14741868218193943934336965)
              ·
                refine ⟨2764100290911364487688181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14741868218193943934336965 2764100290911364487688181)
                ·
                  refine ⟨259134402272940420720767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2764100290911364487688181 259134402272940420720767)
                  ·
                    rfl

theorem cell23_4541962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 4, 5].length) (baseStart_4541962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4541962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4541962 prefixEnd_4541962 := by exact prefixLift 4541962
  have htrace : WordTrace (prefixWord ++ tailWord_4541962) baseStart_4541962 baseEnd_4541962 := by
    simpa [prefixWord, tailWord_4541962, baseEnd_4541962] using wordTrace_append hprefix tailTrace_4541962
  have hstable : (prefixWord ++ tailWord_4541962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4541962).length < 2 ^ (prefixWord ++ tailWord_4541962).sum := by decide
  have hdescent : baseEnd_4541962 < baseStart_4541962 := by decide
  rcases family_descends (prefixWord ++ tailWord_4541962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4542069 : List Nat := [1, 3, 4, 2, 1, 2, 2, 2, 6]
def baseStart_4542069 : Nat := 118140960795 + 4542069 * 2 ^ 59
def prefixEnd_4542069 : Nat := 4983230072969 + 3 ^ 40 * 4542069 * 2
def baseEnd_4542069 : Nat := 259140506987388318649879

theorem tailTrace_4542069 : CollatzResearch.WordTrace tailWord_4542069 prefixEnd_4542069 259140506987388318649879 := by
  unfold tailWord_4542069
  simp only [CollatzResearch.WordTrace]
  refine ⟨165662866181867211471797261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110441910787911474314531507 165662866181867211471797261)
  ·
    refine ⟨62123574818200204301923973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165662866181867211471797261 62123574818200204301923973)
    ·
      refine ⟨11648170278412538306610745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62123574818200204301923973 11648170278412538306610745)
      ·
        refine ⟨8736127708809403729958059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11648170278412538306610745 8736127708809403729958059)
        ·
          refine ⟨13104191563214105594937089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8736127708809403729958059 13104191563214105594937089)
          ·
            refine ⟨9828143672410579196202817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13104191563214105594937089 9828143672410579196202817)
            ·
              refine ⟨7371107754307934397152113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9828143672410579196202817 7371107754307934397152113)
              ·
                refine ⟨5528330815730950797864085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7371107754307934397152113 5528330815730950797864085)
                ·
                  refine ⟨259140506987388318649879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5528330815730950797864085 259140506987388318649879)
                  ·
                    rfl

theorem cell23_4542069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 2, 6].length) (baseStart_4542069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4542069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4542069 prefixEnd_4542069 := by exact prefixLift 4542069
  have htrace : WordTrace (prefixWord ++ tailWord_4542069) baseStart_4542069 baseEnd_4542069 := by
    simpa [prefixWord, tailWord_4542069, baseEnd_4542069] using wordTrace_append hprefix tailTrace_4542069
  have hstable : (prefixWord ++ tailWord_4542069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4542069).length < 2 ^ (prefixWord ++ tailWord_4542069).sum := by decide
  have hdescent : baseEnd_4542069 < baseStart_4542069 := by decide
  rcases family_descends (prefixWord ++ tailWord_4542069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4542105 : List Nat := [1, 2, 1, 2, 1, 2, 2, 1, 5, 1, 5]
def baseStart_4542105 : Nat := 118140960795 + 4542105 * 2 ^ 59
def prefixEnd_4542105 : Nat := 4983230072969 + 3 ^ 40 * 4542105 * 2
def baseEnd_4542105 : Nat := 2332283048190056726998745

theorem tailTrace_4542105 : CollatzResearch.WordTrace tailWord_4542105 prefixEnd_4542105 2332283048190056726998745 := by
  unfold tailWord_4542105
  simp only [CollatzResearch.WordTrace]
  refine ⟨165664179209736789620107769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110442786139824526413405179 165664179209736789620107769)
  ·
    refine ⟨124248134407302592215080827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165664179209736789620107769 124248134407302592215080827)
    ·
      refine ⟨186372201610953888322621241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124248134407302592215080827 186372201610953888322621241)
      ·
        refine ⟨139779151208215416241965931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186372201610953888322621241 139779151208215416241965931)
        ·
          refine ⟨209668726812323124362948897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139779151208215416241965931 209668726812323124362948897)
          ·
            refine ⟨157251545109242343272211673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 209668726812323124362948897 157251545109242343272211673)
            ·
              refine ⟨117938658831931757454158755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 157251545109242343272211673 117938658831931757454158755)
              ·
                refine ⟨176907988247897636181238133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117938658831931757454158755 176907988247897636181238133)
                ·
                  refine ⟨16585123898240403391991075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 176907988247897636181238133 16585123898240403391991075)
                  ·
                    refine ⟨24877685847360605087986613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16585123898240403391991075 24877685847360605087986613)
                    ·
                      refine ⟨2332283048190056726998745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24877685847360605087986613 2332283048190056726998745)
                      ·
                        rfl

theorem cell23_4542105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 5, 1, 5].length) (baseStart_4542105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4542105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4542105 prefixEnd_4542105 := by exact prefixLift 4542105
  have htrace : WordTrace (prefixWord ++ tailWord_4542105) baseStart_4542105 baseEnd_4542105 := by
    simpa [prefixWord, tailWord_4542105, baseEnd_4542105] using wordTrace_append hprefix tailTrace_4542105
  have hstable : (prefixWord ++ tailWord_4542105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4542105).length < 2 ^ (prefixWord ++ tailWord_4542105).sum := by decide
  have hdescent : baseEnd_4542105 < baseStart_4542105 := by decide
  rcases family_descends (prefixWord ++ tailWord_4542105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4542112 : List Nat := [2, 1, 1, 4, 3, 1, 2, 2, 1, 6]
def baseStart_4542112 : Nat := 118140960795 + 4542112 * 2 ^ 59
def prefixEnd_4542112 : Nat := 4983230072969 + 3 ^ 40 * 4542112 * 2
def baseEnd_4542112 : Nat := 777428880851546066537071

theorem tailTrace_4542112 : CollatzResearch.WordTrace tailWord_4542112 prefixEnd_4542112 777428880851546066537071 := by
  unfold tailWord_4542112
  simp only [CollatzResearch.WordTrace]
  refine ⟨82832217260355714907806295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110442956347140953210408393 82832217260355714907806295)
  ·
    refine ⟨124248325890533572361709443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82832217260355714907806295 124248325890533572361709443)
    ·
      refine ⟨186372488835800358542564165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124248325890533572361709443 186372488835800358542564165)
      ·
        refine ⟨34944841656712567226730781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 186372488835800358542564165 34944841656712567226730781)
        ·
          refine ⟨13104315621267212710024043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34944841656712567226730781 13104315621267212710024043)
          ·
            refine ⟨19656473431900819065036065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13104315621267212710024043 19656473431900819065036065)
            ·
              refine ⟨14742355073925614298777049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19656473431900819065036065 14742355073925614298777049)
              ·
                refine ⟨11056766305444210724082787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14742355073925614298777049 11056766305444210724082787)
                ·
                  refine ⟨16585149458166316086124181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11056766305444210724082787 16585149458166316086124181)
                  ·
                    refine ⟨777428880851546066537071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16585149458166316086124181 777428880851546066537071)
                    ·
                      rfl

theorem cell23_4542112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 2, 1, 6].length) (baseStart_4542112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4542112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4542112 prefixEnd_4542112 := by exact prefixLift 4542112
  have htrace : WordTrace (prefixWord ++ tailWord_4542112) baseStart_4542112 baseEnd_4542112 := by
    simpa [prefixWord, tailWord_4542112, baseEnd_4542112] using wordTrace_append hprefix tailTrace_4542112
  have hstable : (prefixWord ++ tailWord_4542112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4542112).length < 2 ^ (prefixWord ++ tailWord_4542112).sum := by decide
  have hdescent : baseEnd_4542112 < baseStart_4542112 := by decide
  rcases family_descends (prefixWord ++ tailWord_4542112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4542113 : List Nat := [1, 2, 3, 3, 2, 2, 2, 3, 1, 1, 3]
def baseStart_4542113 : Nat := 118140960795 + 4542113 * 2 ^ 59
def prefixEnd_4542113 : Nat := 4983230072969 + 3 ^ 40 * 4542113 * 2
def baseEnd_4542113 : Nat := 2332287156035292695698709

theorem tailTrace_4542113 : CollatzResearch.WordTrace tailWord_4542113 prefixEnd_4542113 2332287156035292695698709 := by
  unfold tailWord_4542113
  simp only [CollatzResearch.WordTrace]
  refine ⟨165664470993707806986398993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110442980662471871324265995 165664470993707806986398993)
  ·
    refine ⟨124248353245280855239799245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165664470993707806986398993 124248353245280855239799245)
    ·
      refine ⟨46593132466980320714924717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124248353245280855239799245 46593132466980320714924717)
      ·
        refine ⟨17472424675117620268096769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46593132466980320714924717 17472424675117620268096769)
        ·
          refine ⟨13104318506338215201072577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17472424675117620268096769 13104318506338215201072577)
          ·
            refine ⟨9828238879753661400804433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13104318506338215201072577 9828238879753661400804433)
            ·
              refine ⟨7371179159815246050603325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9828238879753661400804433 7371179159815246050603325)
              ·
                refine ⟨2764192184930717268976247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7371179159815246050603325 2764192184930717268976247)
                ·
                  refine ⟨4146288277396075903464371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2764192184930717268976247 4146288277396075903464371)
                  ·
                    refine ⟨6219432416094113855196557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4146288277396075903464371 6219432416094113855196557)
                    ·
                      refine ⟨2332287156035292695698709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6219432416094113855196557 2332287156035292695698709)
                      ·
                        rfl

theorem cell23_4542113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 3, 1, 1, 3].length) (baseStart_4542113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4542113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4542113 prefixEnd_4542113 := by exact prefixLift 4542113
  have htrace : WordTrace (prefixWord ++ tailWord_4542113) baseStart_4542113 baseEnd_4542113 := by
    simpa [prefixWord, tailWord_4542113, baseEnd_4542113] using wordTrace_append hprefix tailTrace_4542113
  have hstable : (prefixWord ++ tailWord_4542113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4542113).length < 2 ^ (prefixWord ++ tailWord_4542113).sum := by decide
  have hdescent : baseEnd_4542113 < baseStart_4542113 := by decide
  rcases family_descends (prefixWord ++ tailWord_4542113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4542116 : List Nat := [2, 3, 1, 2, 2, 4, 2, 1, 1, 5]
def baseStart_4542116 : Nat := 118140960795 + 4542116 * 2 ^ 59
def prefixEnd_4542116 : Nat := 4983230072969 + 3 ^ 40 * 4542116 * 2
def baseEnd_4542116 : Nat := 777429565492418727987065

theorem tailTrace_4542116 : CollatzResearch.WordTrace tailWord_4542116 prefixEnd_4542116 777429565492418727987065 := by
  unfold tailWord_4542116
  simp only [CollatzResearch.WordTrace]
  refine ⟨82832290206348469249379101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110443053608464625665838801 82832290206348469249379101)
  ·
    refine ⟨31062108827380675968517163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82832290206348469249379101 31062108827380675968517163)
    ·
      refine ⟨46593163241071013952775745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31062108827380675968517163 46593163241071013952775745)
      ·
        refine ⟨34944872430803260464581809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46593163241071013952775745 34944872430803260464581809)
        ·
          refine ⟨26208654323102445348436357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34944872430803260464581809 26208654323102445348436357)
          ·
            refine ⟨4914122685581708502831817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26208654323102445348436357 4914122685581708502831817)
            ·
              refine ⟨3685592014186281377123863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4914122685581708502831817 3685592014186281377123863)
              ·
                refine ⟨5528388021279422065685795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3685592014186281377123863 5528388021279422065685795)
                ·
                  refine ⟨8292582031919133098528693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5528388021279422065685795 8292582031919133098528693)
                  ·
                    refine ⟨777429565492418727987065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8292582031919133098528693 777429565492418727987065)
                    ·
                      rfl

theorem cell23_4542116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 2, 1, 1, 5].length) (baseStart_4542116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4542116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4542116 prefixEnd_4542116 := by exact prefixLift 4542116
  have htrace : WordTrace (prefixWord ++ tailWord_4542116) baseStart_4542116 baseEnd_4542116 := by
    simpa [prefixWord, tailWord_4542116, baseEnd_4542116] using wordTrace_append hprefix tailTrace_4542116
  have hstable : (prefixWord ++ tailWord_4542116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4542116).length < 2 ^ (prefixWord ++ tailWord_4542116).sum := by decide
  have hdescent : baseEnd_4542116 < baseStart_4542116 := by decide
  rcases family_descends (prefixWord ++ tailWord_4542116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4542120 : List Nat := [2, 1, 7, 1, 2, 1, 1, 2, 6]
def baseStart_4542120 : Nat := 118140960795 + 4542120 * 2 ^ 59
def prefixEnd_4542120 : Nat := 4983230072969 + 3 ^ 40 * 4542120 * 2
def baseEnd_4542120 : Nat := 259143416711097129812353

theorem tailTrace_4542120 : CollatzResearch.WordTrace tailWord_4542120 prefixEnd_4542120 259143416711097129812353 := by
  unfold tailWord_4542120
  simp only [CollatzResearch.WordTrace]
  refine ⟨82832363152341223590951907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110443150869788298121269209 82832363152341223590951907)
  ·
    refine ⟨124248544728511835386427861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82832363152341223590951907 124248544728511835386427861)
    ·
      refine ⟨2912075267074496141869403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 124248544728511835386427861 2912075267074496141869403)
      ·
        refine ⟨4368112900611744212804105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2912075267074496141869403 4368112900611744212804105)
        ·
          refine ⟨3276084675458808159603079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4368112900611744212804105 3276084675458808159603079)
          ·
            refine ⟨4914127013188212239404619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3276084675458808159603079 4914127013188212239404619)
            ·
              refine ⟨7371190519782318359106929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4914127013188212239404619 7371190519782318359106929)
              ·
                refine ⟨5528392889836738769330197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7371190519782318359106929 5528392889836738769330197)
                ·
                  refine ⟨259143416711097129812353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5528392889836738769330197 259143416711097129812353)
                  ·
                    rfl

theorem cell23_4542120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 2, 6].length) (baseStart_4542120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4542120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4542120 prefixEnd_4542120 := by exact prefixLift 4542120
  have htrace : WordTrace (prefixWord ++ tailWord_4542120) baseStart_4542120 baseEnd_4542120 := by
    simpa [prefixWord, tailWord_4542120, baseEnd_4542120] using wordTrace_append hprefix tailTrace_4542120
  have hstable : (prefixWord ++ tailWord_4542120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4542120).length < 2 ^ (prefixWord ++ tailWord_4542120).sum := by decide
  have hdescent : baseEnd_4542120 < baseStart_4542120 := by decide
  rcases family_descends (prefixWord ++ tailWord_4542120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4542155 : List Nat := [1, 1, 1, 1, 3, 2, 1, 4, 2, 7]
def baseStart_4542155 : Nat := 118140960795 + 4542155 * 2 ^ 59
def prefixEnd_4542155 : Nat := 4983230072969 + 3 ^ 40 * 4542155 * 2
def baseEnd_4542155 : Nat := 777436240740927177124505

theorem tailTrace_4542155 : CollatzResearch.WordTrace tailWord_4542155 prefixEnd_4542155 777436240740927177124505 := by
  unfold tailWord_4542155
  simp only [CollatzResearch.WordTrace]
  refine ⟨165666002859555648159427919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110444001906370432106285279 165666002859555648159427919)
  ·
    refine ⟨248499004289333472239141879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165666002859555648159427919 248499004289333472239141879)
    ·
      refine ⟨372748506434000208358712819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248499004289333472239141879 372748506434000208358712819)
      ·
        refine ⟨559122759651000312538069229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 372748506434000208358712819 559122759651000312538069229)
        ·
          refine ⟨209671034869125117201775961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 559122759651000312538069229 209671034869125117201775961)
          ·
            refine ⟨157253276151843837901331971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 209671034869125117201775961 157253276151843837901331971)
            ·
              refine ⟨235879914227765756851997957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157253276151843837901331971 235879914227765756851997957)
              ·
                refine ⟨44227483917706079409749617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 235879914227765756851997957 44227483917706079409749617)
                ·
                  refine ⟨33170612938279559557312213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44227483917706079409749617 33170612938279559557312213)
                  ·
                    refine ⟨777436240740927177124505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33170612938279559557312213 777436240740927177124505)
                    ·
                      rfl

theorem cell23_4542155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 2, 7].length) (baseStart_4542155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4542155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4542155 prefixEnd_4542155 := by exact prefixLift 4542155
  have htrace : WordTrace (prefixWord ++ tailWord_4542155) baseStart_4542155 baseEnd_4542155 := by
    simpa [prefixWord, tailWord_4542155, baseEnd_4542155] using wordTrace_append hprefix tailTrace_4542155
  have hstable : (prefixWord ++ tailWord_4542155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4542155).length < 2 ^ (prefixWord ++ tailWord_4542155).sum := by decide
  have hdescent : baseEnd_4542155 < baseStart_4542155 := by decide
  rcases family_descends (prefixWord ++ tailWord_4542155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4542169 : List Nat := [1, 2, 1, 2, 3, 3, 1, 2, 4, 1, 3]
def baseStart_4542169 : Nat := 118140960795 + 4542169 * 2 ^ 59
def prefixEnd_4542169 : Nat := 4983230072969 + 3 ^ 40 * 4542169 * 2
def baseEnd_4542169 : Nat := 2332315910951944476598451

theorem tailTrace_4542169 : CollatzResearch.WordTrace tailWord_4542169 prefixEnd_4542169 2332315910951944476598451 := by
  unfold tailWord_4542169
  simp only [CollatzResearch.WordTrace]
  refine ⟨165666513481504928550437561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110444342321003285700291707 165666513481504928550437561)
  ·
    refine ⟨124249885111128696412828171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165666513481504928550437561 124249885111128696412828171)
    ·
      refine ⟨186374827666693044619242257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124249885111128696412828171 186374827666693044619242257)
      ·
        refine ⟨139781120750019783464431693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186374827666693044619242257 139781120750019783464431693)
        ·
          refine ⟨52417920281257418799161885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 139781120750019783464431693 52417920281257418799161885)
          ·
            refine ⟨19656720105471532049685707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52417920281257418799161885 19656720105471532049685707)
            ·
              refine ⟨29485080158207298074528561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19656720105471532049685707 29485080158207298074528561)
              ·
                refine ⟨22113810118655473555896421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29485080158207298074528561 22113810118655473555896421)
                ·
                  refine ⟨4146339397247901291730579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22113810118655473555896421 4146339397247901291730579)
                  ·
                    refine ⟨6219509095871851937595869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4146339397247901291730579 6219509095871851937595869)
                    ·
                      refine ⟨2332315910951944476598451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6219509095871851937595869 2332315910951944476598451)
                      ·
                        rfl

theorem cell23_4542169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 2, 4, 1, 3].length) (baseStart_4542169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4542169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4542169 prefixEnd_4542169 := by exact prefixLift 4542169
  have htrace : WordTrace (prefixWord ++ tailWord_4542169) baseStart_4542169 baseEnd_4542169 := by
    simpa [prefixWord, tailWord_4542169, baseEnd_4542169] using wordTrace_append hprefix tailTrace_4542169
  have hstable : (prefixWord ++ tailWord_4542169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4542169).length < 2 ^ (prefixWord ++ tailWord_4542169).sum := by decide
  have hdescent : baseEnd_4542169 < baseStart_4542169 := by decide
  rcases family_descends (prefixWord ++ tailWord_4542169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4542170 : List Nat := [3, 1, 1, 2, 2, 5, 1, 3, 1, 2, 2]
def baseStart_4542170 : Nat := 118140960795 + 4542170 * 2 ^ 59
def prefixEnd_4542170 : Nat := 4983230072969 + 3 ^ 40 * 4542170 * 2
def baseEnd_4542170 : Nat := 2332316424432598972685947

theorem tailTrace_4542170 : CollatzResearch.WordTrace tailWord_4542170 prefixEnd_4542170 2332316424432598972685947 := by
  unfold tailWord_4542170
  simp only [CollatzResearch.WordTrace]
  refine ⟨41416637488625326430305991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110444366636334203814149309 41416637488625326430305991)
  ·
    refine ⟨62124956232937989645458987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41416637488625326430305991 62124956232937989645458987)
    ·
      refine ⟨93187434349406984468188481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62124956232937989645458987 93187434349406984468188481)
      ·
        refine ⟨69890575762055238351141361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93187434349406984468188481 69890575762055238351141361)
        ·
          refine ⟨52417931821541428763356021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69890575762055238351141361 52417931821541428763356021)
          ·
            refine ⟨4914181108269508946564627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52417931821541428763356021 4914181108269508946564627)
            ·
              refine ⟨7371271662404263419846941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4914181108269508946564627 7371271662404263419846941)
              ·
                refine ⟨2764226873401598782442603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7371271662404263419846941 2764226873401598782442603)
                ·
                  refine ⟨4146340310102398173663905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2764226873401598782442603 4146340310102398173663905)
                  ·
                    refine ⟨3109755232576798630247929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4146340310102398173663905 3109755232576798630247929)
                    ·
                      refine ⟨2332316424432598972685947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3109755232576798630247929 2332316424432598972685947)
                      ·
                        rfl

theorem cell23_4542170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 3, 1, 2, 2].length) (baseStart_4542170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4542170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4542170 prefixEnd_4542170 := by exact prefixLift 4542170
  have htrace : WordTrace (prefixWord ++ tailWord_4542170) baseStart_4542170 baseEnd_4542170 := by
    simpa [prefixWord, tailWord_4542170, baseEnd_4542170] using wordTrace_append hprefix tailTrace_4542170
  have hstable : (prefixWord ++ tailWord_4542170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4542170).length < 2 ^ (prefixWord ++ tailWord_4542170).sum := by decide
  have hdescent : baseEnd_4542170 < baseStart_4542170 := by decide
  rcases family_descends (prefixWord ++ tailWord_4542170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4542238 : List Nat := [4, 3, 2, 2, 2, 1, 2, 2, 1, 2, 2]
def baseStart_4542238 : Nat := 118140960795 + 4542238 * 2 ^ 59
def prefixEnd_4542238 : Nat := 4983230072969 + 3 ^ 40 * 4542238 * 2
def baseEnd_4542238 : Nat := 2332351341117104706635635

theorem tailTrace_4542238 : CollatzResearch.WordTrace tailWord_4542238 prefixEnd_4542238 2332351341117104706635635 := by
  unfold tailWord_4542238
  simp only [CollatzResearch.WordTrace]
  refine ⟨20708628764781869166837421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110446020078836635556466245 20708628764781869166837421)
  ·
    refine ⟨7765735786793200937564033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20708628764781869166837421 7765735786793200937564033)
    ·
      refine ⟨5824301840094900703173025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7765735786793200937564033 5824301840094900703173025)
      ·
        refine ⟨4368226380071175527379769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5824301840094900703173025 4368226380071175527379769)
        ·
          refine ⟨3276169785053381645534827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4368226380071175527379769 3276169785053381645534827)
          ·
            refine ⟨4914254677580072468302241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3276169785053381645534827 4914254677580072468302241)
            ·
              refine ⟨3685691008185054351226681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4914254677580072468302241 3685691008185054351226681)
              ·
                refine ⟨2764268256138790763420011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3685691008185054351226681 2764268256138790763420011)
                ·
                  refine ⟨4146402384208186145130017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2764268256138790763420011 4146402384208186145130017)
                  ·
                    refine ⟨3109801788156139608847513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4146402384208186145130017 3109801788156139608847513)
                    ·
                      refine ⟨2332351341117104706635635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3109801788156139608847513 2332351341117104706635635)
                      ·
                        rfl

theorem cell23_4542238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_4542238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4542238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4542238 prefixEnd_4542238 := by exact prefixLift 4542238
  have htrace : WordTrace (prefixWord ++ tailWord_4542238) baseStart_4542238 baseEnd_4542238 := by
    simpa [prefixWord, tailWord_4542238, baseEnd_4542238] using wordTrace_append hprefix tailTrace_4542238
  have hstable : (prefixWord ++ tailWord_4542238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4542238).length < 2 ^ (prefixWord ++ tailWord_4542238).sum := by decide
  have hdescent : baseEnd_4542238 < baseStart_4542238 := by decide
  rcases family_descends (prefixWord ++ tailWord_4542238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4542260 : List Nat := [2, 5, 1, 1, 2, 1, 2, 3, 2, 2, 2]
def baseStart_4542260 : Nat := 118140960795 + 4542260 * 2 ^ 59
def prefixEnd_4542260 : Nat := 4983230072969 + 3 ^ 40 * 4542260 * 2
def baseEnd_4542260 : Nat := 2332362637691503620560533

theorem tailTrace_4542260 : CollatzResearch.WordTrace tailWord_4542260 prefixEnd_4542260 2332362637691503620560533 := by
  unfold tailWord_4542260
  simp only [CollatzResearch.WordTrace]
  refine ⟨82834916262087625546000117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110446555016116834061333489 82834916262087625546000117)
  ·
    refine ⟨7765773399570714894937511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 82834916262087625546000117 7765773399570714894937511)
    ·
      refine ⟨11648660099356072342406267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7765773399570714894937511 11648660099356072342406267)
      ·
        refine ⟨17472990149034108513609401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11648660099356072342406267 17472990149034108513609401)
        ·
          refine ⟨13104742611775581385207051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17472990149034108513609401 13104742611775581385207051)
          ·
            refine ⟨19657113917663372077810577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13104742611775581385207051 19657113917663372077810577)
            ·
              refine ⟨14742835438247529058357933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19657113917663372077810577 14742835438247529058357933)
              ·
                refine ⟨5528563289342823396884225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14742835438247529058357933 5528563289342823396884225)
                ·
                  refine ⟨4146422467007117547663169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5528563289342823396884225 4146422467007117547663169)
                  ·
                    refine ⟨3109816850255338160747377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4146422467007117547663169 3109816850255338160747377)
                    ·
                      refine ⟨2332362637691503620560533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3109816850255338160747377 2332362637691503620560533)
                      ·
                        rfl

theorem cell23_4542260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 3, 2, 2, 2].length) (baseStart_4542260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4542260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4542260 prefixEnd_4542260 := by exact prefixLift 4542260
  have htrace : WordTrace (prefixWord ++ tailWord_4542260) baseStart_4542260 baseEnd_4542260 := by
    simpa [prefixWord, tailWord_4542260, baseEnd_4542260] using wordTrace_append hprefix tailTrace_4542260
  have hstable : (prefixWord ++ tailWord_4542260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4542260).length < 2 ^ (prefixWord ++ tailWord_4542260).sum := by decide
  have hdescent : baseEnd_4542260 < baseStart_4542260 := by decide
  rcases family_descends (prefixWord ++ tailWord_4542260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4542279 : List Nat := [1, 1, 4, 1, 2, 1, 5, 1, 2, 5]
def baseStart_4542279 : Nat := 118140960795 + 4542279 * 2 ^ 59
def prefixEnd_4542279 : Nat := 4983230072969 + 3 ^ 40 * 4542279 * 2
def baseEnd_4542279 : Nat := 777457464607979682074315

theorem tailTrace_4542279 : CollatzResearch.WordTrace tailWord_4542279 prefixEnd_4542279 777457464607979682074315 := by
  unfold tailWord_4542279
  simp only [CollatzResearch.WordTrace]
  refine ⟨165670525511106417336941891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110447017007404278224627927 165670525511106417336941891)
  ·
    refine ⟨248505788266659626005412837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165670525511106417336941891 248505788266659626005412837)
    ·
      refine ⟨46594835299998679876014907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 248505788266659626005412837 46594835299998679876014907)
      ·
        refine ⟨69892252949998019814022361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46594835299998679876014907 69892252949998019814022361)
        ·
          refine ⟨52419189712498514860516771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69892252949998019814022361 52419189712498514860516771)
          ·
            refine ⟨78628784568747772290775157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52419189712498514860516771 78628784568747772290775157)
            ·
              refine ⟨7371448553320103652260171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 78628784568747772290775157 7371448553320103652260171)
              ·
                refine ⟨11057172829980155478390257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7371448553320103652260171 11057172829980155478390257)
                ·
                  refine ⟨8292879622485116608792693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11057172829980155478390257 8292879622485116608792693)
                  ·
                    refine ⟨777457464607979682074315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8292879622485116608792693 777457464607979682074315)
                    ·
                      rfl

theorem cell23_4542279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 1, 2, 5].length) (baseStart_4542279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4542279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4542279 prefixEnd_4542279 := by exact prefixLift 4542279
  have htrace : WordTrace (prefixWord ++ tailWord_4542279) baseStart_4542279 baseEnd_4542279 := by
    simpa [prefixWord, tailWord_4542279, baseEnd_4542279] using wordTrace_append hprefix tailTrace_4542279
  have hstable : (prefixWord ++ tailWord_4542279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4542279).length < 2 ^ (prefixWord ++ tailWord_4542279).sum := by decide
  have hdescent : baseEnd_4542279 < baseStart_4542279 := by decide
  rcases family_descends (prefixWord ++ tailWord_4542279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4542316 : List Nat := [2, 2, 1, 1, 4, 2, 2, 1, 2, 4, 2]
def baseStart_4542316 : Nat := 118140960795 + 4542316 * 2 ^ 59
def prefixEnd_4542316 : Nat := 4983230072969 + 3 ^ 40 * 4542316 * 2
def baseEnd_4542316 : Nat := 2332391392608155401460275

theorem tailTrace_4542316 : CollatzResearch.WordTrace tailWord_4542316 prefixEnd_4542316 2332391392608155401460275 := by
  unfold tailWord_4542316
  simp only [CollatzResearch.WordTrace]
  refine ⟨82835937505986186328019401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110447916674648248437359201 82835937505986186328019401)
  ·
    refine ⟨62126953129489639746014551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82835937505986186328019401 62126953129489639746014551)
    ·
      refine ⟨93190429694234459619021827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62126953129489639746014551 93190429694234459619021827)
      ·
        refine ⟨139785644541351689428532741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93190429694234459619021827 139785644541351689428532741)
        ·
          refine ⟨26209808351503441767849889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 139785644541351689428532741 26209808351503441767849889)
          ·
            refine ⟨19657356263627581325887417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26209808351503441767849889 19657356263627581325887417)
            ·
              refine ⟨14743017197720685994415563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19657356263627581325887417 14743017197720685994415563)
              ·
                refine ⟨22114525796581028991623345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14743017197720685994415563 22114525796581028991623345)
                ·
                  refine ⟨16585894347435771743717509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22114525796581028991623345 16585894347435771743717509)
                  ·
                    refine ⟨3109855190144207201947033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16585894347435771743717509 3109855190144207201947033)
                    ·
                      refine ⟨2332391392608155401460275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3109855190144207201947033 2332391392608155401460275)
                      ·
                        rfl

theorem cell23_4542316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 4, 2].length) (baseStart_4542316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4542316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4542316 prefixEnd_4542316 := by exact prefixLift 4542316
  have htrace : WordTrace (prefixWord ++ tailWord_4542316) baseStart_4542316 baseEnd_4542316 := by
    simpa [prefixWord, tailWord_4542316, baseEnd_4542316] using wordTrace_append hprefix tailTrace_4542316
  have hstable : (prefixWord ++ tailWord_4542316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4542316).length < 2 ^ (prefixWord ++ tailWord_4542316).sum := by decide
  have hdescent : baseEnd_4542316 < baseStart_4542316 := by decide
  rcases family_descends (prefixWord ++ tailWord_4542316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4542332 : List Nat := [2, 2, 2, 1, 1, 1, 1, 1, 2, 1, 9]
def baseStart_4542332 : Nat := 118140960795 + 4542332 * 2 ^ 59
def prefixEnd_4542332 : Nat := 4983230072969 + 3 ^ 40 * 4542332 * 2
def baseEnd_4542332 : Nat := 2332399608298627338860201

theorem tailTrace_4542332 : CollatzResearch.WordTrace tailWord_4542332 prefixEnd_4542332 2332399608298627338860201 := by
  unfold tailWord_4542332
  simp only [CollatzResearch.WordTrace]
  refine ⟨82836229289957203694310625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110448305719942938259080833 82836229289957203694310625)
  ·
    refine ⟨62127171967467902770732969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82836229289957203694310625 62127171967467902770732969)
    ·
      refine ⟨46595378975600927078049727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62127171967467902770732969 46595378975600927078049727)
      ·
        refine ⟨69893068463401390617074591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46595378975600927078049727 69893068463401390617074591)
        ·
          refine ⟨104839602695102085925611887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69893068463401390617074591 104839602695102085925611887)
          ·
            refine ⟨157259404042653128888417831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104839602695102085925611887 157259404042653128888417831)
            ·
              refine ⟨235889106063979693332626747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157259404042653128888417831 235889106063979693332626747)
              ·
                refine ⟨353833659095969539998940121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 235889106063979693332626747 353833659095969539998940121)
                ·
                  refine ⟨265375244321977154999205091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 353833659095969539998940121 265375244321977154999205091)
                  ·
                    refine ⟨398062866482965732498807637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 265375244321977154999205091 398062866482965732498807637)
                    ·
                      refine ⟨2332399608298627338860201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 398062866482965732498807637 2332399608298627338860201)
                      ·
                        rfl

theorem cell23_4542332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 2, 1, 9].length) (baseStart_4542332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4542332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4542332 prefixEnd_4542332 := by exact prefixLift 4542332
  have htrace : WordTrace (prefixWord ++ tailWord_4542332) baseStart_4542332 baseEnd_4542332 := by
    simpa [prefixWord, tailWord_4542332, baseEnd_4542332] using wordTrace_append hprefix tailTrace_4542332
  have hstable : (prefixWord ++ tailWord_4542332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4542332).length < 2 ^ (prefixWord ++ tailWord_4542332).sum := by decide
  have hdescent : baseEnd_4542332 < baseStart_4542332 := by decide
  rcases family_descends (prefixWord ++ tailWord_4542332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4542360 : List Nat := [2, 1, 2, 6, 1, 2, 1, 1, 3, 4]
def baseStart_4542360 : Nat := 118140960795 + 4542360 * 2 ^ 59
def prefixEnd_4542360 : Nat := 4983230072969 + 3 ^ 40 * 4542360 * 2
def baseEnd_4542360 : Nat := 777471328585651076436691

theorem tailTrace_4542360 : CollatzResearch.WordTrace tailWord_4542360 prefixEnd_4542360 777471328585651076436691 := by
  unfold tailWord_4542360
  simp only [CollatzResearch.WordTrace]
  refine ⟨82836739911906484085320267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110448986549208645447093689 82836739911906484085320267)
  ·
    refine ⟨124255109867859726127980401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82836739911906484085320267 124255109867859726127980401)
    ·
      refine ⟨93191332400894794595985301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124255109867859726127980401 93191332400894794595985301)
      ·
        refine ⟨4368343706291943496686811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 93191332400894794595985301 4368343706291943496686811)
        ·
          refine ⟨6552515559437915245030217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4368343706291943496686811 6552515559437915245030217)
          ·
            refine ⟨4914386669578436433772663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6552515559437915245030217 4914386669578436433772663)
            ·
              refine ⟨7371580004367654650658995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4914386669578436433772663 7371580004367654650658995)
              ·
                refine ⟨11057370006551481975988493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7371580004367654650658995 11057370006551481975988493)
                ·
                  refine ⟨4146513752456805740995685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11057370006551481975988493 4146513752456805740995685)
                  ·
                    refine ⟨777471328585651076436691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4146513752456805740995685 777471328585651076436691)
                    ·
                      rfl

theorem cell23_4542360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 1, 3, 4].length) (baseStart_4542360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4542360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4542360 prefixEnd_4542360 := by exact prefixLift 4542360
  have htrace : WordTrace (prefixWord ++ tailWord_4542360) baseStart_4542360 baseEnd_4542360 := by
    simpa [prefixWord, tailWord_4542360, baseEnd_4542360] using wordTrace_append hprefix tailTrace_4542360
  have hstable : (prefixWord ++ tailWord_4542360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4542360).length < 2 ^ (prefixWord ++ tailWord_4542360).sum := by decide
  have hdescent : baseEnd_4542360 < baseStart_4542360 := by decide
  rcases family_descends (prefixWord ++ tailWord_4542360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4542393 : List Nat := [1, 2, 1, 4, 2, 1, 4, 1, 2, 3, 2]
def baseStart_4542393 : Nat := 118140960795 + 4542393 * 2 ^ 59
def prefixEnd_4542393 : Nat := 4983230072969 + 3 ^ 40 * 4542393 * 2
def baseEnd_4542393 : Nat := 2332430930618551600197421

theorem tailTrace_4542393 : CollatzResearch.WordTrace tailWord_4542393 prefixEnd_4542393 2332430930618551600197421 := by
  unfold tailWord_4542393
  simp only [CollatzResearch.WordTrace]
  refine ⟨165674683432693414806591833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110449788955128943204394555 165674683432693414806591833)
  ·
    refine ⟨124256012574520061104943875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165674683432693414806591833 124256012574520061104943875)
    ·
      refine ⟨186384018861780091657415813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124256012574520061104943875 186384018861780091657415813)
      ·
        refine ⟨34947003536583767185765465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 186384018861780091657415813 34947003536583767185765465)
        ·
          refine ⟨26210252652437825389324099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34947003536583767185765465 26210252652437825389324099)
          ·
            refine ⟨39315378978656738083986149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26210252652437825389324099 39315378978656738083986149)
            ·
              refine ⟨7371633558498138390747403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39315378978656738083986149 7371633558498138390747403)
              ·
                refine ⟨11057450337747207586121105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7371633558498138390747403 11057450337747207586121105)
                ·
                  refine ⟨8293087753310405689590829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11057450337747207586121105 8293087753310405689590829)
                  ·
                    refine ⟨3109907907491402133596561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8293087753310405689590829 3109907907491402133596561)
                    ·
                      refine ⟨2332430930618551600197421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3109907907491402133596561 2332430930618551600197421)
                      ·
                        rfl

theorem cell23_4542393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 1, 2, 3, 2].length) (baseStart_4542393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4542393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4542393 prefixEnd_4542393 := by exact prefixLift 4542393
  have htrace : WordTrace (prefixWord ++ tailWord_4542393) baseStart_4542393 baseEnd_4542393 := by
    simpa [prefixWord, tailWord_4542393, baseEnd_4542393] using wordTrace_append hprefix tailTrace_4542393
  have hstable : (prefixWord ++ tailWord_4542393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4542393).length < 2 ^ (prefixWord ++ tailWord_4542393).sum := by decide
  have hdescent : baseEnd_4542393 < baseStart_4542393 := by decide
  rcases family_descends (prefixWord ++ tailWord_4542393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4542399 : List Nat := [1, 1, 2, 2, 2, 1, 5, 2, 1, 6]
def baseStart_4542399 : Nat := 118140960795 + 4542399 * 2 ^ 59
def prefixEnd_4542399 : Nat := 4983230072969 + 3 ^ 40 * 4542399 * 2
def baseEnd_4542399 : Nat := 777478003834159525574131

theorem tailTrace_4542399 : CollatzResearch.WordTrace tailWord_4542399 prefixEnd_4542399 777478003834159525574131 := by
  unfold tailWord_4542399
  simp only [CollatzResearch.WordTrace]
  refine ⟨165674902270671677831310251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110449934847114451887540167 165674902270671677831310251)
  ·
    refine ⟨248512353406007516746965377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165674902270671677831310251 248512353406007516746965377)
    ·
      refine ⟨186384265054505637560224033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 248512353406007516746965377 186384265054505637560224033)
      ·
        refine ⟨139788198790879228170168025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186384265054505637560224033 139788198790879228170168025)
        ·
          refine ⟨104841149093159421127626019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139788198790879228170168025 104841149093159421127626019)
          ·
            refine ⟨157261723639739131691439029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104841149093159421127626019 157261723639739131691439029)
            ·
              refine ⟨14743286591225543596072409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 157261723639739131691439029 14743286591225543596072409)
              ·
                refine ⟨11057464943419157697054307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14743286591225543596072409 11057464943419157697054307)
                ·
                  refine ⟨16586197415128736545581461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11057464943419157697054307 16586197415128736545581461)
                  ·
                    refine ⟨777478003834159525574131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16586197415128736545581461 777478003834159525574131)
                    ·
                      rfl

theorem cell23_4542399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 2, 1, 6].length) (baseStart_4542399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4542399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4542399 prefixEnd_4542399 := by exact prefixLift 4542399
  have htrace : WordTrace (prefixWord ++ tailWord_4542399) baseStart_4542399 baseEnd_4542399 := by
    simpa [prefixWord, tailWord_4542399, baseEnd_4542399] using wordTrace_append hprefix tailTrace_4542399
  have hstable : (prefixWord ++ tailWord_4542399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4542399).length < 2 ^ (prefixWord ++ tailWord_4542399).sum := by decide
  have hdescent : baseEnd_4542399 < baseStart_4542399 := by decide
  rcases family_descends (prefixWord ++ tailWord_4542399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4542416 : List Nat := [2, 1, 1, 1, 1, 2, 5, 4, 2, 4]
def baseStart_4542416 : Nat := 118140960795 + 4542416 * 2 ^ 59
def prefixEnd_4542416 : Nat := 4983230072969 + 3 ^ 40 * 4542416 * 2
def baseEnd_4542416 : Nat := 777480913557868336736605

theorem tailTrace_4542416 : CollatzResearch.WordTrace tailWord_4542416 prefixEnd_4542416 777480913557868336736605 := by
  unfold tailWord_4542416
  simp only [CollatzResearch.WordTrace]
  refine ⟨82837761155805044867339551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110450348207740059823119401 82837761155805044867339551)
  ·
    refine ⟨124256641733707567301009327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82837761155805044867339551 124256641733707567301009327)
    ·
      refine ⟨186384962600561350951513991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124256641733707567301009327 186384962600561350951513991)
      ·
        refine ⟨279577443900842026427270987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186384962600561350951513991 279577443900842026427270987)
        ·
          refine ⟨419366165851263039640906481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 279577443900842026427270987 419366165851263039640906481)
          ·
            refine ⟨314524624388447279730679861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 419366165851263039640906481 314524624388447279730679861)
            ·
              refine ⟨29486683536416932474751237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 314524624388447279730679861 29486683536416932474751237)
              ·
                refine ⟨5528753163078174839015857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29486683536416932474751237 5528753163078174839015857)
                ·
                  refine ⟨4146564872308631129261893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5528753163078174839015857 4146564872308631129261893)
                  ·
                    refine ⟨777480913557868336736605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4146564872308631129261893 777480913557868336736605)
                    ·
                      rfl

theorem cell23_4542416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 4, 2, 4].length) (baseStart_4542416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4542416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4542416 prefixEnd_4542416 := by exact prefixLift 4542416
  have htrace : WordTrace (prefixWord ++ tailWord_4542416) baseStart_4542416 baseEnd_4542416 := by
    simpa [prefixWord, tailWord_4542416, baseEnd_4542416] using wordTrace_append hprefix tailTrace_4542416
  have hstable : (prefixWord ++ tailWord_4542416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4542416).length < 2 ^ (prefixWord ++ tailWord_4542416).sum := by decide
  have hdescent : baseEnd_4542416 < baseStart_4542416 := by decide
  rcases family_descends (prefixWord ++ tailWord_4542416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4542423 : List Nat := [1, 1, 3, 2, 1, 1, 4, 3, 3, 2, 2]
def baseStart_4542423 : Nat := 118140960795 + 4542423 * 2 ^ 59
def prefixEnd_4542423 : Nat := 4983230072969 + 3 ^ 40 * 4542423 * 2
def baseEnd_4542423 : Nat := 2332446335038186482822283

theorem tailTrace_4542423 : CollatzResearch.WordTrace tailWord_4542423 prefixEnd_4542423 2332446335038186482822283 := by
  unfold tailWord_4542423
  simp only [CollatzResearch.WordTrace]
  refine ⟨165675777622584729930183923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110450518415056486620122615 165675777622584729930183923)
  ·
    refine ⟨248513666433877094895275885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165675777622584729930183923 248513666433877094895275885)
    ·
      refine ⟨93192624912703910585728457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 248513666433877094895275885 93192624912703910585728457)
      ·
        refine ⟨69894468684527932939296343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93192624912703910585728457 69894468684527932939296343)
        ·
          refine ⟨104841703026791899408944515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69894468684527932939296343 104841703026791899408944515)
          ·
            refine ⟨157262554540187849113416773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104841703026791899408944515 157262554540187849113416773)
            ·
              refine ⟨29486728976285221708765645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 157262554540187849113416773 29486728976285221708765645)
              ·
                refine ⟨11057523366106958140787117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29486728976285221708765645 11057523366106958140787117)
                ·
                  refine ⟨4146571262290109302795169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11057523366106958140787117 4146571262290109302795169)
                  ·
                    refine ⟨3109928446717581977096377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4146571262290109302795169 3109928446717581977096377)
                    ·
                      refine ⟨2332446335038186482822283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3109928446717581977096377 2332446335038186482822283)
                      ·
                        rfl

theorem cell23_4542423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 3, 3, 2, 2].length) (baseStart_4542423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4542423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4542423 prefixEnd_4542423 := by exact prefixLift 4542423
  have htrace : WordTrace (prefixWord ++ tailWord_4542423) baseStart_4542423 baseEnd_4542423 := by
    simpa [prefixWord, tailWord_4542423, baseEnd_4542423] using wordTrace_append hprefix tailTrace_4542423
  have hstable : (prefixWord ++ tailWord_4542423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4542423).length < 2 ^ (prefixWord ++ tailWord_4542423).sum := by decide
  have hdescent : baseEnd_4542423 < baseStart_4542423 := by decide
  rcases family_descends (prefixWord ++ tailWord_4542423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4542436 : List Nat := [2, 3, 1, 1, 1, 1, 6, 1, 1, 2, 4]
def baseStart_4542436 : Nat := 118140960795 + 4542436 * 2 ^ 59
def prefixEnd_4542436 : Nat := 4983230072969 + 3 ^ 40 * 4542436 * 2
def baseEnd_4542436 : Nat := 2332453010286694931959723

theorem tailTrace_4542436 : CollatzResearch.WordTrace tailWord_4542436 prefixEnd_4542436 2332453010286694931959723 := by
  unfold tailWord_4542436
  simp only [CollatzResearch.WordTrace]
  refine ⟨82838125885768816575203581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110450834514358422100271441 82838125885768816575203581)
  ·
    refine ⟨31064297207163306215701343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82838125885768816575203581 31064297207163306215701343)
    ·
      refine ⟨46596445810744959323552015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31064297207163306215701343 46596445810744959323552015)
      ·
        refine ⟨69894668716117438985328023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46596445810744959323552015 69894668716117438985328023)
        ·
          refine ⟨104842003074176158477992035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69894668716117438985328023 104842003074176158477992035)
          ·
            refine ⟨157263004611264237716988053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104842003074176158477992035 157263004611264237716988053)
            ·
              refine ⟨7371703341153011142983815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 157263004611264237716988053 7371703341153011142983815)
              ·
                refine ⟨11057555011729516714475723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7371703341153011142983815 11057555011729516714475723)
                ·
                  refine ⟨16586332517594275071713585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11057555011729516714475723 16586332517594275071713585)
                  ·
                    refine ⟨12439749388195706303785189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16586332517594275071713585 12439749388195706303785189)
                    ·
                      refine ⟨2332453010286694931959723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12439749388195706303785189 2332453010286694931959723)
                      ·
                        rfl

theorem cell23_4542436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 1, 1, 2, 4].length) (baseStart_4542436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4542436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4542436 prefixEnd_4542436 := by exact prefixLift 4542436
  have htrace : WordTrace (prefixWord ++ tailWord_4542436) baseStart_4542436 baseEnd_4542436 := by
    simpa [prefixWord, tailWord_4542436, baseEnd_4542436] using wordTrace_append hprefix tailTrace_4542436
  have hstable : (prefixWord ++ tailWord_4542436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4542436).length < 2 ^ (prefixWord ++ tailWord_4542436).sum := by decide
  have hdescent : baseEnd_4542436 < baseStart_4542436 := by decide
  rcases family_descends (prefixWord ++ tailWord_4542436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4542456 : List Nat := [2, 1, 2, 1, 1, 3, 4, 2, 1, 3, 3]
def baseStart_4542456 : Nat := 118140960795 + 4542456 * 2 ^ 59
def prefixEnd_4542456 : Nat := 4983230072969 + 3 ^ 40 * 4542456 * 2
def baseEnd_4542456 : Nat := 2332463279899784853709631

theorem tailTrace_4542456 : CollatzResearch.WordTrace tailWord_4542456 prefixEnd_4542456 2332463279899784853709631 := by
  unfold tailWord_4542456
  simp only [CollatzResearch.WordTrace]
  refine ⟨82838490615732588283067611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110451320820976784377423481 82838490615732588283067611)
  ·
    refine ⟨124257735923598882424601417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82838490615732588283067611 124257735923598882424601417)
    ·
      refine ⟨93193301942699161818451063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124257735923598882424601417 93193301942699161818451063)
      ·
        refine ⟨139789952914048742727676595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93193301942699161818451063 139789952914048742727676595)
        ·
          refine ⟨209684929371073114091514893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139789952914048742727676595 209684929371073114091514893)
          ·
            refine ⟨78631848514152417784318085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 209684929371073114091514893 78631848514152417784318085)
            ·
              refine ⟨14743471596403578334559641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 78631848514152417784318085 14743471596403578334559641)
              ·
                refine ⟨11057603697302683750919731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14743471596403578334559641 11057603697302683750919731)
                ·
                  refine ⟨16586405545954025626379597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11057603697302683750919731 16586405545954025626379597)
                  ·
                    refine ⟨6219902079732759609892349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16586405545954025626379597 6219902079732759609892349)
                    ·
                      refine ⟨2332463279899784853709631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6219902079732759609892349 2332463279899784853709631)
                      ·
                        rfl

theorem cell23_4542456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 2, 1, 3, 3].length) (baseStart_4542456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4542456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4542456 prefixEnd_4542456 := by exact prefixLift 4542456
  have htrace : WordTrace (prefixWord ++ tailWord_4542456) baseStart_4542456 baseEnd_4542456 := by
    simpa [prefixWord, tailWord_4542456, baseEnd_4542456] using wordTrace_append hprefix tailTrace_4542456
  have hstable : (prefixWord ++ tailWord_4542456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4542456).length < 2 ^ (prefixWord ++ tailWord_4542456).sum := by decide
  have hdescent : baseEnd_4542456 < baseStart_4542456 := by decide
  rcases family_descends (prefixWord ++ tailWord_4542456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4542457 : List Nat := [1, 2, 1, 3, 1, 5, 2, 3, 1, 2, 2]
def baseStart_4542457 : Nat := 118140960795 + 4542457 * 2 ^ 59
def prefixEnd_4542457 : Nat := 4983230072969 + 3 ^ 40 * 4542457 * 2
def baseEnd_4542457 : Nat := 2332463793380439349797127

theorem tailTrace_4542457 : CollatzResearch.WordTrace tailWord_4542457 prefixEnd_4542457 2332463793380439349797127 := by
  unfold tailWord_4542457
  simp only [CollatzResearch.WordTrace]
  refine ⟨165677017704461553736921625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110451345136307702491281083 165677017704461553736921625)
  ·
    refine ⟨124257763278346165302691219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165677017704461553736921625 124257763278346165302691219)
    ·
      refine ⟨186386644917519247954036829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124257763278346165302691219 186386644917519247954036829)
      ·
        refine ⟨69894991844069717982763811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 186386644917519247954036829 69894991844069717982763811)
        ·
          refine ⟨104842487766104576974145717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69894991844069717982763811 104842487766104576974145717)
          ·
            refine ⟨9828983228072304091326161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 104842487766104576974145717 9828983228072304091326161)
            ·
              refine ⟨7371737421054228068494621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9828983228072304091326161 7371737421054228068494621)
              ·
                refine ⟨2764401532895335525685483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7371737421054228068494621 2764401532895335525685483)
                ·
                  refine ⟨4146602299343003288528225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2764401532895335525685483 4146602299343003288528225)
                  ·
                    refine ⟨3109951724507252466396169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4146602299343003288528225 3109951724507252466396169)
                    ·
                      refine ⟨2332463793380439349797127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3109951724507252466396169 2332463793380439349797127)
                      ·
                        rfl

theorem cell23_4542457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 3, 1, 2, 2].length) (baseStart_4542457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4542457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4542457 prefixEnd_4542457 := by exact prefixLift 4542457
  have htrace : WordTrace (prefixWord ++ tailWord_4542457) baseStart_4542457 baseEnd_4542457 := by
    simpa [prefixWord, tailWord_4542457, baseEnd_4542457] using wordTrace_append hprefix tailTrace_4542457
  have hstable : (prefixWord ++ tailWord_4542457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4542457).length < 2 ^ (prefixWord ++ tailWord_4542457).sum := by decide
  have hdescent : baseEnd_4542457 < baseStart_4542457 := by decide
  rcases family_descends (prefixWord ++ tailWord_4542457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4542477 : List Nat := [1, 7, 1, 2, 1, 1, 1, 2, 1, 1, 5]
def baseStart_4542477 : Nat := 118140960795 + 4542477 * 2 ^ 59
def prefixEnd_4542477 : Nat := 4983230072969 + 3 ^ 40 * 4542477 * 2
def baseEnd_4542477 : Nat := 2332474062993529271547035

theorem tailTrace_4542477 : CollatzResearch.WordTrace tailWord_4542477 prefixEnd_4542477 2332474062993529271547035 := by
  unfold tailWord_4542477
  simp only [CollatzResearch.WordTrace]
  refine ⟨165677747164389097152649685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110451831442926064768433123 165677747164389097152649685)
  ·
    refine ⟨3883072199165369464515227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 165677747164389097152649685 3883072199165369464515227)
    ·
      refine ⟨5824608298748054196772841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3883072199165369464515227 5824608298748054196772841)
      ·
        refine ⟨4368456224061040647579631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5824608298748054196772841 4368456224061040647579631)
        ·
          refine ⟨6552684336091560971369447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4368456224061040647579631 6552684336091560971369447)
          ·
            refine ⟨9829026504137341457054171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6552684336091560971369447 9829026504137341457054171)
            ·
              refine ⟨14743539756206012185581257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9829026504137341457054171 14743539756206012185581257)
              ·
                refine ⟨11057654817154509139185943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14743539756206012185581257 11057654817154509139185943)
                ·
                  refine ⟨16586482225731763708778915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11057654817154509139185943 16586482225731763708778915)
                  ·
                    refine ⟨24879723338597645563168373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16586482225731763708778915 24879723338597645563168373)
                    ·
                      refine ⟨2332474062993529271547035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24879723338597645563168373 2332474062993529271547035)
                      ·
                        rfl

theorem cell23_4542477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_4542477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4542477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4542477 prefixEnd_4542477 := by exact prefixLift 4542477
  have htrace : WordTrace (prefixWord ++ tailWord_4542477) baseStart_4542477 baseEnd_4542477 := by
    simpa [prefixWord, tailWord_4542477, baseEnd_4542477] using wordTrace_append hprefix tailTrace_4542477
  have hstable : (prefixWord ++ tailWord_4542477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4542477).length < 2 ^ (prefixWord ++ tailWord_4542477).sum := by decide
  have hdescent : baseEnd_4542477 < baseStart_4542477 := by decide
  rcases family_descends (prefixWord ++ tailWord_4542477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4542484 : List Nat := [2, 4, 3, 2, 1, 1, 3, 1, 2, 4]
def baseStart_4542484 : Nat := 118140960795 + 4542484 * 2 ^ 59
def prefixEnd_4542484 : Nat := 4983230072969 + 3 ^ 40 * 4542484 * 2
def baseEnd_4542484 : Nat := 777492552452703581386501

theorem tailTrace_4542484 : CollatzResearch.WordTrace tailWord_4542484 prefixEnd_4542484 777492552452703581386501 := by
  unfold tailWord_4542484
  simp only [CollatzResearch.WordTrace]
  refine ⟨82839001237681868674077253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110452001650242491565436337 82839001237681868674077253)
  ·
    refine ⟨15532312732065350376389485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82839001237681868674077253 15532312732065350376389485)
    ·
      refine ⟨5824617274524506391146057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15532312732065350376389485 5824617274524506391146057)
      ·
        refine ⟨4368462955893379793359543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5824617274524506391146057 4368462955893379793359543)
        ·
          refine ⟨6552694433840069690039315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4368462955893379793359543 6552694433840069690039315)
          ·
            refine ⟨9829041650760104535058973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6552694433840069690039315 9829041650760104535058973)
            ·
              refine ⟨3685890619035039200647115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9829041650760104535058973 3685890619035039200647115)
              ·
                refine ⟨5528835928552558800970673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3685890619035039200647115 5528835928552558800970673)
                ·
                  refine ⟨4146626946414419100728005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5528835928552558800970673 4146626946414419100728005)
                  ·
                    refine ⟨777492552452703581386501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4146626946414419100728005 777492552452703581386501)
                    ·
                      rfl

theorem cell23_4542484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_4542484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4542484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4542484 prefixEnd_4542484 := by exact prefixLift 4542484
  have htrace : WordTrace (prefixWord ++ tailWord_4542484) baseStart_4542484 baseEnd_4542484 := by
    simpa [prefixWord, tailWord_4542484, baseEnd_4542484] using wordTrace_append hprefix tailTrace_4542484
  have hstable : (prefixWord ++ tailWord_4542484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4542484).length < 2 ^ (prefixWord ++ tailWord_4542484).sum := by decide
  have hdescent : baseEnd_4542484 < baseStart_4542484 := by decide
  rcases family_descends (prefixWord ++ tailWord_4542484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4542519 : List Nat := [1, 1, 3, 1, 2, 2, 2, 2, 9]
def baseStart_4542519 : Nat := 118140960795 + 4542519 * 2 ^ 59
def prefixEnd_4542519 : Nat := 4983230072969 + 3 ^ 40 * 4542519 * 2
def baseEnd_4542519 : Nat := 259166181020113123024649

theorem tailTrace_4542519 : CollatzResearch.WordTrace tailWord_4542519 prefixEnd_4542519 259166181020113123024649 := by
  unfold tailWord_4542519
  simp only [CollatzResearch.WordTrace]
  refine ⟨165679279030236938325678611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110452852686824625550452407 165679279030236938325678611)
  ·
    refine ⟨248518918545355407488517917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165679279030236938325678611 248518918545355407488517917)
    ·
      refine ⟨93194594454508277808194219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 248518918545355407488517917 93194594454508277808194219)
      ·
        refine ⟨139791891681762416712291329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93194594454508277808194219 139791891681762416712291329)
        ·
          refine ⟨104843918761321812534218497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139791891681762416712291329 104843918761321812534218497)
          ·
            refine ⟨78632939070991359400663873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104843918761321812534218497 78632939070991359400663873)
            ·
              refine ⟨58974704303243519550497905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78632939070991359400663873 58974704303243519550497905)
              ·
                refine ⟨44231028227432639662873429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58974704303243519550497905 44231028227432639662873429)
                ·
                  refine ⟨259166181020113123024649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 44231028227432639662873429 259166181020113123024649)
                  ·
                    rfl

theorem cell23_4542519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 9].length) (baseStart_4542519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4542519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4542519 prefixEnd_4542519 := by exact prefixLift 4542519
  have htrace : WordTrace (prefixWord ++ tailWord_4542519) baseStart_4542519 baseEnd_4542519 := by
    simpa [prefixWord, tailWord_4542519, baseEnd_4542519] using wordTrace_append hprefix tailTrace_4542519
  have hstable : (prefixWord ++ tailWord_4542519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4542519).length < 2 ^ (prefixWord ++ tailWord_4542519).sum := by decide
  have hdescent : baseEnd_4542519 < baseStart_4542519 := by decide
  rcases family_descends (prefixWord ++ tailWord_4542519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4542550 : List Nat := [5, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5]
def baseStart_4542550 : Nat := 118140960795 + 4542550 * 2 ^ 59
def prefixEnd_4542550 : Nat := 4983230072969 + 3 ^ 40 * 4542550 * 2
def baseEnd_4542550 : Nat := 2332511547081307485934199

theorem tailTrace_4542550 : CollatzResearch.WordTrace tailWord_4542550 prefixEnd_4542550 2332511547081307485934199 := by
  unfold tailWord_4542550
  simp only [CollatzResearch.WordTrace]
  refine ⟨10355025605820289413753569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 110453606462083087080038069 10355025605820289413753569)
  ·
    refine ⟨7766269204365217060315177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10355025605820289413753569 7766269204365217060315177)
    ·
      refine ⟨5824701903273912795236383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7766269204365217060315177 5824701903273912795236383)
      ·
        refine ⟨8737052854910869192854575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5824701903273912795236383 8737052854910869192854575)
        ·
          refine ⟨13105579282366303789281863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8737052854910869192854575 13105579282366303789281863)
          ·
            refine ⟨19658368923549455683922795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13105579282366303789281863 19658368923549455683922795)
            ·
              refine ⟨29487553385324183525884193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19658368923549455683922795 29487553385324183525884193)
              ·
                refine ⟨22115665038993137644413145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29487553385324183525884193 22115665038993137644413145)
                ·
                  refine ⟨16586748779244853233309859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22115665038993137644413145 16586748779244853233309859)
                  ·
                    refine ⟨24880123168867279849964789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16586748779244853233309859 24880123168867279849964789)
                    ·
                      refine ⟨2332511547081307485934199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24880123168867279849964789 2332511547081307485934199)
                      ·
                        rfl

theorem cell23_4542550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_4542550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4542550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4542550 prefixEnd_4542550 := by exact prefixLift 4542550
  have htrace : WordTrace (prefixWord ++ tailWord_4542550) baseStart_4542550 baseEnd_4542550 := by
    simpa [prefixWord, tailWord_4542550, baseEnd_4542550] using wordTrace_append hprefix tailTrace_4542550
  have hstable : (prefixWord ++ tailWord_4542550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4542550).length < 2 ^ (prefixWord ++ tailWord_4542550).sum := by decide
  have hdescent : baseEnd_4542550 < baseStart_4542550 := by decide
  rcases family_descends (prefixWord ++ tailWord_4542550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4542576 : List Nat := [2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 5]
def baseStart_4542576 : Nat := 118140960795 + 4542576 * 2 ^ 59
def prefixEnd_4542576 : Nat := 4983230072969 + 3 ^ 40 * 4542576 * 2
def baseEnd_4542576 : Nat := 2332524897578324384209079

theorem tailTrace_4542576 : CollatzResearch.WordTrace tailWord_4542576 prefixEnd_4542576 2332524897578324384209079 := by
  unfold tailWord_4542576
  simp only [CollatzResearch.WordTrace]
  refine ⟨82840678995515218530251791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110454238660686958040335721 82840678995515218530251791)
  ·
    refine ⟨124261018493272827795377687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82840678995515218530251791 124261018493272827795377687)
    ·
      refine ⟨186391527739909241693066531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124261018493272827795377687 186391527739909241693066531)
      ·
        refine ⟨279587291609863862539599797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186391527739909241693066531 279587291609863862539599797)
        ·
          refine ⟨26211308588424737113087481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 279587291609863862539599797 26211308588424737113087481)
          ·
            refine ⟨19658481441318552834815611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26211308588424737113087481 19658481441318552834815611)
            ·
              refine ⟨29487722161977829252223417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19658481441318552834815611 29487722161977829252223417)
              ·
                refine ⟨22115791621483371939167563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29487722161977829252223417 22115791621483371939167563)
                ·
                  refine ⟨33173687432225057908751345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22115791621483371939167563 33173687432225057908751345)
                  ·
                    refine ⟨24880265574168793431563509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33173687432225057908751345 24880265574168793431563509)
                    ·
                      refine ⟨2332524897578324384209079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24880265574168793431563509 2332524897578324384209079)
                      ·
                        rfl

theorem cell23_4542576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 5].length) (baseStart_4542576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4542576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4542576 prefixEnd_4542576 := by exact prefixLift 4542576
  have htrace : WordTrace (prefixWord ++ tailWord_4542576) baseStart_4542576 baseEnd_4542576 := by
    simpa [prefixWord, tailWord_4542576, baseEnd_4542576] using wordTrace_append hprefix tailTrace_4542576
  have hstable : (prefixWord ++ tailWord_4542576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4542576).length < 2 ^ (prefixWord ++ tailWord_4542576).sum := by decide
  have hdescent : baseEnd_4542576 < baseStart_4542576 := by decide
  rcases family_descends (prefixWord ++ tailWord_4542576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4542613 : List Nat := [1, 3, 2, 1, 1, 1, 5, 2, 3, 4]
def baseStart_4542613 : Nat := 118140960795 + 4542613 * 2 ^ 59
def prefixEnd_4542613 : Nat := 4983230072969 + 3 ^ 40 * 4542613 * 2
def baseEnd_4542613 : Nat := 777514632120846913148803

theorem tailTrace_4542613 : CollatzResearch.WordTrace tailWord_4542613 prefixEnd_4542613 777514632120846913148803 := by
  unfold tailWord_4542613
  simp only [CollatzResearch.WordTrace]
  refine ⟨165682707491896392379600493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110455138327930928253066995 165682707491896392379600493)
  ·
    refine ⟨62131015309461147142350185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165682707491896392379600493 62131015309461147142350185)
    ·
      refine ⟨46598261482095860356762639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62131015309461147142350185 46598261482095860356762639)
      ·
        refine ⟨69897392223143790535143959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46598261482095860356762639 69897392223143790535143959)
        ·
          refine ⟨104846088334715685802715939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69897392223143790535143959 104846088334715685802715939)
          ·
            refine ⟨157269132502073528704073909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104846088334715685802715939 157269132502073528704073909)
            ·
              refine ⟨14743981172069393316006929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 157269132502073528704073909 14743981172069393316006929)
              ·
                refine ⟨11057985879052044987005197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14743981172069393316006929 11057985879052044987005197)
                ·
                  refine ⟨4146744704644516870126949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11057985879052044987005197 4146744704644516870126949)
                  ·
                    refine ⟨777514632120846913148803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4146744704644516870126949 777514632120846913148803)
                    ·
                      rfl

theorem cell23_4542613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 2, 3, 4].length) (baseStart_4542613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4542613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4542613 prefixEnd_4542613 := by exact prefixLift 4542613
  have htrace : WordTrace (prefixWord ++ tailWord_4542613) baseStart_4542613 baseEnd_4542613 := by
    simpa [prefixWord, tailWord_4542613, baseEnd_4542613] using wordTrace_append hprefix tailTrace_4542613
  have hstable : (prefixWord ++ tailWord_4542613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4542613).length < 2 ^ (prefixWord ++ tailWord_4542613).sum := by decide
  have hdescent : baseEnd_4542613 < baseStart_4542613 := by decide
  rcases family_descends (prefixWord ++ tailWord_4542613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4542673 : List Nat := [1, 2, 2, 1, 2, 2, 3, 4, 1, 5]
def baseStart_4542673 : Nat := 118140960795 + 4542673 * 2 ^ 59
def prefixEnd_4542673 : Nat := 4983230072969 + 3 ^ 40 * 4542673 * 2
def baseEnd_4542673 : Nat := 777524901733936834898711

theorem tailTrace_4542673 : CollatzResearch.WordTrace tailWord_4542673 prefixEnd_4542673 777524901733936834898711 := by
  unfold tailWord_4542673
  simp only [CollatzResearch.WordTrace]
  refine ⟨165684895871679022626784673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110456597247786015084523115 165684895871679022626784673)
  ·
    refine ⟨124263671903759266970088505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165684895871679022626784673 124263671903759266970088505)
    ·
      refine ⟨93197753927819450227566379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124263671903759266970088505 93197753927819450227566379)
      ·
        refine ⟨139796630891729175341349569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93197753927819450227566379 139796630891729175341349569)
        ·
          refine ⟨104847473168796881506012177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139796630891729175341349569 104847473168796881506012177)
          ·
            refine ⟨78635604876597661129509133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104847473168796881506012177 78635604876597661129509133)
            ·
              refine ⟨29488351828724122923565925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78635604876597661129509133 29488351828724122923565925)
              ·
                refine ⟨5529065967885773048168611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29488351828724122923565925 5529065967885773048168611)
                ·
                  refine ⟨8293598951828659572252917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5529065967885773048168611 8293598951828659572252917)
                  ·
                    refine ⟨777524901733936834898711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8293598951828659572252917 777524901733936834898711)
                    ·
                      rfl

theorem cell23_4542673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 4, 1, 5].length) (baseStart_4542673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4542673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4542673 prefixEnd_4542673 := by exact prefixLift 4542673
  have htrace : WordTrace (prefixWord ++ tailWord_4542673) baseStart_4542673 baseEnd_4542673 := by
    simpa [prefixWord, tailWord_4542673, baseEnd_4542673] using wordTrace_append hprefix tailTrace_4542673
  have hstable : (prefixWord ++ tailWord_4542673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4542673).length < 2 ^ (prefixWord ++ tailWord_4542673).sum := by decide
  have hdescent : baseEnd_4542673 < baseStart_4542673 := by decide
  rcases family_descends (prefixWord ++ tailWord_4542673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4542680 : List Nat := [2, 1, 2, 2, 4, 1, 2, 1, 1, 5, 2]
def baseStart_4542680 : Nat := 118140960795 + 4542680 * 2 ^ 59
def prefixEnd_4542680 : Nat := 4983230072969 + 3 ^ 40 * 4542680 * 2
def baseEnd_4542680 : Nat := 2332578299566391977308601

theorem tailTrace_4542680 : CollatzResearch.WordTrace tailWord_4542680 prefixEnd_4542680 2332578299566391977308601 := by
  unfold tailWord_4542680
  simp only [CollatzResearch.WordTrace]
  refine ⟨82842575591326831411144747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110456767455102441881526329 82842575591326831411144747)
  ·
    refine ⟨124263863386990247116717121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82842575591326831411144747 124263863386990247116717121)
    ·
      refine ⟨93197897540242685337537841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124263863386990247116717121 93197897540242685337537841)
      ·
        refine ⟨69898423155182014003153381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93197897540242685337537841 69898423155182014003153381)
        ·
          refine ⟨13105954341596627625591259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69898423155182014003153381 13105954341596627625591259)
          ·
            refine ⟨19658931512394941438386889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13105954341596627625591259 19658931512394941438386889)
            ·
              refine ⟨14744198634296206078790167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19658931512394941438386889 14744198634296206078790167)
              ·
                refine ⟨22116297951444309118185251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14744198634296206078790167 22116297951444309118185251)
                ·
                  refine ⟨33174446927166463677277877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22116297951444309118185251 33174446927166463677277877)
                  ·
                    refine ⟨3110104399421855969744801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33174446927166463677277877 3110104399421855969744801)
                    ·
                      refine ⟨2332578299566391977308601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3110104399421855969744801 2332578299566391977308601)
                      ·
                        rfl

theorem cell23_4542680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 1, 1, 5, 2].length) (baseStart_4542680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4542680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4542680 prefixEnd_4542680 := by exact prefixLift 4542680
  have htrace : WordTrace (prefixWord ++ tailWord_4542680) baseStart_4542680 baseEnd_4542680 := by
    simpa [prefixWord, tailWord_4542680, baseEnd_4542680] using wordTrace_append hprefix tailTrace_4542680
  have hstable : (prefixWord ++ tailWord_4542680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4542680).length < 2 ^ (prefixWord ++ tailWord_4542680).sum := by decide
  have hdescent : baseEnd_4542680 < baseStart_4542680 := by decide
  rcases family_descends (prefixWord ++ tailWord_4542680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4542723 : List Nat := [1, 1, 1, 3, 2, 3, 2, 3, 1, 2, 4]
def baseStart_4542723 : Nat := 118140960795 + 4542723 * 2 ^ 59
def prefixEnd_4542723 : Nat := 4983230072969 + 3 ^ 40 * 4542723 * 2
def baseEnd_4542723 : Nat := 2332600379234535309070903

theorem tailTrace_4542723 : CollatzResearch.WordTrace tailWord_4542723 prefixEnd_4542723 2332600379234535309070903 := by
  unfold tailWord_4542723
  simp only [CollatzResearch.WordTrace]
  refine ⟨165686719521497881166104823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110457813014331920777403215 165686719521497881166104823)
  ·
    refine ⟨248530079282246821749157235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165686719521497881166104823 248530079282246821749157235)
    ·
      refine ⟨372795118923370232623735853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248530079282246821749157235 372795118923370232623735853)
      ·
        refine ⟨139798169596263837233900945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 372795118923370232623735853 139798169596263837233900945)
        ·
          refine ⟨104848627197197877925425709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139798169596263837233900945 104848627197197877925425709)
          ·
            refine ⟨39318235198949204222034641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 104848627197197877925425709 39318235198949204222034641)
            ·
              refine ⟨29488676399211903166525981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39318235198949204222034641 29488676399211903166525981)
              ·
                refine ⟨11058253649704463687447243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29488676399211903166525981 11058253649704463687447243)
                ·
                  refine ⟨16587380474556695531170865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11058253649704463687447243 16587380474556695531170865)
                  ·
                    refine ⟨12440535355917521648378149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16587380474556695531170865 12440535355917521648378149)
                    ·
                      refine ⟨2332600379234535309070903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12440535355917521648378149 2332600379234535309070903)
                      ·
                        rfl

theorem cell23_4542723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 3, 1, 2, 4].length) (baseStart_4542723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4542723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4542723 prefixEnd_4542723 := by exact prefixLift 4542723
  have htrace : WordTrace (prefixWord ++ tailWord_4542723) baseStart_4542723 baseEnd_4542723 := by
    simpa [prefixWord, tailWord_4542723, baseEnd_4542723] using wordTrace_append hprefix tailTrace_4542723
  have hstable : (prefixWord ++ tailWord_4542723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4542723).length < 2 ^ (prefixWord ++ tailWord_4542723).sum := by decide
  have hdescent : baseEnd_4542723 < baseStart_4542723 := by decide
  rcases family_descends (prefixWord ++ tailWord_4542723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4542724 : List Nat := [2, 3, 2, 2, 4, 1, 1, 2, 1, 5]
def baseStart_4542724 : Nat := 118140960795 + 4542724 * 2 ^ 59
def prefixEnd_4542724 : Nat := 4983230072969 + 3 ^ 40 * 4542724 * 2
def baseEnd_4542724 : Nat := 777533630905063268386133

theorem tailTrace_4542724 : CollatzResearch.WordTrace tailWord_4542724 prefixEnd_4542724 777533630905063268386133 := by
  unfold tailWord_4542724
  simp only [CollatzResearch.WordTrace]
  refine ⟨82843377997247129168445613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110457837329662838891260817 82843377997247129168445613)
  ·
    refine ⟨31066266748967673438167105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82843377997247129168445613 31066266748967673438167105)
    ·
      refine ⟨23299700061725755078625329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31066266748967673438167105 23299700061725755078625329)
      ·
        refine ⟨17474775046294316308968997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23299700061725755078625329 17474775046294316308968997)
        ·
          refine ⟨3276520321180184307931687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17474775046294316308968997 3276520321180184307931687)
          ·
            refine ⟨4914780481770276461897531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3276520321180184307931687 4914780481770276461897531)
            ·
              refine ⟨7372170722655414692846297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4914780481770276461897531 7372170722655414692846297)
              ·
                refine ⟨5529128041991561019634723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7372170722655414692846297 5529128041991561019634723)
                ·
                  refine ⟨8293692062987341529452085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5529128041991561019634723 8293692062987341529452085)
                  ·
                    refine ⟨777533630905063268386133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8293692062987341529452085 777533630905063268386133)
                    ·
                      rfl

theorem cell23_4542724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 2, 1, 5].length) (baseStart_4542724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4542724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4542724 prefixEnd_4542724 := by exact prefixLift 4542724
  have htrace : WordTrace (prefixWord ++ tailWord_4542724) baseStart_4542724 baseEnd_4542724 := by
    simpa [prefixWord, tailWord_4542724, baseEnd_4542724] using wordTrace_append hprefix tailTrace_4542724
  have hstable : (prefixWord ++ tailWord_4542724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4542724).length < 2 ^ (prefixWord ++ tailWord_4542724).sum := by decide
  have hdescent : baseEnd_4542724 < baseStart_4542724 := by decide
  rcases family_descends (prefixWord ++ tailWord_4542724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4542727 : List Nat := [1, 1, 4, 5, 1, 1, 1, 1, 3, 1, 4]
def baseStart_4542727 : Nat := 118140960795 + 4542727 * 2 ^ 59
def prefixEnd_4542727 : Nat := 4983230072969 + 3 ^ 40 * 4542727 * 2
def baseEnd_4542727 : Nat := 2332602433157153293420885

theorem tailTrace_4542727 : CollatzResearch.WordTrace tailWord_4542727 prefixEnd_4542727 2332602433157153293420885 := by
  unfold tailWord_4542727
  simp only [CollatzResearch.WordTrace]
  refine ⟨165686865413483389849250435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110457910275655593232833623 165686865413483389849250435)
  ·
    refine ⟨248530298120225084773875653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165686865413483389849250435 248530298120225084773875653)
    ·
      refine ⟨46599430897542203395101685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 248530298120225084773875653 46599430897542203395101685)
      ·
        refine ⟨4368696646644581568290783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46599430897542203395101685 4368696646644581568290783)
        ·
          refine ⟨6553044969966872352436175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4368696646644581568290783 6553044969966872352436175)
          ·
            refine ⟨9829567454950308528654263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6553044969966872352436175 9829567454950308528654263)
            ·
              refine ⟨14744351182425462792981395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9829567454950308528654263 14744351182425462792981395)
              ·
                refine ⟨22116526773638194189472093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14744351182425462792981395 22116526773638194189472093)
                ·
                  refine ⟨8293697540114322821052035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22116526773638194189472093 8293697540114322821052035)
                  ·
                    refine ⟨12440546310171484231578053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8293697540114322821052035 12440546310171484231578053)
                    ·
                      refine ⟨2332602433157153293420885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12440546310171484231578053 2332602433157153293420885)
                      ·
                        rfl

theorem cell23_4542727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_4542727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4542727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4542727 prefixEnd_4542727 := by exact prefixLift 4542727
  have htrace : WordTrace (prefixWord ++ tailWord_4542727) baseStart_4542727 baseEnd_4542727 := by
    simpa [prefixWord, tailWord_4542727, baseEnd_4542727] using wordTrace_append hprefix tailTrace_4542727
  have hstable : (prefixWord ++ tailWord_4542727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4542727).length < 2 ^ (prefixWord ++ tailWord_4542727).sum := by decide
  have hdescent : baseEnd_4542727 < baseStart_4542727 := by decide
  rcases family_descends (prefixWord ++ tailWord_4542727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4542744 : List Nat := [2, 1, 2, 3, 1, 2, 2, 5, 1, 2, 2]
def baseStart_4542744 : Nat := 118140960795 + 4542744 * 2 ^ 59
def prefixEnd_4542744 : Nat := 4983230072969 + 3 ^ 40 * 4542744 * 2
def baseEnd_4542744 : Nat := 2332611162328279726908307

theorem tailTrace_4542744 : CollatzResearch.WordTrace tailWord_4542744 prefixEnd_4542744 2332611162328279726908307 := by
  unfold tailWord_4542744
  simp only [CollatzResearch.WordTrace]
  refine ⟨82843742727210900876309643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110458323636281201168412857 82843742727210900876309643)
  ·
    refine ⟨124265614090816351314464465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82843742727210900876309643 124265614090816351314464465)
    ·
      refine ⟨93199210568112263485848349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124265614090816351314464465 93199210568112263485848349)
      ·
        refine ⟨34949703963042098807193131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93199210568112263485848349 34949703963042098807193131)
        ·
          refine ⟨52424555944563148210789697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34949703963042098807193131 52424555944563148210789697)
          ·
            refine ⟨39318416958422361158092273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52424555944563148210789697 39318416958422361158092273)
            ·
              refine ⟨29488812718816770868569205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39318416958422361158092273 29488812718816770868569205)
              ·
                refine ⟨2764576192389072268928363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29488812718816770868569205 2764576192389072268928363)
                ·
                  refine ⟨4146864288583608403392545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2764576192389072268928363 4146864288583608403392545)
                  ·
                    refine ⟨3110148216437706302544409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4146864288583608403392545 3110148216437706302544409)
                    ·
                      refine ⟨2332611162328279726908307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3110148216437706302544409 2332611162328279726908307)
                      ·
                        rfl

theorem cell23_4542744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 5, 1, 2, 2].length) (baseStart_4542744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4542744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4542744 prefixEnd_4542744 := by exact prefixLift 4542744
  have htrace : WordTrace (prefixWord ++ tailWord_4542744) baseStart_4542744 baseEnd_4542744 := by
    simpa [prefixWord, tailWord_4542744, baseEnd_4542744] using wordTrace_append hprefix tailTrace_4542744
  have hstable : (prefixWord ++ tailWord_4542744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4542744).length < 2 ^ (prefixWord ++ tailWord_4542744).sum := by decide
  have hdescent : baseEnd_4542744 < baseStart_4542744 := by decide
  rcases family_descends (prefixWord ++ tailWord_4542744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4542750 : List Nat := [4, 3, 2, 1, 1, 12]
def baseStart_4542750 : Nat := 118140960795 + 4542750 * 2 ^ 59
def prefixEnd_4542750 : Nat := 4983230072969 + 3 ^ 40 * 4542750 * 2
def baseEnd_4542750 : Nat := 9599235568774513182853

theorem tailTrace_4542750 : CollatzResearch.WordTrace tailWord_4542750 prefixEnd_4542750 9599235568774513182853 := by
  unfold tailWord_4542750
  simp only [CollatzResearch.WordTrace]
  refine ⟨20710963036550008097167213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110458469528266709851558469 20710963036550008097167213)
  ·
    refine ⟨7766611138706253036437705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20710963036550008097167213 7766611138706253036437705)
    ·
      refine ⟨5824958354029689777328279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7766611138706253036437705 5824958354029689777328279)
      ·
        refine ⟨8737437531044534665992419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5824958354029689777328279 8737437531044534665992419)
        ·
          refine ⟨13106156296566801998988629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8737437531044534665992419 13106156296566801998988629)
          ·
            refine ⟨9599235568774513182853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 13106156296566801998988629 9599235568774513182853)
            ·
              rfl

theorem cell23_4542750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 12].length) (baseStart_4542750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4542750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4542750 prefixEnd_4542750 := by exact prefixLift 4542750
  have htrace : WordTrace (prefixWord ++ tailWord_4542750) baseStart_4542750 baseEnd_4542750 := by
    simpa [prefixWord, tailWord_4542750, baseEnd_4542750] using wordTrace_append hprefix tailTrace_4542750
  have hstable : (prefixWord ++ tailWord_4542750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4542750).length < 2 ^ (prefixWord ++ tailWord_4542750).sum := by decide
  have hdescent : baseEnd_4542750 < baseStart_4542750 := by decide
  rcases family_descends (prefixWord ++ tailWord_4542750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4542777 : List Nat := [1, 2, 1, 6, 1, 2, 2, 1, 1, 3, 3]
def baseStart_4542777 : Nat := 118140960795 + 4542777 * 2 ^ 59
def prefixEnd_4542777 : Nat := 4983230072969 + 3 ^ 40 * 4542777 * 2
def baseEnd_4542777 : Nat := 2332628107189878097795655

theorem tailTrace_4542777 : CollatzResearch.WordTrace tailWord_4542777 prefixEnd_4542777 2332628107189878097795655 := by
  unfold tailWord_4542777
  simp only [CollatzResearch.WordTrace]
  refine ⟨165688689063302248388570585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110459126042201498925713723 165688689063302248388570585)
  ·
    refine ⟨124266516797476686291427939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165688689063302248388570585 124266516797476686291427939)
    ·
      refine ⟨186399775196215029437141909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124266516797476686291427939 186399775196215029437141909)
      ·
        refine ⟨8737489462322579504866027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 186399775196215029437141909 8737489462322579504866027)
        ·
          refine ⟨13106234193483869257299041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8737489462322579504866027 13106234193483869257299041)
          ·
            refine ⟨9829675645112901942974281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13106234193483869257299041 9829675645112901942974281)
            ·
              refine ⟨7372256733834676457230711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9829675645112901942974281 7372256733834676457230711)
              ·
                refine ⟨11058385100752014685846067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7372256733834676457230711 11058385100752014685846067)
                ·
                  refine ⟨16587577651128022028769101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11058385100752014685846067 16587577651128022028769101)
                  ·
                    refine ⟨6220341619173008260788413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16587577651128022028769101 6220341619173008260788413)
                    ·
                      refine ⟨2332628107189878097795655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6220341619173008260788413 2332628107189878097795655)
                      ·
                        rfl

theorem cell23_4542777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_4542777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4542777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4542777 prefixEnd_4542777 := by exact prefixLift 4542777
  have htrace : WordTrace (prefixWord ++ tailWord_4542777) baseStart_4542777 baseEnd_4542777 := by
    simpa [prefixWord, tailWord_4542777, baseEnd_4542777] using wordTrace_append hprefix tailTrace_4542777
  have hstable : (prefixWord ++ tailWord_4542777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4542777).length < 2 ^ (prefixWord ++ tailWord_4542777).sum := by decide
  have hdescent : baseEnd_4542777 < baseStart_4542777 := by decide
  rcases family_descends (prefixWord ++ tailWord_4542777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4542783 : List Nat := [1, 1, 2, 2, 4, 1, 1, 2, 2, 3, 4]
def baseStart_4542783 : Nat := 118140960795 + 4542783 * 2 ^ 59
def prefixEnd_4542783 : Nat := 4983230072969 + 3 ^ 40 * 4542783 * 2
def baseEnd_4542783 : Nat := 2332631188073805074320627

theorem tailTrace_4542783 : CollatzResearch.WordTrace tailWord_4542783 prefixEnd_4542783 2332631188073805074320627 := by
  unfold tailWord_4542783
  simp only [CollatzResearch.WordTrace]
  refine ⟨165688907901280511413289003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110459271934187007608859335 165688907901280511413289003)
  ·
    refine ⟨248533361851920767119933505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165688907901280511413289003 248533361851920767119933505)
    ·
      refine ⟨186400021388940575339950129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 248533361851920767119933505 186400021388940575339950129)
      ·
        refine ⟨139800016041705431504962597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186400021388940575339950129 139800016041705431504962597)
        ·
          refine ⟨26212503007819768407180487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 139800016041705431504962597 26212503007819768407180487)
          ·
            refine ⟨39318754511729652610770731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26212503007819768407180487 39318754511729652610770731)
            ·
              refine ⟨58978131767594478916156097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39318754511729652610770731 58978131767594478916156097)
              ·
                refine ⟨44233598825695859187117073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58978131767594478916156097 44233598825695859187117073)
                ·
                  refine ⟨33175199119271894390337805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44233598825695859187117073 33175199119271894390337805)
                  ·
                    refine ⟨12440699669726960396376677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33175199119271894390337805 12440699669726960396376677)
                    ·
                      refine ⟨2332631188073805074320627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12440699669726960396376677 2332631188073805074320627)
                      ·
                        rfl

theorem cell23_4542783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 2, 3, 4].length) (baseStart_4542783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4542783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4542783 prefixEnd_4542783 := by exact prefixLift 4542783
  have htrace : WordTrace (prefixWord ++ tailWord_4542783) baseStart_4542783 baseEnd_4542783 := by
    simpa [prefixWord, tailWord_4542783, baseEnd_4542783] using wordTrace_append hprefix tailTrace_4542783
  have hstable : (prefixWord ++ tailWord_4542783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4542783).length < 2 ^ (prefixWord ++ tailWord_4542783).sum := by decide
  have hdescent : baseEnd_4542783 < baseStart_4542783 := by decide
  rcases family_descends (prefixWord ++ tailWord_4542783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4542803 : List Nat := [1, 1, 1, 2, 1, 1, 4, 2, 1, 6, 3]
def baseStart_4542803 : Nat := 118140960795 + 4542803 * 2 ^ 59
def prefixEnd_4542803 : Nat := 4983230072969 + 3 ^ 40 * 4542803 * 2
def baseEnd_4542803 : Nat := 2332641457686894996070535

theorem tailTrace_4542803 : CollatzResearch.WordTrace tailWord_4542803 prefixEnd_4542803 2332641457686894996070535 := by
  unfold tailWord_4542803
  simp only [CollatzResearch.WordTrace]
  refine ⟨165689637361208054829017063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110459758240805369886011375 165689637361208054829017063)
  ·
    refine ⟨248534456041812082243525595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165689637361208054829017063 248534456041812082243525595)
    ·
      refine ⟨372801684062718123365288393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248534456041812082243525595 372801684062718123365288393)
      ·
        refine ⟨279601263047038592523966295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 372801684062718123365288393 279601263047038592523966295)
        ·
          refine ⟨419401894570557888785949443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 279601263047038592523966295 419401894570557888785949443)
          ·
            refine ⟨629102841855836833178924165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 419401894570557888785949443 629102841855836833178924165)
            ·
              refine ⟨117956782847969406221048281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 629102841855836833178924165 117956782847969406221048281)
              ·
                refine ⟨88467587135977054665786211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 117956782847969406221048281 88467587135977054665786211)
                ·
                  refine ⟨132701380703965581998679317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 88467587135977054665786211 132701380703965581998679317)
                  ·
                    refine ⟨6220377220498386656188093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 132701380703965581998679317 6220377220498386656188093)
                    ·
                      refine ⟨2332641457686894996070535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6220377220498386656188093 2332641457686894996070535)
                      ·
                        rfl

theorem cell23_4542803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 6, 3].length) (baseStart_4542803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4542803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4542803 prefixEnd_4542803 := by exact prefixLift 4542803
  have htrace : WordTrace (prefixWord ++ tailWord_4542803) baseStart_4542803 baseEnd_4542803 := by
    simpa [prefixWord, tailWord_4542803, baseEnd_4542803] using wordTrace_append hprefix tailTrace_4542803
  have hstable : (prefixWord ++ tailWord_4542803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4542803).length < 2 ^ (prefixWord ++ tailWord_4542803).sum := by decide
  have hdescent : baseEnd_4542803 < baseStart_4542803 := by decide
  rcases family_descends (prefixWord ++ tailWord_4542803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4542804 : List Nat := [2, 4, 1, 1, 2, 3, 1, 3, 1, 3, 2]
def baseStart_4542804 : Nat := 118140960795 + 4542804 * 2 ^ 59
def prefixEnd_4542804 : Nat := 4983230072969 + 3 ^ 40 * 4542804 * 2
def baseEnd_4542804 : Nat := 2332641971167549492158031

theorem tailTrace_4542804 : CollatzResearch.WordTrace tailWord_4542804 prefixEnd_4542804 2332641971167549492158031 := by
  unfold tailWord_4542804
  simp only [CollatzResearch.WordTrace]
  refine ⟨82844836917102215999901733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110459782556136287999868977 82844836917102215999901733)
  ·
    refine ⟨15533406921956665499981575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82844836917102215999901733 15533406921956665499981575)
    ·
      refine ⟨23300110382934998249972363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15533406921956665499981575 23300110382934998249972363)
      ·
        refine ⟨34950165574402497374958545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23300110382934998249972363 34950165574402497374958545)
        ·
          refine ⟨26212624180801873031218909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34950165574402497374958545 26212624180801873031218909)
          ·
            refine ⟨9829734067800702386707091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26212624180801873031218909 9829734067800702386707091)
            ·
              refine ⟨14744601101701053580060637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9829734067800702386707091 14744601101701053580060637)
              ·
                refine ⟨5529225413137895092522739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14744601101701053580060637 5529225413137895092522739)
                ·
                  refine ⟨8293838119706842638784109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5529225413137895092522739 8293838119706842638784109)
                  ·
                    refine ⟨3110189294890065989544041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8293838119706842638784109 3110189294890065989544041)
                    ·
                      refine ⟨2332641971167549492158031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3110189294890065989544041 2332641971167549492158031)
                      ·
                        rfl

theorem cell23_4542804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 3, 1, 3, 2].length) (baseStart_4542804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4542804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4542804 prefixEnd_4542804 := by exact prefixLift 4542804
  have htrace : WordTrace (prefixWord ++ tailWord_4542804) baseStart_4542804 baseEnd_4542804 := by
    simpa [prefixWord, tailWord_4542804, baseEnd_4542804] using wordTrace_append hprefix tailTrace_4542804
  have hstable : (prefixWord ++ tailWord_4542804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4542804).length < 2 ^ (prefixWord ++ tailWord_4542804).sum := by decide
  have hdescent : baseEnd_4542804 < baseStart_4542804 := by decide
  rcases family_descends (prefixWord ++ tailWord_4542804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4542834 : List Nat := [3, 2, 1, 2, 1, 5, 1, 1, 1, 4, 2]
def baseStart_4542834 : Nat := 118140960795 + 4542834 * 2 ^ 59
def prefixEnd_4542834 : Nat := 4983230072969 + 3 ^ 40 * 4542834 * 2
def baseEnd_4542834 : Nat := 2332657375587184374782893

theorem tailTrace_4542834 : CollatzResearch.WordTrace tailWord_4542834 prefixEnd_4542834 2332657375587184374782893 := by
  unfold tailWord_4542834
  simp only [CollatzResearch.WordTrace]
  refine ⟨41422692006023936780848889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110460512016063831415597037 41422692006023936780848889)
  ·
    refine ⟨31067019004517952585636667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41422692006023936780848889 31067019004517952585636667)
    ·
      refine ⟨46600528506776928878455001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31067019004517952585636667 46600528506776928878455001)
      ·
        refine ⟨34950396380082696658841251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46600528506776928878455001 34950396380082696658841251)
        ·
          refine ⟨52425594570124044988261877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34950396380082696658841251 52425594570124044988261877)
          ·
            refine ⟨4914899490949129217649551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52425594570124044988261877 4914899490949129217649551)
            ·
              refine ⟨7372349236423693826474327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4914899490949129217649551 7372349236423693826474327)
              ·
                refine ⟨11058523854635540739711491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7372349236423693826474327 11058523854635540739711491)
                ·
                  refine ⟨16587785781953311109567237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11058523854635540739711491 16587785781953311109567237)
                  ·
                    refine ⟨3110209834116245833043857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16587785781953311109567237 3110209834116245833043857)
                    ·
                      refine ⟨2332657375587184374782893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3110209834116245833043857 2332657375587184374782893)
                      ·
                        rfl

theorem cell23_4542834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 1, 1, 4, 2].length) (baseStart_4542834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4542834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4542834 prefixEnd_4542834 := by exact prefixLift 4542834
  have htrace : WordTrace (prefixWord ++ tailWord_4542834) baseStart_4542834 baseEnd_4542834 := by
    simpa [prefixWord, tailWord_4542834, baseEnd_4542834] using wordTrace_append hprefix tailTrace_4542834
  have hstable : (prefixWord ++ tailWord_4542834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4542834).length < 2 ^ (prefixWord ++ tailWord_4542834).sum := by decide
  have hdescent : baseEnd_4542834 < baseStart_4542834 := by decide
  rcases family_descends (prefixWord ++ tailWord_4542834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4542838 : List Nat := [5, 1, 1, 4, 1, 1, 2, 2, 1, 3, 2]
def baseStart_4542838 : Nat := 118140960795 + 4542838 * 2 ^ 59
def prefixEnd_4542838 : Nat := 4983230072969 + 3 ^ 40 * 4542838 * 2
def baseEnd_4542838 : Nat := 2332659429509802359132875

theorem tailTrace_4542838 : CollatzResearch.WordTrace tailWord_4542838 prefixEnd_4542838 2332659429509802359132875 := by
  unfold tailWord_4542838
  simp only [CollatzResearch.WordTrace]
  refine ⟨10355682119755078487908823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 110460609277387503871027445 10355682119755078487908823)
  ·
    refine ⟨15533523179632617731863235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10355682119755078487908823 15533523179632617731863235)
    ·
      refine ⟨23300284769448926597794853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15533523179632617731863235 23300284769448926597794853)
      ·
        refine ⟨4368803394271673737086535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23300284769448926597794853 4368803394271673737086535)
        ·
          refine ⟨6553205091407510605629803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4368803394271673737086535 6553205091407510605629803)
          ·
            refine ⟨9829807637111265908444705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6553205091407510605629803 9829807637111265908444705)
            ·
              refine ⟨7372355727833449431333529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9829807637111265908444705 7372355727833449431333529)
              ·
                refine ⟨5529266795875087073500147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7372355727833449431333529 5529266795875087073500147)
                ·
                  refine ⟨8293900193812630610250221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5529266795875087073500147 8293900193812630610250221)
                  ·
                    refine ⟨3110212572679736478843833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8293900193812630610250221 3110212572679736478843833)
                    ·
                      refine ⟨2332659429509802359132875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3110212572679736478843833 2332659429509802359132875)
                      ·
                        rfl

theorem cell23_4542838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_4542838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4542838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4542838 prefixEnd_4542838 := by exact prefixLift 4542838
  have htrace : WordTrace (prefixWord ++ tailWord_4542838) baseStart_4542838 baseEnd_4542838 := by
    simpa [prefixWord, tailWord_4542838, baseEnd_4542838] using wordTrace_append hprefix tailTrace_4542838
  have hstable : (prefixWord ++ tailWord_4542838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4542838).length < 2 ^ (prefixWord ++ tailWord_4542838).sum := by decide
  have hdescent : baseEnd_4542838 < baseStart_4542838 := by decide
  rcases family_descends (prefixWord ++ tailWord_4542838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4542857 : List Nat := [1, 2, 1, 1, 6, 1, 3, 3, 5]
def baseStart_4542857 : Nat := 118140960795 + 4542857 * 2 ^ 59
def prefixEnd_4542857 : Nat := 4983230072969 + 3 ^ 40 * 4542857 * 2
def baseEnd_4542857 : Nat := 259185465071359753866143

theorem tailTrace_4542857 : CollatzResearch.WordTrace tailWord_4542857 prefixEnd_4542857 259185465071359753866143 := by
  unfold tailWord_4542857
  simp only [CollatzResearch.WordTrace]
  refine ⟨165691606903012422051482825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110461071268674948034321883 165691606903012422051482825)
  ·
    refine ⟨124268705177259316538612119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165691606903012422051482825 124268705177259316538612119)
    ·
      refine ⟨186403057765888974807918179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124268705177259316538612119 186403057765888974807918179)
      ·
        refine ⟨279604586648833462211877269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186403057765888974807918179 279604586648833462211877269)
        ·
          refine ⟨13106464999164068541181747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 279604586648833462211877269 13106464999164068541181747)
          ·
            refine ⟨19659697498746102811772621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13106464999164068541181747 19659697498746102811772621)
            ·
              refine ⟨7372386562029788554414733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19659697498746102811772621 7372386562029788554414733)
              ·
                refine ⟨2764644960761170707905525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7372386562029788554414733 2764644960761170707905525)
                ·
                  refine ⟨259185465071359753866143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2764644960761170707905525 259185465071359753866143)
                  ·
                    rfl

theorem cell23_4542857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 3, 5].length) (baseStart_4542857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4542857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4542857 prefixEnd_4542857 := by exact prefixLift 4542857
  have htrace : WordTrace (prefixWord ++ tailWord_4542857) baseStart_4542857 baseEnd_4542857 := by
    simpa [prefixWord, tailWord_4542857, baseEnd_4542857] using wordTrace_append hprefix tailTrace_4542857
  have hstable : (prefixWord ++ tailWord_4542857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4542857).length < 2 ^ (prefixWord ++ tailWord_4542857).sum := by decide
  have hdescent : baseEnd_4542857 < baseStart_4542857 := by decide
  rcases family_descends (prefixWord ++ tailWord_4542857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4542874 : List Nat := [3, 1, 1, 4, 1, 3, 3, 2, 5]
def baseStart_4542874 : Nat := 118140960795 + 4542874 * 2 ^ 59
def prefixEnd_4542874 : Nat := 4983230072969 + 3 ^ 40 * 4542874 * 2
def baseEnd_4542874 : Nat := 259186434979262690920301

theorem tailTrace_4542874 : CollatzResearch.WordTrace tailWord_4542874 prefixEnd_4542874 259186434979262690920301 := by
  unfold tailWord_4542874
  simp only [CollatzResearch.WordTrace]
  refine ⟨41423056735987708488712919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110461484629300555969901117 41423056735987708488712919)
  ·
    refine ⟨62134585103981562733069379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41423056735987708488712919 62134585103981562733069379)
    ·
      refine ⟨93201877655972344099604069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62134585103981562733069379 93201877655972344099604069)
      ·
        refine ⟨17475352060494814518675763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 93201877655972344099604069 17475352060494814518675763)
        ·
          refine ⟨26213028090742221778013645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17475352060494814518675763 26213028090742221778013645)
          ·
            refine ⟨9829885534028333166755117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26213028090742221778013645 9829885534028333166755117)
            ·
              refine ⟨3686207075260624937533169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9829885534028333166755117 3686207075260624937533169)
              ·
                refine ⟨2764655306445468703149877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3686207075260624937533169 2764655306445468703149877)
                ·
                  refine ⟨259186434979262690920301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2764655306445468703149877 259186434979262690920301)
                  ·
                    rfl

theorem cell23_4542874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 3, 2, 5].length) (baseStart_4542874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4542874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4542874 prefixEnd_4542874 := by exact prefixLift 4542874
  have htrace : WordTrace (prefixWord ++ tailWord_4542874) baseStart_4542874 baseEnd_4542874 := by
    simpa [prefixWord, tailWord_4542874, baseEnd_4542874] using wordTrace_append hprefix tailTrace_4542874
  have hstable : (prefixWord ++ tailWord_4542874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4542874).length < 2 ^ (prefixWord ++ tailWord_4542874).sum := by decide
  have hdescent : baseEnd_4542874 < baseStart_4542874 := by decide
  rcases family_descends (prefixWord ++ tailWord_4542874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4542880 : List Nat := [2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 5]
def baseStart_4542880 : Nat := 118140960795 + 4542880 * 2 ^ 59
def prefixEnd_4542880 : Nat := 4983230072969 + 3 ^ 40 * 4542880 * 2
def baseEnd_4542880 : Nat := 2332680995697291194807681

theorem tailTrace_4542880 : CollatzResearch.WordTrace tailWord_4542880 prefixEnd_4542880 2332680995697291194807681 := by
  unfold tailWord_4542880
  simp only [CollatzResearch.WordTrace]
  refine ⟨82846222890964548489785047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110461630521286064653046729 82846222890964548489785047)
  ·
    refine ⟨124269334336446822734677571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82846222890964548489785047 124269334336446822734677571)
    ·
      refine ⟨186404001504670234102016357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124269334336446822734677571 186404001504670234102016357)
      ·
        refine ⟨34950750282125668894128067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 186404001504670234102016357 34950750282125668894128067)
        ·
          refine ⟨52426125423188503341192101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34950750282125668894128067 52426125423188503341192101)
          ·
            refine ⟨9829898516847844376473519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52426125423188503341192101 9829898516847844376473519)
            ·
              refine ⟨14744847775271766564710279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9829898516847844376473519 14744847775271766564710279)
              ·
                refine ⟨22117271662907649847065419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14744847775271766564710279 22117271662907649847065419)
                ·
                  refine ⟨33175907494361474770598129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22117271662907649847065419 33175907494361474770598129)
                  ·
                    refine ⟨24881930620771106077948597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33175907494361474770598129 24881930620771106077948597)
                    ·
                      refine ⟨2332680995697291194807681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24881930620771106077948597 2332680995697291194807681)
                      ·
                        rfl

theorem cell23_4542880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_4542880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4542880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4542880 prefixEnd_4542880 := by exact prefixLift 4542880
  have htrace : WordTrace (prefixWord ++ tailWord_4542880) baseStart_4542880 baseEnd_4542880 := by
    simpa [prefixWord, tailWord_4542880, baseEnd_4542880] using wordTrace_append hprefix tailTrace_4542880
  have hstable : (prefixWord ++ tailWord_4542880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4542880).length < 2 ^ (prefixWord ++ tailWord_4542880).sum := by decide
  have hdescent : baseEnd_4542880 < baseStart_4542880 := by decide
  rcases family_descends (prefixWord ++ tailWord_4542880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4542934 : List Nat := [5, 2, 1, 1, 1, 1, 2, 3, 3, 4]
def baseStart_4542934 : Nat := 118140960795 + 4542934 * 2 ^ 59
def prefixEnd_4542934 : Nat := 4983230072969 + 3 ^ 40 * 4542934 * 2
def baseEnd_4542934 : Nat := 777569574550877994510811

theorem tailTrace_4542934 : CollatzResearch.WordTrace tailWord_4542934 prefixEnd_4542934 777569574550877994510811 := by
  unfold tailWord_4542934
  simp only [CollatzResearch.WordTrace]
  refine ⟨10355900957733341512627241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 110462943549155642801357237 10355900957733341512627241)
  ·
    refine ⟨7766925718300006134470431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10355900957733341512627241 7766925718300006134470431)
    ·
      refine ⟨11650388577450009201705647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7766925718300006134470431 11650388577450009201705647)
      ·
        refine ⟨17475582866175013802558471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11650388577450009201705647 17475582866175013802558471)
        ·
          refine ⟨26213374299262520703837707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17475582866175013802558471 26213374299262520703837707)
          ·
            refine ⟨39320061448893781055756561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26213374299262520703837707 39320061448893781055756561)
            ·
              refine ⟨29490046086670335791817421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39320061448893781055756561 29490046086670335791817421)
              ·
                refine ⟨11058767282501375921931533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29490046086670335791817421 11058767282501375921931533)
                ·
                  refine ⟨4147037730938015970724325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11058767282501375921931533 4147037730938015970724325)
                  ·
                    refine ⟨777569574550877994510811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4147037730938015970724325 777569574550877994510811)
                    ·
                      rfl

theorem cell23_4542934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_4542934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4542934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4542934 prefixEnd_4542934 := by exact prefixLift 4542934
  have htrace : WordTrace (prefixWord ++ tailWord_4542934) baseStart_4542934 baseEnd_4542934 := by
    simpa [prefixWord, tailWord_4542934, baseEnd_4542934] using wordTrace_append hprefix tailTrace_4542934
  have hstable : (prefixWord ++ tailWord_4542934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4542934).length < 2 ^ (prefixWord ++ tailWord_4542934).sum := by decide
  have hdescent : baseEnd_4542934 < baseStart_4542934 := by decide
  rcases family_descends (prefixWord ++ tailWord_4542934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4542960 : List Nat := [2, 1, 1, 1, 3, 3, 1, 3, 3, 5]
def baseStart_4542960 : Nat := 118140960795 + 4542960 * 2 ^ 59
def prefixEnd_4542960 : Nat := 4983230072969 + 3 ^ 40 * 4542960 * 2
def baseEnd_4542960 : Nat := 777574024716550293935771

theorem tailTrace_4542960 : CollatzResearch.WordTrace tailWord_4542960 prefixEnd_4542960 777574024716550293935771 := by
  unfold tailWord_4542960
  simp only [CollatzResearch.WordTrace]
  refine ⟨82847681810819635321241167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110463575747759513761654889 82847681810819635321241167)
  ·
    refine ⟨124271522716229452981861751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82847681810819635321241167 124271522716229452981861751)
    ·
      refine ⟨186407284074344179472792627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124271522716229452981861751 186407284074344179472792627)
      ·
        refine ⟨279610926111516269209188941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186407284074344179472792627 279610926111516269209188941)
        ·
          refine ⟨104854097291818600953445853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 279610926111516269209188941 104854097291818600953445853)
          ·
            refine ⟨39320286484431975357542195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 104854097291818600953445853 39320286484431975357542195)
            ·
              refine ⟨58980429726647963036313293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39320286484431975357542195 58980429726647963036313293)
              ·
                refine ⟨22117661147492986138617485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58980429726647963036313293 22117661147492986138617485)
                ·
                  refine ⟨8294122930309869801981557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22117661147492986138617485 8294122930309869801981557)
                  ·
                    refine ⟨777574024716550293935771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8294122930309869801981557 777574024716550293935771)
                    ·
                      rfl

theorem cell23_4542960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 3, 3, 5].length) (baseStart_4542960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4542960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4542960 prefixEnd_4542960 := by exact prefixLift 4542960
  have htrace : WordTrace (prefixWord ++ tailWord_4542960) baseStart_4542960 baseEnd_4542960 := by
    simpa [prefixWord, tailWord_4542960, baseEnd_4542960] using wordTrace_append hprefix tailTrace_4542960
  have hstable : (prefixWord ++ tailWord_4542960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4542960).length < 2 ^ (prefixWord ++ tailWord_4542960).sum := by decide
  have hdescent : baseEnd_4542960 < baseStart_4542960 := by decide
  rcases family_descends (prefixWord ++ tailWord_4542960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4543034 : List Nat := [3, 1, 1, 1, 3, 3, 2, 3, 1, 2, 3]
def baseStart_4543034 : Nat := 118140960795 + 4543034 * 2 ^ 59
def prefixEnd_4543034 : Nat := 4983230072969 + 3 ^ 40 * 4543034 * 2
def baseEnd_4543034 : Nat := 2332760071718083592281973

theorem tailTrace_4543034 : CollatzResearch.WordTrace tailWord_4543034 prefixEnd_4543034 2332760071718083592281973 := by
  unfold tailWord_4543034
  simp only [CollatzResearch.WordTrace]
  refine ⟨41424515655842795320169039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110465375082247454187117437 41424515655842795320169039)
  ·
    refine ⟨62136773483764192980253559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41424515655842795320169039 62136773483764192980253559)
    ·
      refine ⟨93205160225646289470380339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62136773483764192980253559 93205160225646289470380339)
      ·
        refine ⟨139807740338469434205570509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93205160225646289470380339 139807740338469434205570509)
        ·
          refine ⟨52427902626926037827088941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 139807740338469434205570509 52427902626926037827088941)
          ·
            refine ⟨19660463485097264185158353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52427902626926037827088941 19660463485097264185158353)
            ·
              refine ⟨14745347613822948138868765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19660463485097264185158353 14745347613822948138868765)
              ·
                refine ⟨5529505355183605552075787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14745347613822948138868765 5529505355183605552075787)
                ·
                  refine ⟨8294258032775408328113681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5529505355183605552075787 8294258032775408328113681)
                  ·
                    refine ⟨6220693524581556246085261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8294258032775408328113681 6220693524581556246085261)
                    ·
                      refine ⟨2332760071718083592281973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6220693524581556246085261 2332760071718083592281973)
                      ·
                        rfl

theorem cell23_4543034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 3, 1, 2, 3].length) (baseStart_4543034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4543034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4543034 prefixEnd_4543034 := by exact prefixLift 4543034
  have htrace : WordTrace (prefixWord ++ tailWord_4543034) baseStart_4543034 baseEnd_4543034 := by
    simpa [prefixWord, tailWord_4543034, baseEnd_4543034] using wordTrace_append hprefix tailTrace_4543034
  have hstable : (prefixWord ++ tailWord_4543034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4543034).length < 2 ^ (prefixWord ++ tailWord_4543034).sum := by decide
  have hdescent : baseEnd_4543034 < baseStart_4543034 := by decide
  rcases family_descends (prefixWord ++ tailWord_4543034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4543037 : List Nat := [1, 4, 1, 3, 2, 3, 9]
def baseStart_4543037 : Nat := 118140960795 + 4543037 * 2 ^ 59
def prefixEnd_4543037 : Nat := 4983230072969 + 3 ^ 40 * 4543037 * 2
def baseEnd_4543037 : Nat := 28799526076049963957339

theorem tailTrace_4543037 : CollatzResearch.WordTrace tailWord_4543037 prefixEnd_4543037 28799526076049963957339 := by
  unfold tailWord_4543037
  simp only [CollatzResearch.WordTrace]
  refine ⟨165698172042360312793035365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110465448028240208528690243 165698172042360312793035365)
  ·
    refine ⟨31068407257942558648694131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 165698172042360312793035365 31068407257942558648694131)
    ·
      refine ⟨46602610886913837973041197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31068407257942558648694131 46602610886913837973041197)
      ·
        refine ⟨17475979082592689239890449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46602610886913837973041197 17475979082592689239890449)
        ·
          refine ⟨13106984311944516929917837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17475979082592689239890449 13106984311944516929917837)
          ·
            refine ⟨4915119116979193848719189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13106984311944516929917837 4915119116979193848719189)
            ·
              refine ⟨28799526076049963957339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4915119116979193848719189 28799526076049963957339)
              ·
                rfl

theorem cell23_4543037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 9].length) (baseStart_4543037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4543037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4543037 prefixEnd_4543037 := by exact prefixLift 4543037
  have htrace : WordTrace (prefixWord ++ tailWord_4543037) baseStart_4543037 baseEnd_4543037 := by
    simpa [prefixWord, tailWord_4543037, baseEnd_4543037] using wordTrace_append hprefix tailTrace_4543037
  have hstable : (prefixWord ++ tailWord_4543037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4543037).length < 2 ^ (prefixWord ++ tailWord_4543037).sum := by decide
  have hdescent : baseEnd_4543037 < baseStart_4543037 := by decide
  rcases family_descends (prefixWord ++ tailWord_4543037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4543068 : List Nat := [2, 2, 4, 1, 3, 2, 1, 2, 1, 2, 3]
def baseStart_4543068 : Nat := 118140960795 + 4543068 * 2 ^ 59
def prefixEnd_4543068 : Nat := 4983230072969 + 3 ^ 40 * 4543068 * 2
def baseEnd_4543068 : Nat := 2332777530060336459256817

theorem tailTrace_4543068 : CollatzResearch.WordTrace tailWord_4543068 prefixEnd_4543068 2332777530060336459256817 := by
  unfold tailWord_4543068
  simp only [CollatzResearch.WordTrace]
  refine ⟨82849651352624002543706929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110466201803498670058275905 82849651352624002543706929)
  ·
    refine ⟨62137238514468001907780197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82849651352624002543706929 62137238514468001907780197)
    ·
      refine ⟨11650732221462750357708787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62137238514468001907780197 11650732221462750357708787)
      ·
        refine ⟨17476098332194125536563181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11650732221462750357708787 17476098332194125536563181)
        ·
          refine ⟨6553536874572797076211193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17476098332194125536563181 6553536874572797076211193)
          ·
            refine ⟨4915152655929597807158395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6553536874572797076211193 4915152655929597807158395)
            ·
              refine ⟨7372728983894396710737593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4915152655929597807158395 7372728983894396710737593)
              ·
                refine ⟨5529546737920797533053195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7372728983894396710737593 5529546737920797533053195)
                ·
                  refine ⟨8294320106881196299579793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5529546737920797533053195 8294320106881196299579793)
                  ·
                    refine ⟨6220740080160897224684845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8294320106881196299579793 6220740080160897224684845)
                    ·
                      refine ⟨2332777530060336459256817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6220740080160897224684845 2332777530060336459256817)
                      ·
                        rfl

theorem cell23_4543068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_4543068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4543068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4543068 prefixEnd_4543068 := by exact prefixLift 4543068
  have htrace : WordTrace (prefixWord ++ tailWord_4543068) baseStart_4543068 baseEnd_4543068 := by
    simpa [prefixWord, tailWord_4543068, baseEnd_4543068] using wordTrace_append hprefix tailTrace_4543068
  have hstable : (prefixWord ++ tailWord_4543068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4543068).length < 2 ^ (prefixWord ++ tailWord_4543068).sum := by decide
  have hdescent : baseEnd_4543068 < baseStart_4543068 := by decide
  rcases family_descends (prefixWord ++ tailWord_4543068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4543107 : List Nat := [1, 1, 1, 3, 3, 1, 3, 1, 2, 4, 3]
def baseStart_4543107 : Nat := 118140960795 + 4543107 * 2 ^ 59
def prefixEnd_4543107 : Nat := 4983230072969 + 3 ^ 40 * 4543107 * 2
def baseEnd_4543107 : Nat := 2332797555805861806669137

theorem tailTrace_4543107 : CollatzResearch.WordTrace tailWord_4543107 prefixEnd_4543107 2332797555805861806669137 := by
  unfold tailWord_4543107
  simp only [CollatzResearch.WordTrace]
  refine ⟨165700725152106714748083575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110467150101404476498722383 165700725152106714748083575)
  ·
    refine ⟨248551087728160072122125363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165700725152106714748083575 248551087728160072122125363)
    ·
      refine ⟨372826631592240108183188045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248551087728160072122125363 372826631592240108183188045)
      ·
        refine ⟨139809986847090040568695517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 372826631592240108183188045 139809986847090040568695517)
        ·
          refine ⟨52428745067658765213260819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 139809986847090040568695517 52428745067658765213260819)
          ·
            refine ⟨78643117601488147819891229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52428745067658765213260819 78643117601488147819891229)
            ·
              refine ⟨29491169100558055432459211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78643117601488147819891229 29491169100558055432459211)
              ·
                refine ⟨44236753650837083148688817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29491169100558055432459211 44236753650837083148688817)
                ·
                  refine ⟨33177565238127812361516613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44236753650837083148688817 33177565238127812361516613)
                  ·
                    refine ⟨6220793482148964817784365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33177565238127812361516613 6220793482148964817784365)
                    ·
                      refine ⟨2332797555805861806669137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6220793482148964817784365 2332797555805861806669137)
                      ·
                        rfl

theorem cell23_4543107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 2, 4, 3].length) (baseStart_4543107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4543107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4543107 prefixEnd_4543107 := by exact prefixLift 4543107
  have htrace : WordTrace (prefixWord ++ tailWord_4543107) baseStart_4543107 baseEnd_4543107 := by
    simpa [prefixWord, tailWord_4543107, baseEnd_4543107] using wordTrace_append hprefix tailTrace_4543107
  have hstable : (prefixWord ++ tailWord_4543107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4543107).length < 2 ^ (prefixWord ++ tailWord_4543107).sum := by decide
  have hdescent : baseEnd_4543107 < baseStart_4543107 := by decide
  rcases family_descends (prefixWord ++ tailWord_4543107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4543114 : List Nat := [3, 1, 2, 3, 3, 1, 1, 1, 2, 6]
def baseStart_4543114 : Nat := 118140960795 + 4543114 * 2 ^ 59
def prefixEnd_4543114 : Nat := 4983230072969 + 3 ^ 40 * 4543114 * 2
def baseEnd_4543114 : Nat := 777600383390147759760535

theorem tailTrace_4543114 : CollatzResearch.WordTrace tailWord_4543114 prefixEnd_4543114 777600383390147759760535 := by
  unfold tailWord_4543114
  simp only [CollatzResearch.WordTrace]
  refine ⟨41425245115770338735897099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110467320308720903295725597 41425245115770338735897099)
  ·
    refine ⟨62137867673655508103845649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41425245115770338735897099 62137867673655508103845649)
    ·
      refine ⟨46603400755241631077884237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62137867673655508103845649 46603400755241631077884237)
      ·
        refine ⟨17476275283215611654206589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46603400755241631077884237 17476275283215611654206589)
        ·
          refine ⟨6553603231205854370327471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17476275283215611654206589 6553603231205854370327471)
          ·
            refine ⟨9830404846808781555491207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6553603231205854370327471 9830404846808781555491207)
            ·
              refine ⟨14745607270213172333236811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9830404846808781555491207 14745607270213172333236811)
              ·
                refine ⟨22118410905319758499855217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14745607270213172333236811 22118410905319758499855217)
                ·
                  refine ⟨16588808178989818874891413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22118410905319758499855217 16588808178989818874891413)
                  ·
                    refine ⟨777600383390147759760535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16588808178989818874891413 777600383390147759760535)
                    ·
                      rfl

theorem cell23_4543114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 1, 2, 6].length) (baseStart_4543114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4543114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4543114 prefixEnd_4543114 := by exact prefixLift 4543114
  have htrace : WordTrace (prefixWord ++ tailWord_4543114) baseStart_4543114 baseEnd_4543114 := by
    simpa [prefixWord, tailWord_4543114, baseEnd_4543114] using wordTrace_append hprefix tailTrace_4543114
  have hstable : (prefixWord ++ tailWord_4543114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4543114).length < 2 ^ (prefixWord ++ tailWord_4543114).sum := by decide
  have hdescent : baseEnd_4543114 < baseStart_4543114 := by decide
  rcases family_descends (prefixWord ++ tailWord_4543114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4543127 : List Nat := [1, 1, 3, 3, 2, 1, 3, 2, 7]
def baseStart_4543127 : Nat := 118140960795 + 4543127 * 2 ^ 59
def prefixEnd_4543127 : Nat := 4983230072969 + 3 ^ 40 * 4543127 * 2
def baseEnd_4543127 : Nat := 259200869490994636491005

theorem tailTrace_4543127 : CollatzResearch.WordTrace tailWord_4543127 prefixEnd_4543127 259200869490994636491005 := by
  unfold tailWord_4543127
  simp only [CollatzResearch.WordTrace]
  refine ⟨165701454612034258163811635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110467636408022838775874423 165701454612034258163811635)
  ·
    refine ⟨248552181918051387245717453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165701454612034258163811635 248552181918051387245717453)
    ·
      refine ⟨93207068219269270217144045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 248552181918051387245717453 93207068219269270217144045)
      ·
        refine ⟨34952650582225976331429017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93207068219269270217144045 34952650582225976331429017)
        ·
          refine ⟨26214487936669482248571763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34952650582225976331429017 26214487936669482248571763)
          ·
            refine ⟨39321731905004223372857645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26214487936669482248571763 39321731905004223372857645)
            ·
              refine ⟨14745649464376583764821617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39321731905004223372857645 14745649464376583764821617)
              ·
                refine ⟨11059237098282437823616213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14745649464376583764821617 11059237098282437823616213)
                ·
                  refine ⟨259200869490994636491005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11059237098282437823616213 259200869490994636491005)
                  ·
                    rfl

theorem cell23_4543127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 2, 7].length) (baseStart_4543127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4543127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4543127 prefixEnd_4543127 := by exact prefixLift 4543127
  have htrace : WordTrace (prefixWord ++ tailWord_4543127) baseStart_4543127 baseEnd_4543127 := by
    simpa [prefixWord, tailWord_4543127, baseEnd_4543127] using wordTrace_append hprefix tailTrace_4543127
  have hstable : (prefixWord ++ tailWord_4543127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4543127).length < 2 ^ (prefixWord ++ tailWord_4543127).sum := by decide
  have hdescent : baseEnd_4543127 < baseStart_4543127 := by decide
  rcases family_descends (prefixWord ++ tailWord_4543127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4543134 : List Nat := [4, 3, 1, 1, 1, 1, 1, 2, 1, 4, 4]
def baseStart_4543134 : Nat := 118140960795 + 4543134 * 2 ^ 59
def prefixEnd_4543134 : Nat := 4983230072969 + 3 ^ 40 * 4543134 * 2
def baseEnd_4543134 : Nat := 2332811419783533201031513

theorem tailTrace_4543134 : CollatzResearch.WordTrace tailWord_4543134 prefixEnd_4543134 2332811419783533201031513 := by
  unfold tailWord_4543134
  simp only [CollatzResearch.WordTrace]
  refine ⟨20712713740376112294914557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110467806615339265572877637 20712713740376112294914557)
  ·
    refine ⟨7767267652641042110592959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20712713740376112294914557 7767267652641042110592959)
    ·
      refine ⟨11650901478961563165889439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7767267652641042110592959 11650901478961563165889439)
      ·
        refine ⟨17476352218442344748834159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11650901478961563165889439 17476352218442344748834159)
        ·
          refine ⟨26214528327663517123251239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17476352218442344748834159 26214528327663517123251239)
          ·
            refine ⟨39321792491495275684876859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26214528327663517123251239 39321792491495275684876859)
            ·
              refine ⟨58982688737242913527315289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39321792491495275684876859 58982688737242913527315289)
              ·
                refine ⟨44237016552932185145486467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58982688737242913527315289 44237016552932185145486467)
                ·
                  refine ⟨66355524829398277718229701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44237016552932185145486467 66355524829398277718229701)
                  ·
                    refine ⟨12441660905512177072168069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 66355524829398277718229701 12441660905512177072168069)
                    ·
                      refine ⟨2332811419783533201031513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12441660905512177072168069 2332811419783533201031513)
                      ·
                        rfl

theorem cell23_4543134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_4543134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4543134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4543134 prefixEnd_4543134 := by exact prefixLift 4543134
  have htrace : WordTrace (prefixWord ++ tailWord_4543134) baseStart_4543134 baseEnd_4543134 := by
    simpa [prefixWord, tailWord_4543134, baseEnd_4543134] using wordTrace_append hprefix tailTrace_4543134
  have hstable : (prefixWord ++ tailWord_4543134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4543134).length < 2 ^ (prefixWord ++ tailWord_4543134).sum := by decide
  have hdescent : baseEnd_4543134 < baseStart_4543134 := by decide
  rcases family_descends (prefixWord ++ tailWord_4543134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4543194 : List Nat := [3, 1, 1, 2, 2, 2, 2, 3, 2, 1, 4]
def baseStart_4543194 : Nat := 118140960795 + 4543194 * 2 ^ 59
def prefixEnd_4543194 : Nat := 4983230072969 + 3 ^ 40 * 4543194 * 2
def baseEnd_4543194 : Nat := 2332842228622802966281237

theorem tailTrace_4543194 : CollatzResearch.WordTrace tailWord_4543194 prefixEnd_4543194 2332842228622802966281237 := by
  unfold tailWord_4543194
  simp only [CollatzResearch.WordTrace]
  refine ⟨41425974575697882151625159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110469265535194352404333757 41425974575697882151625159)
  ·
    refine ⟨62138961863546823227437739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41425974575697882151625159 62138961863546823227437739)
    ·
      refine ⟨93208442795320234841156609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62138961863546823227437739 93208442795320234841156609)
      ·
        refine ⟨69906332096490176130867457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93208442795320234841156609 69906332096490176130867457)
        ·
          refine ⟨52429749072367632098150593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69906332096490176130867457 52429749072367632098150593)
          ·
            refine ⟨39322311804275724073612945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52429749072367632098150593 39322311804275724073612945)
            ·
              refine ⟨29491733853206793055209709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39322311804275724073612945 29491733853206793055209709)
              ·
                refine ⟨11059400194952547395703641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29491733853206793055209709 11059400194952547395703641)
                ·
                  refine ⟨8294550146214410546777731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11059400194952547395703641 8294550146214410546777731)
                  ·
                    refine ⟨12441825219321615820166597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8294550146214410546777731 12441825219321615820166597)
                    ·
                      refine ⟨2332842228622802966281237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12441825219321615820166597 2332842228622802966281237)
                      ·
                        rfl

theorem cell23_4543194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 3, 2, 1, 4].length) (baseStart_4543194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4543194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4543194 prefixEnd_4543194 := by exact prefixLift 4543194
  have htrace : WordTrace (prefixWord ++ tailWord_4543194) baseStart_4543194 baseEnd_4543194 := by
    simpa [prefixWord, tailWord_4543194, baseEnd_4543194] using wordTrace_append hprefix tailTrace_4543194
  have hstable : (prefixWord ++ tailWord_4543194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4543194).length < 2 ^ (prefixWord ++ tailWord_4543194).sum := by decide
  have hdescent : baseEnd_4543194 < baseStart_4543194 := by decide
  rcases family_descends (prefixWord ++ tailWord_4543194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4543217 : List Nat := [1, 2, 2, 2, 2, 2, 1, 3, 8]
def baseStart_4543217 : Nat := 118140960795 + 4543217 * 2 ^ 59
def prefixEnd_4543217 : Nat := 4983230072969 + 3 ^ 40 * 4543217 * 2
def baseEnd_4543217 : Nat := 259206004297539597365959

theorem tailTrace_4543217 : CollatzResearch.WordTrace tailWord_4543217 prefixEnd_4543217 259206004297539597365959 := by
  unfold tailWord_4543217
  simp only [CollatzResearch.WordTrace]
  refine ⟨165704737181708203534587905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110469824787805469023058603 165704737181708203534587905)
  ·
    refine ⟨124278552886281152650940929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165704737181708203534587905 124278552886281152650940929)
    ·
      refine ⟨93208914664710864488205697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124278552886281152650940929 93208914664710864488205697)
      ·
        refine ⟨69906685998533148366154273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93208914664710864488205697 69906685998533148366154273)
        ·
          refine ⟨52430014498899861274615705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69906685998533148366154273 52430014498899861274615705)
          ·
            refine ⟨39322510874174895955961779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52430014498899861274615705 39322510874174895955961779)
            ·
              refine ⟨58983766311262343933942669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39322510874174895955961779 58983766311262343933942669)
              ·
                refine ⟨22118912366723378975228501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58983766311262343933942669 22118912366723378975228501)
                ·
                  refine ⟨259206004297539597365959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22118912366723378975228501 259206004297539597365959)
                  ·
                    rfl

theorem cell23_4543217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 3, 8].length) (baseStart_4543217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4543217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4543217 prefixEnd_4543217 := by exact prefixLift 4543217
  have htrace : WordTrace (prefixWord ++ tailWord_4543217) baseStart_4543217 baseEnd_4543217 := by
    simpa [prefixWord, tailWord_4543217, baseEnd_4543217] using wordTrace_append hprefix tailTrace_4543217
  have hstable : (prefixWord ++ tailWord_4543217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4543217).length < 2 ^ (prefixWord ++ tailWord_4543217).sum := by decide
  have hdescent : baseEnd_4543217 < baseStart_4543217 := by decide
  rcases family_descends (prefixWord ++ tailWord_4543217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4543237 : List Nat := [1, 3, 1, 1, 2, 1, 1, 4, 1, 2, 6]
def baseStart_4543237 : Nat := 118140960795 + 4543237 * 2 ^ 59
def prefixEnd_4543237 : Nat := 4983230072969 + 3 ^ 40 * 4543237 * 2
def baseEnd_4543237 : Nat := 2332864308290946298043539

theorem tailTrace_4543237 : CollatzResearch.WordTrace tailWord_4543237 prefixEnd_4543237 2332864308290946298043539 := by
  unfold tailWord_4543237
  simp only [CollatzResearch.WordTrace]
  refine ⟨165705466641635746950315965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110470311094423831300210643 165705466641635746950315965)
  ·
    refine ⟨62139549990613405106368487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165705466641635746950315965 62139549990613405106368487)
    ·
      refine ⟨93209324985920107659552731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62139549990613405106368487 93209324985920107659552731)
      ·
        refine ⟨139813987478880161489329097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93209324985920107659552731 139813987478880161489329097)
        ·
          refine ⟨104860490609160121116996823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139813987478880161489329097 104860490609160121116996823)
          ·
            refine ⟨157290735913740181675495235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104860490609160121116996823 157290735913740181675495235)
            ·
              refine ⟨235936103870610272513242853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157290735913740181675495235 235936103870610272513242853)
              ·
                refine ⟨44238019475739426096233035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 235936103870610272513242853 44238019475739426096233035)
                ·
                  refine ⟨66357029213609139144349553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44238019475739426096233035 66357029213609139144349553)
                  ·
                    refine ⟨49767771910206854358262165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 66357029213609139144349553 49767771910206854358262165)
                    ·
                      refine ⟨2332864308290946298043539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49767771910206854358262165 2332864308290946298043539)
                      ·
                        rfl

theorem cell23_4543237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 2, 6].length) (baseStart_4543237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4543237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4543237 prefixEnd_4543237 := by exact prefixLift 4543237
  have htrace : WordTrace (prefixWord ++ tailWord_4543237) baseStart_4543237 baseEnd_4543237 := by
    simpa [prefixWord, tailWord_4543237, baseEnd_4543237] using wordTrace_append hprefix tailTrace_4543237
  have hstable : (prefixWord ++ tailWord_4543237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4543237).length < 2 ^ (prefixWord ++ tailWord_4543237).sum := by decide
  have hdescent : baseEnd_4543237 < baseStart_4543237 := by decide
  rcases family_descends (prefixWord ++ tailWord_4543237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4543257 : List Nat := [1, 2, 1, 2, 1, 1, 1, 3, 2, 4, 5]
def baseStart_4543257 : Nat := 118140960795 + 4543257 * 2 ^ 59
def prefixEnd_4543257 : Nat := 4983230072969 + 3 ^ 40 * 4543257 * 2
def baseEnd_4543257 : Nat := 2332874577904036219793447

theorem tailTrace_4543257 : CollatzResearch.WordTrace tailWord_4543257 prefixEnd_4543257 2332874577904036219793447 := by
  unfold tailWord_4543257
  simp only [CollatzResearch.WordTrace]
  refine ⟨165706196101563290366044025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110470797401042193577362683 165706196101563290366044025)
  ·
    refine ⟨124279647076172467774533019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165706196101563290366044025 124279647076172467774533019)
    ·
      refine ⟨186419470614258701661799529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124279647076172467774533019 186419470614258701661799529)
      ·
        refine ⟨139814602960694026246349647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186419470614258701661799529 139814602960694026246349647)
        ·
          refine ⟨209721904441041039369524471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139814602960694026246349647 209721904441041039369524471)
          ·
            refine ⟨314582856661561559054286707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 209721904441041039369524471 314582856661561559054286707)
            ·
              refine ⟨471874284992342338581430061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 314582856661561559054286707 471874284992342338581430061)
              ·
                refine ⟨176952856872128376968036273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 471874284992342338581430061 176952856872128376968036273)
                ·
                  refine ⟨132714642654096282726027205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 176952856872128376968036273 132714642654096282726027205)
                  ·
                    refine ⟨24883995497643053011130101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 132714642654096282726027205 24883995497643053011130101)
                    ·
                      refine ⟨2332874577904036219793447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24883995497643053011130101 2332874577904036219793447)
                      ·
                        rfl

theorem cell23_4543257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 4, 5].length) (baseStart_4543257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4543257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4543257 prefixEnd_4543257 := by exact prefixLift 4543257
  have htrace : WordTrace (prefixWord ++ tailWord_4543257) baseStart_4543257 baseEnd_4543257 := by
    simpa [prefixWord, tailWord_4543257, baseEnd_4543257] using wordTrace_append hprefix tailTrace_4543257
  have hstable : (prefixWord ++ tailWord_4543257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4543257).length < 2 ^ (prefixWord ++ tailWord_4543257).sum := by decide
  have hdescent : baseEnd_4543257 < baseStart_4543257 := by decide
  rcases family_descends (prefixWord ++ tailWord_4543257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4543335 : List Nat := [1, 1, 5, 1, 2, 3, 2, 1, 3, 2, 2]
def baseStart_4543335 : Nat := 118140960795 + 4543335 * 2 ^ 59
def prefixEnd_4543335 : Nat := 4983230072969 + 3 ^ 40 * 4543335 * 2
def baseEnd_4543335 : Nat := 2332914629395086914618089

theorem tailTrace_4543335 : CollatzResearch.WordTrace tailWord_4543335 prefixEnd_4543335 2332914629395086914618089 := by
  unfold tailWord_4543335
  simp only [CollatzResearch.WordTrace]
  refine ⟨165709040995280709687383459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110472693996853806458255639 165709040995280709687383459)
  ·
    refine ⟨248563561492921064531075189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165709040995280709687383459 248563561492921064531075189)
    ·
      refine ⟨23302833889961349799788299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 248563561492921064531075189 23302833889961349799788299)
      ·
        refine ⟨34954250834942024699682449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23302833889961349799788299 34954250834942024699682449)
        ·
          refine ⟨26215688126206518524761837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34954250834942024699682449 26215688126206518524761837)
          ·
            refine ⟨9830883047327444446785689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26215688126206518524761837 9830883047327444446785689)
            ·
              refine ⟨7373162285495583335089267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9830883047327444446785689 7373162285495583335089267)
              ·
                refine ⟨11059743428243375002633901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7373162285495583335089267 11059743428243375002633901)
                ·
                  refine ⟨4147403785591265625987713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11059743428243375002633901 4147403785591265625987713)
                  ·
                    refine ⟨3110552839193449219490785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4147403785591265625987713 3110552839193449219490785)
                    ·
                      refine ⟨2332914629395086914618089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3110552839193449219490785 2332914629395086914618089)
                      ·
                        rfl

theorem cell23_4543335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 1, 3, 2, 2].length) (baseStart_4543335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4543335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4543335 prefixEnd_4543335 := by exact prefixLift 4543335
  have htrace : WordTrace (prefixWord ++ tailWord_4543335) baseStart_4543335 baseEnd_4543335 := by
    simpa [prefixWord, tailWord_4543335, baseEnd_4543335] using wordTrace_append hprefix tailTrace_4543335
  have hstable : (prefixWord ++ tailWord_4543335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4543335).length < 2 ^ (prefixWord ++ tailWord_4543335).sum := by decide
  have hdescent : baseEnd_4543335 < baseStart_4543335 := by decide
  rcases family_descends (prefixWord ++ tailWord_4543335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4543358 : List Nat := [4, 2, 3, 1, 2, 1, 1, 9]
def baseStart_4543358 : Nat := 118140960795 + 4543358 * 2 ^ 59
def prefixEnd_4543358 : Nat := 4983230072969 + 3 ^ 40 * 4543358 * 2
def baseEnd_4543358 : Nat := 86404682942597789801129

theorem tailTrace_4543358 : CollatzResearch.WordTrace tailWord_4543358 prefixEnd_4543358 86404682942597789801129 := by
  unfold tailWord_4543358
  simp only [CollatzResearch.WordTrace]
  refine ⟨20713734984274673076933841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110473253249464923076980485 20713734984274673076933841)
  ·
    refine ⟨15535301238206004807700381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20713734984274673076933841 15535301238206004807700381)
    ·
      refine ⟨5825737964327251802887643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15535301238206004807700381 5825737964327251802887643)
      ·
        refine ⟨8738606946490877704331465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5825737964327251802887643 8738606946490877704331465)
        ·
          refine ⟨6553955209868158278248599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8738606946490877704331465 6553955209868158278248599)
          ·
            refine ⟨9830932814802237417372899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6553955209868158278248599 9830932814802237417372899)
            ·
              refine ⟨14746399222203356126059349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9830932814802237417372899 14746399222203356126059349)
              ·
                refine ⟨86404682942597789801129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14746399222203356126059349 86404682942597789801129)
                ·
                  rfl

theorem cell23_4543358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 9].length) (baseStart_4543358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4543358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4543358 prefixEnd_4543358 := by exact prefixLift 4543358
  have htrace : WordTrace (prefixWord ++ tailWord_4543358) baseStart_4543358 baseEnd_4543358 := by
    simpa [prefixWord, tailWord_4543358, baseEnd_4543358] using wordTrace_append hprefix tailTrace_4543358
  have hstable : (prefixWord ++ tailWord_4543358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4543358).length < 2 ^ (prefixWord ++ tailWord_4543358).sum := by decide
  have hdescent : baseEnd_4543358 < baseStart_4543358 := by decide
  rcases family_descends (prefixWord ++ tailWord_4543358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4543368 : List Nat := [2, 1, 3, 3, 2, 1, 1, 2, 4, 1, 3]
def baseStart_4543368 : Nat := 118140960795 + 4543368 * 2 ^ 59
def prefixEnd_4543368 : Nat := 4983230072969 + 3 ^ 40 * 4543368 * 2
def baseEnd_4543368 : Nat := 2332931574256685285505437

theorem tailTrace_4543368 : CollatzResearch.WordTrace tailWord_4543368 prefixEnd_4543368 2332931574256685285505437 := by
  unfold tailWord_4543368
  simp only [CollatzResearch.WordTrace]
  refine ⟨82855122302080578161667379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110473496402774104215556505 82855122302080578161667379)
  ·
    refine ⟨124282683453120867242501069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82855122302080578161667379 124282683453120867242501069)
    ·
      refine ⟨46606006294920325215937901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124282683453120867242501069 46606006294920325215937901)
      ·
        refine ⟨17477252360595121955976713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46606006294920325215937901 17477252360595121955976713)
        ·
          refine ⟨13107939270446341466982535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17477252360595121955976713 13107939270446341466982535)
          ·
            refine ⟨19661908905669512200473803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13107939270446341466982535 19661908905669512200473803)
            ·
              refine ⟨29492863358504268300710705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19661908905669512200473803 29492863358504268300710705)
              ·
                refine ⟨22119647518878201225533029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29492863358504268300710705 22119647518878201225533029)
                ·
                  refine ⟨4147433909789662729787443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22119647518878201225533029 4147433909789662729787443)
                  ·
                    refine ⟨6221150864684494094681165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4147433909789662729787443 6221150864684494094681165)
                    ·
                      refine ⟨2332931574256685285505437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6221150864684494094681165 2332931574256685285505437)
                      ·
                        rfl

theorem cell23_4543368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_4543368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4543368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4543368 prefixEnd_4543368 := by exact prefixLift 4543368
  have htrace : WordTrace (prefixWord ++ tailWord_4543368) baseStart_4543368 baseEnd_4543368 := by
    simpa [prefixWord, tailWord_4543368, baseEnd_4543368] using wordTrace_append hprefix tailTrace_4543368
  have hstable : (prefixWord ++ tailWord_4543368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4543368).length < 2 ^ (prefixWord ++ tailWord_4543368).sum := by decide
  have hdescent : baseEnd_4543368 < baseStart_4543368 := by decide
  rcases family_descends (prefixWord ++ tailWord_4543368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4543412 : List Nat := [2, 5, 2, 1, 1, 2, 1, 1, 3, 3, 2]
def baseStart_4543412 : Nat := 118140960795 + 4543412 * 2 ^ 59
def prefixEnd_4543412 : Nat := 4983230072969 + 3 ^ 40 * 4543412 * 2
def baseEnd_4543412 : Nat := 2332954167405483113355235

theorem tailTrace_4543412 : CollatzResearch.WordTrace tailWord_4543412 prefixEnd_4543412 2332954167405483113355235 := by
  unfold tailWord_4543412
  simp only [CollatzResearch.WordTrace]
  refine ⟨82855924708000875918968245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110474566277334501225290993 82855924708000875918968245)
  ·
    refine ⟨7767742941375082117403273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 82855924708000875918968245 7767742941375082117403273)
    ·
      refine ⟨5825807206031311588052455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7767742941375082117403273 5825807206031311588052455)
      ·
        refine ⟨8738710809046967382078683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5825807206031311588052455 8738710809046967382078683)
        ·
          refine ⟨13108066213570451073118025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8738710809046967382078683 13108066213570451073118025)
          ·
            refine ⟨9831049660177838304838519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13108066213570451073118025 9831049660177838304838519)
            ·
              refine ⟨14746574490266757457257779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9831049660177838304838519 14746574490266757457257779)
              ·
                refine ⟨22119861735400136185886669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14746574490266757457257779 22119861735400136185886669)
                ·
                  refine ⟨8294948150775051069707501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22119861735400136185886669 8294948150775051069707501)
                  ·
                    refine ⟨3110605556540644151140313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8294948150775051069707501 3110605556540644151140313)
                    ·
                      refine ⟨2332954167405483113355235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3110605556540644151140313 2332954167405483113355235)
                      ·
                        rfl

theorem cell23_4543412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_4543412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4543412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4543412 prefixEnd_4543412 := by exact prefixLift 4543412
  have htrace : WordTrace (prefixWord ++ tailWord_4543412) baseStart_4543412 baseEnd_4543412 := by
    simpa [prefixWord, tailWord_4543412, baseEnd_4543412] using wordTrace_append hprefix tailTrace_4543412
  have hstable : (prefixWord ++ tailWord_4543412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4543412).length < 2 ^ (prefixWord ++ tailWord_4543412).sum := by decide
  have hdescent : baseEnd_4543412 < baseStart_4543412 := by decide
  rcases family_descends (prefixWord ++ tailWord_4543412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4543437 : List Nat := [1, 6, 3, 1, 2, 1, 2, 2, 1, 2, 2]
def baseStart_4543437 : Nat := 118140960795 + 4543437 * 2 ^ 59
def prefixEnd_4543437 : Nat := 4983230072969 + 3 ^ 40 * 4543437 * 2
def baseEnd_4543437 : Nat := 2332967004421845515542621

theorem tailTrace_4543437 : CollatzResearch.WordTrace tailWord_4543437 prefixEnd_4543437 2332967004421845515542621 := by
  unfold tailWord_4543437
  simp only [CollatzResearch.WordTrace]
  refine ⟨165712761240911181107596565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110475174160607454071731043 165712761240911181107596565)
  ·
    refine ⟨7767785683167711614418589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 165712761240911181107596565 7767785683167711614418589)
    ·
      refine ⟨2912919631187891855406971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7767785683167711614418589 2912919631187891855406971)
      ·
        refine ⟨4369379446781837783110457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2912919631187891855406971 4369379446781837783110457)
        ·
          refine ⟨3277034585086378337332843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4369379446781837783110457 3277034585086378337332843)
          ·
            refine ⟨4915551877629567505999265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3277034585086378337332843 4915551877629567505999265)
            ·
              refine ⟨3686663908222175629499449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4915551877629567505999265 3686663908222175629499449)
              ·
                refine ⟨2764997931166631722124587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3686663908222175629499449 2764997931166631722124587)
                ·
                  refine ⟨4147496896749947583186881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2764997931166631722124587 4147496896749947583186881)
                  ·
                    refine ⟨3110622672562460687390161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4147496896749947583186881 3110622672562460687390161)
                    ·
                      refine ⟨2332967004421845515542621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3110622672562460687390161 2332967004421845515542621)
                      ·
                        rfl

theorem cell23_4543437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_4543437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4543437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4543437 prefixEnd_4543437 := by exact prefixLift 4543437
  have htrace : WordTrace (prefixWord ++ tailWord_4543437) baseStart_4543437 baseEnd_4543437 := by
    simpa [prefixWord, tailWord_4543437, baseEnd_4543437] using wordTrace_append hprefix tailTrace_4543437
  have hstable : (prefixWord ++ tailWord_4543437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4543437).length < 2 ^ (prefixWord ++ tailWord_4543437).sum := by decide
  have hdescent : baseEnd_4543437 < baseStart_4543437 := by decide
  rcases family_descends (prefixWord ++ tailWord_4543437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4543441 : List Nat := [1, 2, 2, 1, 2, 1, 4, 2, 2, 3, 3]
def baseStart_4543441 : Nat := 118140960795 + 4543441 * 2 ^ 59
def prefixEnd_4543441 : Nat := 4983230072969 + 3 ^ 40 * 4543441 * 2
def baseEnd_4543441 : Nat := 2332969058344463499892601

theorem tailTrace_4543441 : CollatzResearch.WordTrace tailWord_4543441 prefixEnd_4543441 2332969058344463499892601 := by
  unfold tailWord_4543441
  simp only [CollatzResearch.WordTrace]
  refine ⟨165712907132896689790742177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110475271421931126527161451 165712907132896689790742177)
  ·
    refine ⟨124284680349672517343056633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165712907132896689790742177 124284680349672517343056633)
    ·
      refine ⟨93213510262254388007292475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124284680349672517343056633 93213510262254388007292475)
      ·
        refine ⟨139820265393381582010938713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93213510262254388007292475 139820265393381582010938713)
        ·
          refine ⟨104865199045036186508204035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139820265393381582010938713 104865199045036186508204035)
          ·
            refine ⟨157297798567554279762306053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104865199045036186508204035 157297798567554279762306053)
            ·
              refine ⟨29493337231416427455432385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 157297798567554279762306053 29493337231416427455432385)
              ·
                refine ⟨22120002923562320591574289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29493337231416427455432385 22120002923562320591574289)
                ·
                  refine ⟨16590002192671740443680717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22120002923562320591574289 16590002192671740443680717)
                  ·
                    refine ⟨6221250822251902666380269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16590002192671740443680717 6221250822251902666380269)
                    ·
                      refine ⟨2332969058344463499892601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6221250822251902666380269 2332969058344463499892601)
                      ·
                        rfl

theorem cell23_4543441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 2, 2, 3, 3].length) (baseStart_4543441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4543441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4543441 prefixEnd_4543441 := by exact prefixLift 4543441
  have htrace : WordTrace (prefixWord ++ tailWord_4543441) baseStart_4543441 baseEnd_4543441 := by
    simpa [prefixWord, tailWord_4543441, baseEnd_4543441] using wordTrace_append hprefix tailTrace_4543441
  have hstable : (prefixWord ++ tailWord_4543441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4543441).length < 2 ^ (prefixWord ++ tailWord_4543441).sum := by decide
  have hdescent : baseEnd_4543441 < baseStart_4543441 := by decide
  rcases family_descends (prefixWord ++ tailWord_4543441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4543442 : List Nat := [3, 2, 2, 3, 1, 1, 1, 4, 2, 2, 2]
def baseStart_4543442 : Nat := 118140960795 + 4543442 * 2 ^ 59
def prefixEnd_4543442 : Nat := 4983230072969 + 3 ^ 40 * 4543442 * 2
def baseEnd_4543442 : Nat := 2332969571825117995980097

theorem tailTrace_4543442 : CollatzResearch.WordTrace tailWord_4543442 prefixEnd_4543442 2332969571825117995980097 := by
  unfold tailWord_4543442
  simp only [CollatzResearch.WordTrace]
  refine ⟨41428235901473266740382145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110475295737262044641019053 41428235901473266740382145)
  ·
    refine ⟨31071176926104950055286609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41428235901473266740382145 31071176926104950055286609)
    ·
      refine ⟨23303382694578712541464957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31071176926104950055286609 23303382694578712541464957)
      ·
        refine ⟨8738768510467017203049359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23303382694578712541464957 8738768510467017203049359)
        ·
          refine ⟨13108152765700525804574039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8738768510467017203049359 13108152765700525804574039)
          ·
            refine ⟨19662229148550788706861059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13108152765700525804574039 19662229148550788706861059)
            ·
              refine ⟨29493343722826183060291589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19662229148550788706861059 29493343722826183060291589)
              ·
                refine ⟨5530001948029909323804673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29493343722826183060291589 5530001948029909323804673)
                ·
                  refine ⟨4147501461022431992853505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5530001948029909323804673 4147501461022431992853505)
                  ·
                    refine ⟨3110626095766823994640129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4147501461022431992853505 3110626095766823994640129)
                    ·
                      refine ⟨2332969571825117995980097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3110626095766823994640129 2332969571825117995980097)
                      ·
                        rfl

theorem cell23_4543442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_4543442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4543442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4543442 prefixEnd_4543442 := by exact prefixLift 4543442
  have htrace : WordTrace (prefixWord ++ tailWord_4543442) baseStart_4543442 baseEnd_4543442 := by
    simpa [prefixWord, tailWord_4543442, baseEnd_4543442] using wordTrace_append hprefix tailTrace_4543442
  have hstable : (prefixWord ++ tailWord_4543442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4543442).length < 2 ^ (prefixWord ++ tailWord_4543442).sum := by decide
  have hdescent : baseEnd_4543442 < baseStart_4543442 := by decide
  rcases family_descends (prefixWord ++ tailWord_4543442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4543448 : List Nat := [2, 1, 2, 2, 2, 4, 1, 4, 5]
def baseStart_4543448 : Nat := 118140960795 + 4543448 * 2 ^ 59
def prefixEnd_4543448 : Nat := 4983230072969 + 3 ^ 40 * 4543448 * 2
def baseEnd_4543448 : Nat := 259219183634338330278341

theorem tailTrace_4543448 : CollatzResearch.WordTrace tailWord_4543448 prefixEnd_4543448 259219183634338330278341 := by
  unfold tailWord_4543448
  simp only [CollatzResearch.WordTrace]
  refine ⟨82856581221935664993123499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110475441629247553324164665 82856581221935664993123499)
  ·
    refine ⟨124284871832903497489685249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82856581221935664993123499 124284871832903497489685249)
    ·
      refine ⟨93213653874677623117263937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124284871832903497489685249 93213653874677623117263937)
      ·
        refine ⟨69910240406008217337947953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93213653874677623117263937 69910240406008217337947953)
        ·
          refine ⟨52432680304506163003460965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69910240406008217337947953 52432680304506163003460965)
          ·
            refine ⟨9831127557094905563148931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52432680304506163003460965 9831127557094905563148931)
            ·
              refine ⟨14746691335642358344723397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9831127557094905563148931 14746691335642358344723397)
              ·
                refine ⟨2765004625432942189635637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14746691335642358344723397 2765004625432942189635637)
                ·
                  refine ⟨259219183634338330278341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2765004625432942189635637 259219183634338330278341)
                  ·
                    rfl

theorem cell23_4543448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 4, 5].length) (baseStart_4543448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4543448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4543448 prefixEnd_4543448 := by exact prefixLift 4543448
  have htrace : WordTrace (prefixWord ++ tailWord_4543448) baseStart_4543448 baseEnd_4543448 := by
    simpa [prefixWord, tailWord_4543448, baseEnd_4543448] using wordTrace_append hprefix tailTrace_4543448
  have hstable : (prefixWord ++ tailWord_4543448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4543448).length < 2 ^ (prefixWord ++ tailWord_4543448).sum := by decide
  have hdescent : baseEnd_4543448 < baseStart_4543448 := by decide
  rcases family_descends (prefixWord ++ tailWord_4543448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4543478 : List Nat := [5, 1, 1, 1, 3, 2, 1, 1, 1, 7]
def baseStart_4543478 : Nat := 118140960795 + 4543478 * 2 ^ 59
def prefixEnd_4543478 : Nat := 4983230072969 + 3 ^ 40 * 4543478 * 2
def baseEnd_4543478 : Nat := 777662685709559951709977

theorem tailTrace_4543478 : CollatzResearch.WordTrace tailWord_4543478 prefixEnd_4543478 777662685709559951709977 := by
  unfold tailWord_4543478
  simp only [CollatzResearch.WordTrace]
  refine ⟨10357141039610165319364943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 110476171089175096739892725 10357141039610165319364943)
  ·
    refine ⟨15535711559415247979047415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10357141039610165319364943 15535711559415247979047415)
    ·
      refine ⟨23303567339122871968571123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15535711559415247979047415 23303567339122871968571123)
      ·
        refine ⟨34955351008684307952856685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23303567339122871968571123 34955351008684307952856685)
        ·
          refine ⟨13108256628256615482321257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34955351008684307952856685 13108256628256615482321257)
          ·
            refine ⟨9831192471192461611740943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13108256628256615482321257 9831192471192461611740943)
            ·
              refine ⟨14746788706788692417611415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9831192471192461611740943 14746788706788692417611415)
              ·
                refine ⟨22120183060183038626417123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14746788706788692417611415 22120183060183038626417123)
                ·
                  refine ⟨33180274590274557939625685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22120183060183038626417123 33180274590274557939625685)
                  ·
                    refine ⟨777662685709559951709977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33180274590274557939625685 777662685709559951709977)
                    ·
                      rfl

theorem cell23_4543478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 1, 1, 7].length) (baseStart_4543478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4543478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4543478 prefixEnd_4543478 := by exact prefixLift 4543478
  have htrace : WordTrace (prefixWord ++ tailWord_4543478) baseStart_4543478 baseEnd_4543478 := by
    simpa [prefixWord, tailWord_4543478, baseEnd_4543478] using wordTrace_append hprefix tailTrace_4543478
  have hstable : (prefixWord ++ tailWord_4543478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4543478).length < 2 ^ (prefixWord ++ tailWord_4543478).sum := by decide
  have hdescent : baseEnd_4543478 < baseStart_4543478 := by decide
  rcases family_descends (prefixWord ++ tailWord_4543478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4543481 : List Nat := [1, 2, 1, 3, 1, 3, 3, 1, 1, 3, 4]
def baseStart_4543481 : Nat := 118140960795 + 4543481 * 2 ^ 59
def prefixEnd_4543481 : Nat := 4983230072969 + 3 ^ 40 * 4543481 * 2
def baseEnd_4543481 : Nat := 2332989597570643343392417

theorem tailTrace_4543481 : CollatzResearch.WordTrace tailWord_4543481 prefixEnd_4543481 2332989597570643343392417 := by
  unfold tailWord_4543481
  simp only [CollatzResearch.WordTrace]
  refine ⟨165714366052751776622198297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110476244035167851081465531 165714366052751776622198297)
  ·
    refine ⟨124285774539563832466648723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165714366052751776622198297 124285774539563832466648723)
    ·
      refine ⟨186428661809345748699973085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124285774539563832466648723 186428661809345748699973085)
      ·
        refine ⟨69910748178504655762489907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 186428661809345748699973085 69910748178504655762489907)
        ·
          refine ⟨104866122267756983643734861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69910748178504655762489907 104866122267756983643734861)
          ·
            refine ⟨39324795850408868866400573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 104866122267756983643734861 39324795850408868866400573)
            ·
              refine ⟨14746798443903325824900215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39324795850408868866400573 14746798443903325824900215)
              ·
                refine ⟨22120197665854988737350323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14746798443903325824900215 22120197665854988737350323)
                ·
                  refine ⟨33180296498782483106025485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22120197665854988737350323 33180296498782483106025485)
                  ·
                    refine ⟨12442611187043431164759557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33180296498782483106025485 12442611187043431164759557)
                    ·
                      refine ⟨2332989597570643343392417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12442611187043431164759557 2332989597570643343392417)
                      ·
                        rfl

theorem cell23_4543481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 1, 1, 3, 4].length) (baseStart_4543481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4543481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4543481 prefixEnd_4543481 := by exact prefixLift 4543481
  have htrace : WordTrace (prefixWord ++ tailWord_4543481) baseStart_4543481 baseEnd_4543481 := by
    simpa [prefixWord, tailWord_4543481, baseEnd_4543481] using wordTrace_append hprefix tailTrace_4543481
  have hstable : (prefixWord ++ tailWord_4543481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4543481).length < 2 ^ (prefixWord ++ tailWord_4543481).sum := by decide
  have hdescent : baseEnd_4543481 < baseStart_4543481 := by decide
  rcases family_descends (prefixWord ++ tailWord_4543481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4543531 : List Nat := [1, 1, 1, 1, 2, 1, 5, 1, 2, 5, 3]
def baseStart_4543531 : Nat := 118140960795 + 4543531 * 2 ^ 59
def prefixEnd_4543531 : Nat := 4983230072969 + 3 ^ 40 * 4543531 * 2
def baseEnd_4543531 : Nat := 2333015271603368147767187

theorem tailTrace_4543531 : CollatzResearch.WordTrace tailWord_4543531 prefixEnd_4543531 2333015271603368147767187 := by
  unfold tailWord_4543531
  simp only [CollatzResearch.WordTrace]
  refine ⟨165716189702570635161518447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110477459801713756774345631 165716189702570635161518447)
  ·
    refine ⟨248574284553855952742277671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165716189702570635161518447 248574284553855952742277671)
    ·
      refine ⟨372861426830783929113416507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248574284553855952742277671 372861426830783929113416507)
      ·
        refine ⟨559292140246175893670124761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 372861426830783929113416507 559292140246175893670124761)
        ·
          refine ⟨419469105184631920252593571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 559292140246175893670124761 419469105184631920252593571)
          ·
            refine ⟨629203657776947880378890357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 419469105184631920252593571 629203657776947880378890357)
            ·
              refine ⟨58987842916588863785520971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 629203657776947880378890357 58987842916588863785520971)
              ·
                refine ⟨88481764374883295678281457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58987842916588863785520971 88481764374883295678281457)
                ·
                  refine ⟨66361323281162471758711093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 88481764374883295678281457 66361323281162471758711093)
                  ·
                    refine ⟨6221374057608981727379165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 66361323281162471758711093 6221374057608981727379165)
                    ·
                      refine ⟨2333015271603368147767187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6221374057608981727379165 2333015271603368147767187)
                      ·
                        rfl

theorem cell23_4543531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 5, 3].length) (baseStart_4543531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4543531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4543531 prefixEnd_4543531 := by exact prefixLift 4543531
  have htrace : WordTrace (prefixWord ++ tailWord_4543531) baseStart_4543531 baseEnd_4543531 := by
    simpa [prefixWord, tailWord_4543531, baseEnd_4543531] using wordTrace_append hprefix tailTrace_4543531
  have hstable : (prefixWord ++ tailWord_4543531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4543531).length < 2 ^ (prefixWord ++ tailWord_4543531).sum := by decide
  have hdescent : baseEnd_4543531 < baseStart_4543531 := by decide
  rcases family_descends (prefixWord ++ tailWord_4543531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4543551 : List Nat := [1, 1, 2, 2, 3, 1, 1, 2, 5, 5]
def baseStart_4543551 : Nat := 118140960795 + 4543551 * 2 ^ 59
def prefixEnd_4543551 : Nat := 4983230072969 + 3 ^ 40 * 4543551 * 2
def baseEnd_4543551 : Nat := 777675180405486023172365

theorem tailTrace_4543551 : CollatzResearch.WordTrace tailWord_4543551 prefixEnd_4543551 777675180405486023172365 := by
  unfold tailWord_4543551
  simp only [CollatzResearch.WordTrace]
  refine ⟨165716919162498178577246507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110477946108332119051497671 165716919162498178577246507)
  ·
    refine ⟨248575378743747267865869761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165716919162498178577246507 248575378743747267865869761)
    ·
      refine ⟨186431534057810450899402321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 248575378743747267865869761 186431534057810450899402321)
      ·
        refine ⟨139823650543357838174551741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186431534057810450899402321 139823650543357838174551741)
        ·
          refine ⟨52433868953759189315456903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 139823650543357838174551741 52433868953759189315456903)
          ·
            refine ⟨78650803430638783973185355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52433868953759189315456903 78650803430638783973185355)
            ·
              refine ⟨117976205145958175959778033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78650803430638783973185355 117976205145958175959778033)
              ·
                refine ⟨88482153859468631969833525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 117976205145958175959778033 88482153859468631969833525)
                ·
                  refine ⟨8295201924325184247171893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 88482153859468631969833525 8295201924325184247171893)
                  ·
                    refine ⟨777675180405486023172365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8295201924325184247171893 777675180405486023172365)
                    ·
                      rfl

theorem cell23_4543551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 5, 5].length) (baseStart_4543551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4543551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4543551 prefixEnd_4543551 := by exact prefixLift 4543551
  have htrace : WordTrace (prefixWord ++ tailWord_4543551) baseStart_4543551 baseEnd_4543551 := by
    simpa [prefixWord, tailWord_4543551, baseEnd_4543551] using wordTrace_append hprefix tailTrace_4543551
  have hstable : (prefixWord ++ tailWord_4543551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4543551).length < 2 ^ (prefixWord ++ tailWord_4543551).sum := by decide
  have hdescent : baseEnd_4543551 < baseStart_4543551 := by decide
  rcases family_descends (prefixWord ++ tailWord_4543551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4543598 : List Nat := [4, 1, 2, 2, 1, 2, 1, 1, 3, 6]
def baseStart_4543598 : Nat := 118140960795 + 4543598 * 2 ^ 59
def prefixEnd_4543598 : Nat := 4983230072969 + 3 ^ 40 * 4543598 * 2
def baseEnd_4543598 : Nat := 777683224935739795209793

theorem tailTrace_4543598 : CollatzResearch.WordTrace tailWord_4543598 prefixEnd_4543598 777683224935739795209793 := by
  unfold tailWord_4543598
  simp only [CollatzResearch.WordTrace]
  refine ⟨20714829174165988200525931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110479088928885270402804965 20714829174165988200525931)
  ·
    refine ⟨31072243761248982300788897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20714829174165988200525931 31072243761248982300788897)
    ·
      refine ⟨23304182820936736725591673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31072243761248982300788897 23304182820936736725591673)
      ·
        refine ⟨17478137115702552544193755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23304182820936736725591673 17478137115702552544193755)
        ·
          refine ⟨26217205673553828816290633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17478137115702552544193755 26217205673553828816290633)
          ·
            refine ⟨19662904255165371612217975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26217205673553828816290633 19662904255165371612217975)
            ·
              refine ⟨29494356382748057418326963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19662904255165371612217975 29494356382748057418326963)
              ·
                refine ⟨44241534574122086127490445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29494356382748057418326963 44241534574122086127490445)
                ·
                  refine ⟨16590575465295782297808917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44241534574122086127490445 16590575465295782297808917)
                  ·
                    refine ⟨777683224935739795209793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16590575465295782297808917 777683224935739795209793)
                    ·
                      rfl

theorem cell23_4543598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 3, 6].length) (baseStart_4543598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4543598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4543598 prefixEnd_4543598 := by exact prefixLift 4543598
  have htrace : WordTrace (prefixWord ++ tailWord_4543598) baseStart_4543598 baseEnd_4543598 := by
    simpa [prefixWord, tailWord_4543598, baseEnd_4543598] using wordTrace_append hprefix tailTrace_4543598
  have hstable : (prefixWord ++ tailWord_4543598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4543598).length < 2 ^ (prefixWord ++ tailWord_4543598).sum := by decide
  have hdescent : baseEnd_4543598 < baseStart_4543598 := by decide
  rcases family_descends (prefixWord ++ tailWord_4543598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4543601 : List Nat := [1, 2, 2, 2, 1, 1, 2, 2, 3, 1, 6]
def baseStart_4543601 : Nat := 118140960795 + 4543601 * 2 ^ 59
def prefixEnd_4543601 : Nat := 4983230072969 + 3 ^ 40 * 4543601 * 2
def baseEnd_4543601 : Nat := 2333051215249182873891865

theorem tailTrace_4543601 : CollatzResearch.WordTrace tailWord_4543601 prefixEnd_4543601 2333051215249182873891865 := by
  unfold tailWord_4543601
  simp only [CollatzResearch.WordTrace]
  refine ⟨165718742812317037116566657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110479161874878024744377771 165718742812317037116566657)
  ·
    refine ⟨124289057109237777837424993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165718742812317037116566657 124289057109237777837424993)
    ·
      refine ⟨93216792831928333378068745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124289057109237777837424993 93216792831928333378068745)
      ·
        refine ⟨69912594623946250033551559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93216792831928333378068745 69912594623946250033551559)
        ·
          refine ⟨104868891935919375050327339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69912594623946250033551559 104868891935919375050327339)
          ·
            refine ⟨157303337903879062575491009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104868891935919375050327339 157303337903879062575491009)
            ·
              refine ⟨117977503427909296931618257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 157303337903879062575491009 117977503427909296931618257)
              ·
                refine ⟨88483127570931972698713693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 117977503427909296931618257 88483127570931972698713693)
                ·
                  refine ⟨33181172839099489762017635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 88483127570931972698713693 33181172839099489762017635)
                  ·
                    refine ⟨49771759258649234643026453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33181172839099489762017635 49771759258649234643026453)
                    ·
                      refine ⟨2333051215249182873891865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49771759258649234643026453 2333051215249182873891865)
                      ·
                        rfl

theorem cell23_4543601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 3, 1, 6].length) (baseStart_4543601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4543601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4543601 prefixEnd_4543601 := by exact prefixLift 4543601
  have htrace : WordTrace (prefixWord ++ tailWord_4543601) baseStart_4543601 baseEnd_4543601 := by
    simpa [prefixWord, tailWord_4543601, baseEnd_4543601] using wordTrace_append hprefix tailTrace_4543601
  have hstable : (prefixWord ++ tailWord_4543601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4543601).length < 2 ^ (prefixWord ++ tailWord_4543601).sum := by decide
  have hdescent : baseEnd_4543601 < baseStart_4543601 := by decide
  rcases family_descends (prefixWord ++ tailWord_4543601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4543608 : List Nat := [2, 1, 2, 1, 1, 1, 7, 1, 1, 1, 5]
def baseStart_4543608 : Nat := 118140960795 + 4543608 * 2 ^ 59
def prefixEnd_4543608 : Nat := 4983230072969 + 3 ^ 40 * 4543608 * 2
def baseEnd_4543608 : Nat := 2333054809613764346504333

theorem tailTrace_4543608 : CollatzResearch.WordTrace tailWord_4543608 prefixEnd_4543608 2333054809613764346504333 := by
  unfold tailWord_4543608
  simp only [CollatzResearch.WordTrace]
  refine ⟨82859499061645838656035739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110479332082194451541380985 82859499061645838656035739)
  ·
    refine ⟨124289248592468757984053609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82859499061645838656035739 124289248592468757984053609)
    ·
      refine ⟨93216936444351568488040207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124289248592468757984053609 93216936444351568488040207)
      ·
        refine ⟨139825404666527352732060311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93216936444351568488040207 139825404666527352732060311)
        ·
          refine ⟨209738106999791029098090467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139825404666527352732060311 209738106999791029098090467)
          ·
            refine ⟨314607160499686543647135701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 209738106999791029098090467 314607160499686543647135701)
            ·
              refine ⟨7373605324211403366729743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 314607160499686543647135701 7373605324211403366729743)
              ·
                refine ⟨11060407986317105050094615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7373605324211403366729743 11060407986317105050094615)
                ·
                  refine ⟨16590611979475657575141923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11060407986317105050094615 16590611979475657575141923)
                  ·
                    refine ⟨24885917969213486362712885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16590611979475657575141923 24885917969213486362712885)
                    ·
                      refine ⟨2333054809613764346504333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24885917969213486362712885 2333054809613764346504333)
                      ·
                        rfl

theorem cell23_4543608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 1, 1, 1, 5].length) (baseStart_4543608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4543608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4543608 prefixEnd_4543608 := by exact prefixLift 4543608
  have htrace : WordTrace (prefixWord ++ tailWord_4543608) baseStart_4543608 baseEnd_4543608 := by
    simpa [prefixWord, tailWord_4543608, baseEnd_4543608] using wordTrace_append hprefix tailTrace_4543608
  have hstable : (prefixWord ++ tailWord_4543608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4543608).length < 2 ^ (prefixWord ++ tailWord_4543608).sum := by decide
  have hdescent : baseEnd_4543608 < baseStart_4543608 := by decide
  rcases family_descends (prefixWord ++ tailWord_4543608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4543688 : List Nat := [2, 1, 3, 1, 2, 1, 4, 1, 2, 6]
def baseStart_4543688 : Nat := 118140960795 + 4543688 * 2 ^ 59
def prefixEnd_4543688 : Nat := 4983230072969 + 3 ^ 40 * 4543688 * 2
def baseEnd_4543688 : Nat := 777698629355374677834655

theorem tailTrace_4543688 : CollatzResearch.WordTrace tailWord_4543688 prefixEnd_4543688 777698629355374677834655 := by
  unfold tailWord_4543688
  simp only [CollatzResearch.WordTrace]
  refine ⟨82860957981500925487491859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110481277308667900649989145 82860957981500925487491859)
  ·
    refine ⟨124291436972251388231237789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82860957981500925487491859 124291436972251388231237789)
    ·
      refine ⟨46609288864594270586714171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124291436972251388231237789 46609288864594270586714171)
      ·
        refine ⟨69913933296891405880071257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46609288864594270586714171 69913933296891405880071257)
        ·
          refine ⟨52435449972668554410053443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69913933296891405880071257 52435449972668554410053443)
          ·
            refine ⟨78653174959002831615080165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52435449972668554410053443 78653174959002831615080165)
            ·
              refine ⟨14747470304813030927827531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 78653174959002831615080165 14747470304813030927827531)
              ·
                refine ⟨22121205457219546391741297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14747470304813030927827531 22121205457219546391741297)
                ·
                  refine ⟨16590904092914659793805973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22121205457219546391741297 16590904092914659793805973)
                  ·
                    refine ⟨777698629355374677834655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16590904092914659793805973 777698629355374677834655)
                    ·
                      rfl

theorem cell23_4543688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 1, 2, 6].length) (baseStart_4543688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4543688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4543688 prefixEnd_4543688 := by exact prefixLift 4543688
  have htrace : WordTrace (prefixWord ++ tailWord_4543688) baseStart_4543688 baseEnd_4543688 := by
    simpa [prefixWord, tailWord_4543688, baseEnd_4543688] using wordTrace_append hprefix tailTrace_4543688
  have hstable : (prefixWord ++ tailWord_4543688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4543688).length < 2 ^ (prefixWord ++ tailWord_4543688).sum := by decide
  have hdescent : baseEnd_4543688 < baseStart_4543688 := by decide
  rcases family_descends (prefixWord ++ tailWord_4543688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4543695 : List Nat := [1, 1, 2, 1, 1, 3, 2, 5, 1, 4, 2]
def baseStart_4543695 : Nat := 118140960795 + 4543695 * 2 ^ 59
def prefixEnd_4543695 : Nat := 4983230072969 + 3 ^ 40 * 4543695 * 2
def baseEnd_4543695 : Nat := 2333099482430705506116433

theorem tailTrace_4543695 : CollatzResearch.WordTrace tailWord_4543695 prefixEnd_4543695 2333099482430705506116433 := by
  unfold tailWord_4543695
  simp only [CollatzResearch.WordTrace]
  refine ⟨165722171273976491170488539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110481447515984327446992359 165722171273976491170488539)
  ·
    refine ⟨248583256910964736755732809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165722171273976491170488539 248583256910964736755732809)
    ·
      refine ⟨186437442683223552566799607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 248583256910964736755732809 186437442683223552566799607)
      ·
        refine ⟨279656164024835328850199411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186437442683223552566799607 279656164024835328850199411)
        ·
          refine ⟨419484246037252993275299117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 279656164024835328850199411 419484246037252993275299117)
          ·
            refine ⟨157306592263969872478237169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 419484246037252993275299117 157306592263969872478237169)
            ·
              refine ⟨117979944197977404358677877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 157306592263969872478237169 117979944197977404358677877)
              ·
                refine ⟨11060619768560381658626051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 117979944197977404358677877 11060619768560381658626051)
                ·
                  refine ⟨16590929652840572487939077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11060619768560381658626051 16590929652840572487939077)
                  ·
                    refine ⟨3110799309907607341488577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16590929652840572487939077 3110799309907607341488577)
                    ·
                      refine ⟨2333099482430705506116433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3110799309907607341488577 2333099482430705506116433)
                      ·
                        rfl

theorem cell23_4543695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 5, 1, 4, 2].length) (baseStart_4543695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4543695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4543695 prefixEnd_4543695 := by exact prefixLift 4543695
  have htrace : WordTrace (prefixWord ++ tailWord_4543695) baseStart_4543695 baseEnd_4543695 := by
    simpa [prefixWord, tailWord_4543695, baseEnd_4543695] using wordTrace_append hprefix tailTrace_4543695
  have hstable : (prefixWord ++ tailWord_4543695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4543695).length < 2 ^ (prefixWord ++ tailWord_4543695).sum := by decide
  have hdescent : baseEnd_4543695 < baseStart_4543695 := by decide
  rcases family_descends (prefixWord ++ tailWord_4543695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4543712 : List Nat := [2, 1, 1, 3, 1, 4, 1, 2, 4, 2, 2]
def baseStart_4543712 : Nat := 118140960795 + 4543712 * 2 ^ 59
def prefixEnd_4543712 : Nat := 4983230072969 + 3 ^ 40 * 4543712 * 2
def baseEnd_4543712 : Nat := 2333108211601831939603855

theorem tailTrace_4543712 : CollatzResearch.WordTrace tailWord_4543712 prefixEnd_4543712 2333108211601831939603855 := by
  unfold tailWord_4543712
  simp only [CollatzResearch.WordTrace]
  refine ⟨82861395657457451536928695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110481860876609935382571593 82861395657457451536928695)
  ·
    refine ⟨124292093486186177305393043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82861395657457451536928695 124292093486186177305393043)
    ·
      refine ⟨186438140229279265958089565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124292093486186177305393043 186438140229279265958089565)
      ·
        refine ⟨69914302585979724734283587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 186438140229279265958089565 69914302585979724734283587)
        ·
          refine ⟨104871453878969587101425381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69914302585979724734283587 104871453878969587101425381)
          ·
            refine ⟨19663397602306797581517259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 104871453878969587101425381 19663397602306797581517259)
            ·
              refine ⟨29495096403460196372275889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19663397602306797581517259 29495096403460196372275889)
              ·
                refine ⟨22121322302595147279206917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29495096403460196372275889 22121322302595147279206917)
                ·
                  refine ⟨4147747931736590114851297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22121322302595147279206917 4147747931736590114851297)
                  ·
                    refine ⟨3110810948802442586138473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4147747931736590114851297 3110810948802442586138473)
                    ·
                      refine ⟨2333108211601831939603855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3110810948802442586138473 2333108211601831939603855)
                      ·
                        rfl

theorem cell23_4543712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 2, 4, 2, 2].length) (baseStart_4543712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4543712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4543712 prefixEnd_4543712 := by exact prefixLift 4543712
  have htrace : WordTrace (prefixWord ++ tailWord_4543712) baseStart_4543712 baseEnd_4543712 := by
    simpa [prefixWord, tailWord_4543712, baseEnd_4543712] using wordTrace_append hprefix tailTrace_4543712
  have hstable : (prefixWord ++ tailWord_4543712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4543712).length < 2 ^ (prefixWord ++ tailWord_4543712).sum := by decide
  have hdescent : baseEnd_4543712 < baseStart_4543712 := by decide
  rcases family_descends (prefixWord ++ tailWord_4543712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4543786 : List Nat := [3, 1, 4, 2, 1, 3, 2, 2, 5]
def baseStart_4543786 : Nat := 118140960795 + 4543786 * 2 ^ 59
def prefixEnd_4543786 : Nat := 4983230072969 + 3 ^ 40 * 4543786 * 2
def baseEnd_4543786 : Nat := 259238467685584961119835

theorem tailTrace_4543786 : CollatzResearch.WordTrace tailWord_4543786 prefixEnd_4543786 259238467685584961119835 := by
  unfold tailWord_4543786
  simp only [CollatzResearch.WordTrace]
  refine ⟨41431372579161703428012803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110483660211097875808034141 41431372579161703428012803)
  ·
    refine ⟨62147058868742555142019205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41431372579161703428012803 62147058868742555142019205)
    ·
      refine ⟨11652573537889229089128601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62147058868742555142019205 11652573537889229089128601)
      ·
        refine ⟨8739430153416921816846451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11652573537889229089128601 8739430153416921816846451)
        ·
          refine ⟨13109145230125382725269677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8739430153416921816846451 13109145230125382725269677)
          ·
            refine ⟨4915929461297018521976129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13109145230125382725269677 4915929461297018521976129)
            ·
              refine ⟨3686947095972763891482097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4915929461297018521976129 3686947095972763891482097)
              ·
                refine ⟨2765210321979572918611573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3686947095972763891482097 2765210321979572918611573)
                ·
                  refine ⟨259238467685584961119835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2765210321979572918611573 259238467685584961119835)
                  ·
                    rfl

theorem cell23_4543786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 2, 2, 5].length) (baseStart_4543786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4543786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4543786 prefixEnd_4543786 := by exact prefixLift 4543786
  have htrace : WordTrace (prefixWord ++ tailWord_4543786) baseStart_4543786 baseEnd_4543786 := by
    simpa [prefixWord, tailWord_4543786, baseEnd_4543786] using wordTrace_append hprefix tailTrace_4543786
  have hstable : (prefixWord ++ tailWord_4543786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4543786).length < 2 ^ (prefixWord ++ tailWord_4543786).sum := by decide
  have hdescent : baseEnd_4543786 < baseStart_4543786 := by decide
  rcases family_descends (prefixWord ++ tailWord_4543786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4543788 : List Nat := [2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 5]
def baseStart_4543788 : Nat := 118140960795 + 4543788 * 2 ^ 59
def prefixEnd_4543788 : Nat := 4983230072969 + 3 ^ 40 * 4543788 * 2
def baseEnd_4543788 : Nat := 2333147236131573642253505

theorem tailTrace_4543788 : CollatzResearch.WordTrace tailWord_4543788 prefixEnd_4543788 2333147236131573642253505 := by
  unfold tailWord_4543788
  simp only [CollatzResearch.WordTrace]
  refine ⟨82862781631319784026812009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110483708841759712035749345 82862781631319784026812009)
  ·
    refine ⟨62147086223489838020109007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82862781631319784026812009 62147086223489838020109007)
    ·
      refine ⟨93220629335234757030163511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62147086223489838020109007 93220629335234757030163511)
      ·
        refine ⟨139830944002852135545245267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93220629335234757030163511 139830944002852135545245267)
        ·
          refine ⟨209746416004278203317867901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139830944002852135545245267 209746416004278203317867901)
          ·
            refine ⟨78654906001604326244200463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 209746416004278203317867901 78654906001604326244200463)
            ·
              refine ⟨117982359002406489366300695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78654906001604326244200463 117982359002406489366300695)
              ·
                refine ⟨176973538503609734049451043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117982359002406489366300695 176973538503609734049451043)
                ·
                  refine ⟨265460307755414601074176565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 176973538503609734049451043 265460307755414601074176565)
                  ·
                    refine ⟨24886903852070118850704053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 265460307755414601074176565 24886903852070118850704053)
                    ·
                      refine ⟨2333147236131573642253505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24886903852070118850704053 2333147236131573642253505)
                      ·
                        rfl

theorem cell23_4543788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 5].length) (baseStart_4543788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4543788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4543788 prefixEnd_4543788 := by exact prefixLift 4543788
  have htrace : WordTrace (prefixWord ++ tailWord_4543788) baseStart_4543788 baseEnd_4543788 := by
    simpa [prefixWord, tailWord_4543788, baseEnd_4543788] using wordTrace_append hprefix tailTrace_4543788
  have hstable : (prefixWord ++ tailWord_4543788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4543788).length < 2 ^ (prefixWord ++ tailWord_4543788).sum := by decide
  have hdescent : baseEnd_4543788 < baseStart_4543788 := by decide
  rcases family_descends (prefixWord ++ tailWord_4543788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4543789 : List Nat := [1, 5, 3, 1, 1, 1, 1, 1, 2, 5, 2]
def baseStart_4543789 : Nat := 118140960795 + 4543789 * 2 ^ 59
def prefixEnd_4543789 : Nat := 4983230072969 + 3 ^ 40 * 4543789 * 2
def baseEnd_4543789 : Nat := 2333147749612228138341001

theorem tailTrace_4543789 : CollatzResearch.WordTrace tailWord_4543789 prefixEnd_4543789 2333147749612228138341001 := by
  unfold tailWord_4543789
  simp only [CollatzResearch.WordTrace]
  refine ⟨165725599735635945224410421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110483733157090630149606947 165725599735635945224410421)
  ·
    refine ⟨15536774975215869864788477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 165725599735635945224410421 15536774975215869864788477)
    ·
      refine ⟨5826290615705951199295679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15536774975215869864788477 5826290615705951199295679)
      ·
        refine ⟨8739435923558926798943519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5826290615705951199295679 8739435923558926798943519)
        ·
          refine ⟨13109153885338390198415279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8739435923558926798943519 13109153885338390198415279)
          ·
            refine ⟨19663730828007585297622919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13109153885338390198415279 19663730828007585297622919)
            ·
              refine ⟨29495596242011377946434379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19663730828007585297622919 29495596242011377946434379)
              ·
                refine ⟨44243394363017066919651569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29495596242011377946434379 44243394363017066919651569)
                ·
                  refine ⟨33182545772262800189738677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44243394363017066919651569 33182545772262800189738677)
                  ·
                    refine ⟨3110863666149637517788001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33182545772262800189738677 3110863666149637517788001)
                    ·
                      refine ⟨2333147749612228138341001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3110863666149637517788001 2333147749612228138341001)
                      ·
                        rfl

theorem cell23_4543789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_4543789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4543789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4543789 prefixEnd_4543789 := by exact prefixLift 4543789
  have htrace : WordTrace (prefixWord ++ tailWord_4543789) baseStart_4543789 baseEnd_4543789 := by
    simpa [prefixWord, tailWord_4543789, baseEnd_4543789] using wordTrace_append hprefix tailTrace_4543789
  have hstable : (prefixWord ++ tailWord_4543789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4543789).length < 2 ^ (prefixWord ++ tailWord_4543789).sum := by decide
  have hdescent : baseEnd_4543789 < baseStart_4543789 := by decide
  rcases family_descends (prefixWord ++ tailWord_4543789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4543802 : List Nat := [3, 1, 1, 1, 4, 1, 3, 1, 2, 4, 2]
def baseStart_4543802 : Nat := 118140960795 + 4543802 * 2 ^ 59
def prefixEnd_4543802 : Nat := 4983230072969 + 3 ^ 40 * 4543802 * 2
def baseEnd_4543802 : Nat := 2333154424860736587478441

theorem tailTrace_4543802 : CollatzResearch.WordTrace tailWord_4543802 prefixEnd_4543802 2333154424860736587478441 := by
  unfold tailWord_4543802
  simp only [CollatzResearch.WordTrace]
  refine ⟨41431518471147212111158415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110484049256392565629755773 41431518471147212111158415)
  ·
    refine ⟨62147277706720818166737623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41431518471147212111158415 62147277706720818166737623)
    ·
      refine ⟨93220916560081227250106435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62147277706720818166737623 93220916560081227250106435)
      ·
        refine ⟨139831374840121840875159653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93220916560081227250106435 139831374840121840875159653)
        ·
          refine ⟨26218382782522845164092435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 139831374840121840875159653 26218382782522845164092435)
          ·
            refine ⟨39327574173784267746138653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26218382782522845164092435 39327574173784267746138653)
            ·
              refine ⟨14747840315169100404801995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39327574173784267746138653 14747840315169100404801995)
              ·
                refine ⟨22121760472753650607202993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14747840315169100404801995 22121760472753650607202993)
                ·
                  refine ⟨16591320354565237955402245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22121760472753650607202993 16591320354565237955402245)
                  ·
                    refine ⟨3110872566480982116637921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16591320354565237955402245 3110872566480982116637921)
                    ·
                      refine ⟨2333154424860736587478441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3110872566480982116637921 2333154424860736587478441)
                      ·
                        rfl

theorem cell23_4543802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 1, 2, 4, 2].length) (baseStart_4543802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4543802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4543802 prefixEnd_4543802 := by exact prefixLift 4543802
  have htrace : WordTrace (prefixWord ++ tailWord_4543802) baseStart_4543802 baseEnd_4543802 := by
    simpa [prefixWord, tailWord_4543802, baseEnd_4543802] using wordTrace_append hprefix tailTrace_4543802
  have hstable : (prefixWord ++ tailWord_4543802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4543802).length < 2 ^ (prefixWord ++ tailWord_4543802).sum := by decide
  have hdescent : baseEnd_4543802 < baseStart_4543802 := by decide
  rcases family_descends (prefixWord ++ tailWord_4543802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4543829 : List Nat := [1, 3, 2, 2, 3, 1, 1, 5, 1, 4]
def baseStart_4543829 : Nat := 118140960795 + 4543829 * 2 ^ 59
def prefixEnd_4543829 : Nat := 4983230072969 + 3 ^ 40 * 4543829 * 2
def baseEnd_4543829 : Nat := 777722762946135993946939

theorem tailTrace_4543829 : CollatzResearch.WordTrace tailWord_4543829 prefixEnd_4543829 777722762946135993946939 := by
  unfold tailWord_4543829
  simp only [CollatzResearch.WordTrace]
  refine ⟨165727058655491032055866541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110484705770327354703911027 165727058655491032055866541)
  ·
    refine ⟨62147646995809137020949953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165727058655491032055866541 62147646995809137020949953)
    ·
      refine ⟨46610735246856852765712465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62147646995809137020949953 46610735246856852765712465)
      ·
        refine ⟨34958051435142639574284349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46610735246856852765712465 34958051435142639574284349)
        ·
          refine ⟨13109269288178489840356631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34958051435142639574284349 13109269288178489840356631)
          ·
            refine ⟨19663903932267734760534947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13109269288178489840356631 19663903932267734760534947)
            ·
              refine ⟨29495855898401602140802421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19663903932267734760534947 29495855898401602140802421)
              ·
                refine ⟨2765236490475150200700227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29495855898401602140802421 2765236490475150200700227)
                ·
                  refine ⟨4147854735712725301050341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2765236490475150200700227 4147854735712725301050341)
                  ·
                    refine ⟨777722762946135993946939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4147854735712725301050341 777722762946135993946939)
                    ·
                      rfl

theorem cell23_4543829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 5, 1, 4].length) (baseStart_4543829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4543829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4543829 prefixEnd_4543829 := by exact prefixLift 4543829
  have htrace : WordTrace (prefixWord ++ tailWord_4543829) baseStart_4543829 baseEnd_4543829 := by
    simpa [prefixWord, tailWord_4543829, baseEnd_4543829] using wordTrace_append hprefix tailTrace_4543829
  have hstable : (prefixWord ++ tailWord_4543829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4543829).length < 2 ^ (prefixWord ++ tailWord_4543829).sum := by decide
  have hdescent : baseEnd_4543829 < baseStart_4543829 := by decide
  rcases family_descends (prefixWord ++ tailWord_4543829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4543896 : List Nat := [2, 1, 2, 5, 2, 1, 1, 2, 2, 3, 2]
def baseStart_4543896 : Nat := 118140960795 + 4543896 * 2 ^ 59
def prefixEnd_4543896 : Nat := 4983230072969 + 3 ^ 40 * 4543896 * 2
def baseEnd_4543896 : Nat := 2333202692042259219703009

theorem tailTrace_4543896 : CollatzResearch.WordTrace tailWord_4543896 prefixEnd_4543896 2333202692042259219703009 := by
  unfold tailWord_4543896
  simp only [CollatzResearch.WordTrace]
  refine ⟨82864751173124151249277771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110486334897498868332370361 82864751173124151249277771)
  ·
    refine ⟨124297126759686226873916657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82864751173124151249277771 124297126759686226873916657)
    ·
      refine ⟨93222845069764670155437493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124297126759686226873916657 93222845069764670155437493)
      ·
        refine ⟨8739641725290437827072265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 93222845069764670155437493 8739641725290437827072265)
        ·
          refine ⟨6554731293967828370304199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8739641725290437827072265 6554731293967828370304199)
          ·
            refine ⟨9832096940951742555456299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6554731293967828370304199 9832096940951742555456299)
            ·
              refine ⟨14748145411427613833184449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9832096940951742555456299 14748145411427613833184449)
              ·
                refine ⟨11061109058570710374888337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14748145411427613833184449 11061109058570710374888337)
                ·
                  refine ⟨8295831793928032781166253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11061109058570710374888337 8295831793928032781166253)
                  ·
                    refine ⟨3110936922723012292937345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8295831793928032781166253 3110936922723012292937345)
                    ·
                      refine ⟨2333202692042259219703009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3110936922723012292937345 2333202692042259219703009)
                      ·
                        rfl

theorem cell23_4543896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_4543896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4543896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4543896 prefixEnd_4543896 := by exact prefixLift 4543896
  have htrace : WordTrace (prefixWord ++ tailWord_4543896) baseStart_4543896 baseEnd_4543896 := by
    simpa [prefixWord, tailWord_4543896, baseEnd_4543896] using wordTrace_append hprefix tailTrace_4543896
  have hstable : (prefixWord ++ tailWord_4543896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4543896).length < 2 ^ (prefixWord ++ tailWord_4543896).sum := by decide
  have hdescent : baseEnd_4543896 < baseStart_4543896 := by decide
  rcases family_descends (prefixWord ++ tailWord_4543896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4543903 : List Nat := [1, 1, 2, 5, 1, 3, 3, 2, 1, 1, 3]
def baseStart_4543903 : Nat := 118140960795 + 4543903 * 2 ^ 59
def prefixEnd_4543903 : Nat := 4983230072969 + 3 ^ 40 * 4543903 * 2
def baseEnd_4543903 : Nat := 2333206286406840692315477

theorem tailTrace_4543903 : CollatzResearch.WordTrace tailWord_4543903 prefixEnd_4543903 2333206286406840692315477 := by
  unfold tailWord_4543903
  simp only [CollatzResearch.WordTrace]
  refine ⟨165729757657222942694060363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110486505104815295129373575 165729757657222942694060363)
  ·
    refine ⟨248594636485834414041090545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165729757657222942694060363 248594636485834414041090545)
    ·
      refine ⟨186445977364375810530817909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 248594636485834414041090545 186445977364375810530817909)
      ·
        refine ⟨17479310377910232237264179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 186445977364375810530817909 17479310377910232237264179)
        ·
          refine ⟨26218965566865348355896269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17479310377910232237264179 26218965566865348355896269)
          ·
            refine ⟨9832112087574505633461101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26218965566865348355896269 9832112087574505633461101)
            ·
              refine ⟨3687042032840439612547913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9832112087574505633461101 3687042032840439612547913)
              ·
                refine ⟨2765281524630329709410935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3687042032840439612547913 2765281524630329709410935)
                ·
                  refine ⟨4147922286945494564116403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2765281524630329709410935 4147922286945494564116403)
                  ·
                    refine ⟨6221883430418241846174605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4147922286945494564116403 6221883430418241846174605)
                    ·
                      refine ⟨2333206286406840692315477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6221883430418241846174605 2333206286406840692315477)
                      ·
                        rfl

theorem cell23_4543903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 3, 2, 1, 1, 3].length) (baseStart_4543903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4543903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4543903 prefixEnd_4543903 := by exact prefixLift 4543903
  have htrace : WordTrace (prefixWord ++ tailWord_4543903) baseStart_4543903 baseEnd_4543903 := by
    simpa [prefixWord, tailWord_4543903, baseEnd_4543903] using wordTrace_append hprefix tailTrace_4543903
  have hstable : (prefixWord ++ tailWord_4543903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4543903).length < 2 ^ (prefixWord ++ tailWord_4543903).sum := by decide
  have hdescent : baseEnd_4543903 < baseStart_4543903 := by decide
  rcases family_descends (prefixWord ++ tailWord_4543903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4543909 : List Nat := [1, 3, 1, 2, 1, 1, 2, 5, 3, 2, 2]
def baseStart_4543909 : Nat := 118140960795 + 4543909 * 2 ^ 59
def prefixEnd_4543909 : Nat := 4983230072969 + 3 ^ 40 * 4543909 * 2
def baseEnd_4543909 : Nat := 2333209367290767668840449

theorem tailTrace_4543909 : CollatzResearch.WordTrace tailWord_4543909 prefixEnd_4543909 2333209367290767668840449 := by
  unfold tailWord_4543909
  simp only [CollatzResearch.WordTrace]
  refine ⟨165729976495201205718778781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110486650996800803812519187 165729976495201205718778781)
  ·
    refine ⟨62148741185700452144542043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165729976495201205718778781 62148741185700452144542043)
    ·
      refine ⟨93223111778550678216813065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62148741185700452144542043 93223111778550678216813065)
      ·
        refine ⟨69917333833913008662609799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93223111778550678216813065 69917333833913008662609799)
        ·
          refine ⟨104876000750869512993914699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69917333833913008662609799 104876000750869512993914699)
          ·
            refine ⟨157314001126304269490872049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104876000750869512993914699 157314001126304269490872049)
            ·
              refine ⟨117985500844728202118154037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 157314001126304269490872049 117985500844728202118154037)
              ·
                refine ⟨11061140704193268948576941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 117985500844728202118154037 11061140704193268948576941)
                ·
                  refine ⟨4147927764072475855716353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11061140704193268948576941 4147927764072475855716353)
                  ·
                    refine ⟨3110945823054356891787265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4147927764072475855716353 3110945823054356891787265)
                    ·
                      refine ⟨2333209367290767668840449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3110945823054356891787265 2333209367290767668840449)
                      ·
                        rfl

theorem cell23_4543909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 5, 3, 2, 2].length) (baseStart_4543909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4543909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4543909 prefixEnd_4543909 := by exact prefixLift 4543909
  have htrace : WordTrace (prefixWord ++ tailWord_4543909) baseStart_4543909 baseEnd_4543909 := by
    simpa [prefixWord, tailWord_4543909, baseEnd_4543909] using wordTrace_append hprefix tailTrace_4543909
  have hstable : (prefixWord ++ tailWord_4543909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4543909).length < 2 ^ (prefixWord ++ tailWord_4543909).sum := by decide
  have hdescent : baseEnd_4543909 < baseStart_4543909 := by decide
  rcases family_descends (prefixWord ++ tailWord_4543909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4543929 : List Nat := [1, 2, 1, 4, 4, 1, 1, 1, 3, 2, 3]
def baseStart_4543929 : Nat := 118140960795 + 4543929 * 2 ^ 59
def prefixEnd_4543929 : Nat := 4983230072969 + 3 ^ 40 * 4543929 * 2
def baseEnd_4543929 : Nat := 2333219636903857590590357

theorem tailTrace_4543929 : CollatzResearch.WordTrace tailWord_4543929 prefixEnd_4543929 2333219636903857590590357 := by
  unfold tailWord_4543929
  simp only [CollatzResearch.WordTrace]
  refine ⟨165730705955128749134506841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110487137303419166089671227 165730705955128749134506841)
  ·
    refine ⟨124298029466346561850880131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165730705955128749134506841 124298029466346561850880131)
    ·
      refine ⟨186447044199519842776320197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124298029466346561850880131 186447044199519842776320197)
      ·
        refine ⟨34958820787409970520560037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 186447044199519842776320197 34958820787409970520560037)
        ·
          refine ⟨6554778897639369472605007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34958820787409970520560037 6554778897639369472605007)
          ·
            refine ⟨9832168346459054208907511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6554778897639369472605007 9832168346459054208907511)
            ·
              refine ⟨14748252519688581313361267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9832168346459054208907511 14748252519688581313361267)
              ·
                refine ⟨22122378779532871970041901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14748252519688581313361267 22122378779532871970041901)
                ·
                  refine ⟨8295892042324826988765713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22122378779532871970041901 8295892042324826988765713)
                  ·
                    refine ⟨6221919031743620241574285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8295892042324826988765713 6221919031743620241574285)
                    ·
                      refine ⟨2333219636903857590590357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6221919031743620241574285 2333219636903857590590357)
                      ·
                        rfl

theorem cell23_4543929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 1, 3, 2, 3].length) (baseStart_4543929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4543929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4543929 prefixEnd_4543929 := by exact prefixLift 4543929
  have htrace : WordTrace (prefixWord ++ tailWord_4543929) baseStart_4543929 baseEnd_4543929 := by
    simpa [prefixWord, tailWord_4543929, baseEnd_4543929] using wordTrace_append hprefix tailTrace_4543929
  have hstable : (prefixWord ++ tailWord_4543929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4543929).length < 2 ^ (prefixWord ++ tailWord_4543929).sum := by decide
  have hdescent : baseEnd_4543929 < baseStart_4543929 := by decide
  rcases family_descends (prefixWord ++ tailWord_4543929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4543946 : List Nat := [3, 1, 2, 1, 2, 4, 3, 1, 1, 2, 3]
def baseStart_4543946 : Nat := 118140960795 + 4543946 * 2 ^ 59
def prefixEnd_4543946 : Nat := 4983230072969 + 3 ^ 40 * 4543946 * 2
def baseEnd_4543946 : Nat := 2333228366074984024077779

theorem tailTrace_4543946 : CollatzResearch.WordTrace tailWord_4543946 prefixEnd_4543946 2333228366074984024077779 := by
  unfold tailWord_4543946
  simp only [CollatzResearch.WordTrace]
  refine ⟨41432831499016790259468923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110487550664044774025250461 41432831499016790259468923)
  ·
    refine ⟨62149247248525185389203385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41432831499016790259468923 62149247248525185389203385)
    ·
      refine ⟨46611935436393889041902539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62149247248525185389203385 46611935436393889041902539)
      ·
        refine ⟨69917903154590833562853809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46611935436393889041902539 69917903154590833562853809)
        ·
          refine ⟨52438427365943125172140357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69917903154590833562853809 52438427365943125172140357)
          ·
            refine ⟨9832205131114335969776317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52438427365943125172140357 9832205131114335969776317)
            ·
              refine ⟨3687076924167875988666119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9832205131114335969776317 3687076924167875988666119)
              ·
                refine ⟨5530615386251813982999179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3687076924167875988666119 5530615386251813982999179)
                ·
                  refine ⟨8295923079377720974498769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5530615386251813982999179 8295923079377720974498769)
                  ·
                    refine ⟨6221942309533290730874077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8295923079377720974498769 6221942309533290730874077)
                    ·
                      refine ⟨2333228366074984024077779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6221942309533290730874077 2333228366074984024077779)
                      ·
                        rfl

theorem cell23_4543946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 3, 1, 1, 2, 3].length) (baseStart_4543946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4543946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4543946 prefixEnd_4543946 := by exact prefixLift 4543946
  have htrace : WordTrace (prefixWord ++ tailWord_4543946) baseStart_4543946 baseEnd_4543946 := by
    simpa [prefixWord, tailWord_4543946, baseEnd_4543946] using wordTrace_append hprefix tailTrace_4543946
  have hstable : (prefixWord ++ tailWord_4543946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4543946).length < 2 ^ (prefixWord ++ tailWord_4543946).sum := by decide
  have hdescent : baseEnd_4543946 < baseStart_4543946 := by decide
  rcases family_descends (prefixWord ++ tailWord_4543946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4543969 : List Nat := [1, 2, 3, 1, 2, 3, 1, 2, 3, 3, 2]
def baseStart_4543969 : Nat := 118140960795 + 4543969 * 2 ^ 59
def prefixEnd_4543969 : Nat := 4983230072969 + 3 ^ 40 * 4543969 * 2
def baseEnd_4543969 : Nat := 2333240176130037434090173

theorem tailTrace_4543969 : CollatzResearch.WordTrace tailWord_4543969 prefixEnd_4543969 2333240176130037434090173 := by
  unfold tailWord_4543969
  simp only [CollatzResearch.WordTrace]
  refine ⟨165732164874983835965962961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110488109916655890643975307 165732164874983835965962961)
  ·
    refine ⟨124299123656237876974472221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165732164874983835965962961 124299123656237876974472221)
    ·
      refine ⟨46612171371089203865427083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124299123656237876974472221 46612171371089203865427083)
      ·
        refine ⟨69918257056633805798140625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46612171371089203865427083 69918257056633805798140625)
        ·
          refine ⟨52438692792475354348605469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69918257056633805798140625 52438692792475354348605469)
          ·
            refine ⟨19664509797178257880727051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52438692792475354348605469 19664509797178257880727051)
            ·
              refine ⟨29496764695767386821090577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19664509797178257880727051 29496764695767386821090577)
              ·
                refine ⟨22122573521825540115817933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29496764695767386821090577 22122573521825540115817933)
                ·
                  refine ⟨8295965070684577543431725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22122573521825540115817933 8295965070684577543431725)
                  ·
                    refine ⟨3110986901506716578786897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8295965070684577543431725 3110986901506716578786897)
                    ·
                      refine ⟨2333240176130037434090173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3110986901506716578786897 2333240176130037434090173)
                      ·
                        rfl

theorem cell23_4543969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 2, 3, 3, 2].length) (baseStart_4543969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4543969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4543969 prefixEnd_4543969 := by exact prefixLift 4543969
  have htrace : WordTrace (prefixWord ++ tailWord_4543969) baseStart_4543969 baseEnd_4543969 := by
    simpa [prefixWord, tailWord_4543969, baseEnd_4543969] using wordTrace_append hprefix tailTrace_4543969
  have hstable : (prefixWord ++ tailWord_4543969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4543969).length < 2 ^ (prefixWord ++ tailWord_4543969).sum := by decide
  have hdescent : baseEnd_4543969 < baseStart_4543969 := by decide
  rcases family_descends (prefixWord ++ tailWord_4543969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4543982 : List Nat := [4, 1, 2, 1, 2, 1, 1, 2, 2, 3, 4]
def baseStart_4543982 : Nat := 118140960795 + 4543982 * 2 ^ 59
def prefixEnd_4543982 : Nat := 4983230072969 + 3 ^ 40 * 4543982 * 2
def baseEnd_4543982 : Nat := 2333246851378545883227613

theorem tailTrace_4543982 : CollatzResearch.WordTrace tailWord_4543982 prefixEnd_4543982 2333246851378545883227613 := by
  unfold tailWord_4543982
  simp only [CollatzResearch.WordTrace]
  refine ⟨20716579877992092398273275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110488426015957826124124133 20716579877992092398273275)
  ·
    refine ⟨31074869816988138597409913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20716579877992092398273275 31074869816988138597409913)
    ·
      refine ⟨23306152362741103948057435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31074869816988138597409913 23306152362741103948057435)
      ·
        refine ⟨34959228544111655922086153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23306152362741103948057435 34959228544111655922086153)
        ·
          refine ⟨26219421408083741941564615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34959228544111655922086153 26219421408083741941564615)
          ·
            refine ⟨39329132112125612912346923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26219421408083741941564615 39329132112125612912346923)
            ·
              refine ⟨58993698168188419368520385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39329132112125612912346923 58993698168188419368520385)
              ·
                refine ⟨44245273626141314526390289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58993698168188419368520385 44245273626141314526390289)
                ·
                  refine ⟨33183955219605985894792717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44245273626141314526390289 33183955219605985894792717)
                  ·
                    refine ⟨12443983207352244710547269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33183955219605985894792717 12443983207352244710547269)
                    ·
                      refine ⟨2333246851378545883227613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12443983207352244710547269 2333246851378545883227613)
                      ·
                        rfl

theorem cell23_4543982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_4543982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4543982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4543982 prefixEnd_4543982 := by exact prefixLift 4543982
  have htrace : WordTrace (prefixWord ++ tailWord_4543982) baseStart_4543982 baseEnd_4543982 := by
    simpa [prefixWord, tailWord_4543982, baseEnd_4543982] using wordTrace_append hprefix tailTrace_4543982
  have hstable : (prefixWord ++ tailWord_4543982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4543982).length < 2 ^ (prefixWord ++ tailWord_4543982).sum := by decide
  have hdescent : baseEnd_4543982 < baseStart_4543982 := by decide
  rcases family_descends (prefixWord ++ tailWord_4543982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4543986 : List Nat := [3, 2, 1, 4, 1, 1, 2, 1, 3, 3, 2]
def baseStart_4543986 : Nat := 118140960795 + 4543986 * 2 ^ 59
def prefixEnd_4543986 : Nat := 4983230072969 + 3 ^ 40 * 4543986 * 2
def baseEnd_4543986 : Nat := 2333248905301163867577595

theorem tailTrace_4543986 : CollatzResearch.WordTrace tailWord_4543986 prefixEnd_4543986 2333248905301163867577595 := by
  unfold tailWord_4543986
  simp only [CollatzResearch.WordTrace]
  refine ⟨41433196228980561967332953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110488523277281498579554541 41433196228980561967332953)
  ·
    refine ⟨31074897171735421475499715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41433196228980561967332953 31074897171735421475499715)
    ·
      refine ⟨46612345757603132213249573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31074897171735421475499715 46612345757603132213249573)
      ·
        refine ⟨8739814829550587289984295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46612345757603132213249573 8739814829550587289984295)
        ·
          refine ⟨13109722244325880934976443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8739814829550587289984295 13109722244325880934976443)
          ·
            refine ⟨19664583366488821402464665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13109722244325880934976443 19664583366488821402464665)
            ·
              refine ⟨14748437524866616051848499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19664583366488821402464665 14748437524866616051848499)
              ·
                refine ⟨22122656287299924077772749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14748437524866616051848499 22122656287299924077772749)
                ·
                  refine ⟨8295996107737471529164781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22122656287299924077772749 8295996107737471529164781)
                  ·
                    refine ⟨3110998540401551823436793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8295996107737471529164781 3110998540401551823436793)
                    ·
                      refine ⟨2333248905301163867577595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3110998540401551823436793 2333248905301163867577595)
                      ·
                        rfl

theorem cell23_4543986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_4543986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4543986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4543986 prefixEnd_4543986 := by exact prefixLift 4543986
  have htrace : WordTrace (prefixWord ++ tailWord_4543986) baseStart_4543986 baseEnd_4543986 := by
    simpa [prefixWord, tailWord_4543986, baseEnd_4543986] using wordTrace_append hprefix tailTrace_4543986
  have hstable : (prefixWord ++ tailWord_4543986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4543986).length < 2 ^ (prefixWord ++ tailWord_4543986).sum := by decide
  have hdescent : baseEnd_4543986 < baseStart_4543986 := by decide
  rcases family_descends (prefixWord ++ tailWord_4543986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4544005 : List Nat := [1, 3, 1, 1, 2, 2, 1, 1, 11]
def baseStart_4544005 : Nat := 118140960795 + 4544005 * 2 ^ 59
def prefixEnd_4544005 : Nat := 4983230072969 + 3 ^ 40 * 4544005 * 2
def baseEnd_4544005 : Nat := 259250962381511032582223

theorem tailTrace_4544005 : CollatzResearch.WordTrace tailWord_4544005 prefixEnd_4544005 259250962381511032582223 := by
  unfold tailWord_4544005
  simp only [CollatzResearch.WordTrace]
  refine ⟨165733477902853414114273469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110488985268568942742848979 165733477902853414114273469)
  ·
    refine ⟨62150054213570030292852551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165733477902853414114273469 62150054213570030292852551)
    ·
      refine ⟨93225081320355045439278827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62150054213570030292852551 93225081320355045439278827)
      ·
        refine ⟨139837621980532568158918241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93225081320355045439278827 139837621980532568158918241)
        ·
          refine ⟨104878216485399426119188681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139837621980532568158918241 104878216485399426119188681)
          ·
            refine ⟨78658662364049569589391511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104878216485399426119188681 78658662364049569589391511)
            ·
              refine ⟨117987993546074354384087267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78658662364049569589391511 117987993546074354384087267)
              ·
                refine ⟨176981990319111531576130901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117987993546074354384087267 176981990319111531576130901)
                ·
                  refine ⟨259250962381511032582223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 176981990319111531576130901 259250962381511032582223)
                  ·
                    rfl

theorem cell23_4544005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 11].length) (baseStart_4544005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4544005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4544005 prefixEnd_4544005 := by exact prefixLift 4544005
  have htrace : WordTrace (prefixWord ++ tailWord_4544005) baseStart_4544005 baseEnd_4544005 := by
    simpa [prefixWord, tailWord_4544005, baseEnd_4544005] using wordTrace_append hprefix tailTrace_4544005
  have hstable : (prefixWord ++ tailWord_4544005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4544005).length < 2 ^ (prefixWord ++ tailWord_4544005).sum := by decide
  have hdescent : baseEnd_4544005 < baseStart_4544005 := by decide
  rcases family_descends (prefixWord ++ tailWord_4544005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4544025 : List Nat := [1, 2, 1, 2, 1, 1, 2, 1, 1, 3, 8]
def baseStart_4544025 : Nat := 118140960795 + 4544025 * 2 ^ 59
def prefixEnd_4544025 : Nat := 4983230072969 + 3 ^ 40 * 4544025 * 2
def baseEnd_4544025 : Nat := 2333268931046689214989915

theorem tailTrace_4544025 : CollatzResearch.WordTrace tailWord_4544025 prefixEnd_4544025 2333268931046689214989915 := by
  unfold tailWord_4544025
  simp only [CollatzResearch.WordTrace]
  refine ⟨165734207362780957530001529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110489471575187305020001019 165734207362780957530001529)
  ·
    refine ⟨124300655522085718147501147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165734207362780957530001529 124300655522085718147501147)
    ·
      refine ⟨186450983283128577221251721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124300655522085718147501147 186450983283128577221251721)
      ·
        refine ⟨139838237462346432915938791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186450983283128577221251721 139838237462346432915938791)
        ·
          refine ⟨209757356193519649373908187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139838237462346432915938791 209757356193519649373908187)
          ·
            refine ⟨314636034290279474060862281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 209757356193519649373908187 314636034290279474060862281)
            ·
              refine ⟨235977025717709605545646711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 314636034290279474060862281 235977025717709605545646711)
              ·
                refine ⟨353965538576564408318470067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 235977025717709605545646711 353965538576564408318470067)
                ·
                  refine ⟨530948307864846612477705101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 353965538576564408318470067 530948307864846612477705101)
                  ·
                    refine ⟨199105615449317479679139413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 530948307864846612477705101 199105615449317479679139413)
                    ·
                      refine ⟨2333268931046689214989915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 199105615449317479679139413 2333268931046689214989915)
                      ·
                        rfl

theorem cell23_4544025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 3, 8].length) (baseStart_4544025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4544025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4544025 prefixEnd_4544025 := by exact prefixLift 4544025
  have htrace : WordTrace (prefixWord ++ tailWord_4544025) baseStart_4544025 baseEnd_4544025 := by
    simpa [prefixWord, tailWord_4544025, baseEnd_4544025] using wordTrace_append hprefix tailTrace_4544025
  have hstable : (prefixWord ++ tailWord_4544025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4544025).length < 2 ^ (prefixWord ++ tailWord_4544025).sum := by decide
  have hdescent : baseEnd_4544025 < baseStart_4544025 := by decide
  rcases family_descends (prefixWord ++ tailWord_4544025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4544056 : List Nat := [2, 1, 2, 1, 4, 4, 1, 3, 5]
def baseStart_4544056 : Nat := 118140960795 + 4544056 * 2 ^ 59
def prefixEnd_4544056 : Nat := 4983230072969 + 3 ^ 40 * 4544056 * 2
def baseEnd_4544056 : Nat := 259253872105219843744697

theorem tailTrace_4544056 : CollatzResearch.WordTrace tailWord_4544056 prefixEnd_4544056 259253872105219843744697 := by
  unfold tailWord_4544056
  simp only [CollatzResearch.WordTrace]
  refine ⟨82867669012834324912190011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110490225350445766549586681 82867669012834324912190011)
  ·
    refine ⟨124301503519251487368285017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82867669012834324912190011 124301503519251487368285017)
    ·
      refine ⟨93226127639438615526213763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124301503519251487368285017 93226127639438615526213763)
      ·
        refine ⟨139839191459157923289320645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93226127639438615526213763 139839191459157923289320645)
        ·
          refine ⟨26219848398592110616747621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 139839191459157923289320645 26219848398592110616747621)
          ·
            refine ⟨4916221574736020740640179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26219848398592110616747621 4916221574736020740640179)
            ·
              refine ⟨7374332362104031110960269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4916221574736020740640179 7374332362104031110960269)
              ·
                refine ⟨2765374635789011666610101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7374332362104031110960269 2765374635789011666610101)
                ·
                  refine ⟨259253872105219843744697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2765374635789011666610101 259253872105219843744697)
                  ·
                    rfl

theorem cell23_4544056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 3, 5].length) (baseStart_4544056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4544056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4544056 prefixEnd_4544056 := by exact prefixLift 4544056
  have htrace : WordTrace (prefixWord ++ tailWord_4544056) baseStart_4544056 baseEnd_4544056 := by
    simpa [prefixWord, tailWord_4544056, baseEnd_4544056] using wordTrace_append hprefix tailTrace_4544056
  have hstable : (prefixWord ++ tailWord_4544056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4544056).length < 2 ^ (prefixWord ++ tailWord_4544056).sum := by decide
  have hdescent : baseEnd_4544056 < baseStart_4544056 := by decide
  rcases family_descends (prefixWord ++ tailWord_4544056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4544089 : List Nat := [1, 2, 1, 2, 2, 1, 1, 5, 2, 4, 2]
def baseStart_4544089 : Nat := 118140960795 + 4544089 * 2 ^ 59
def prefixEnd_4544089 : Nat := 4983230072969 + 3 ^ 40 * 4544089 * 2
def baseEnd_4544089 : Nat := 2333301793808576964589621

theorem tailTrace_4544089 : CollatzResearch.WordTrace tailWord_4544089 prefixEnd_4544089 2333301793808576964589621 := by
  unfold tailWord_4544089
  simp only [CollatzResearch.WordTrace]
  refine ⟨165736541634549096460331321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110491027756366064306887547 165736541634549096460331321)
  ·
    refine ⟨124302406225911822345248491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165736541634549096460331321 124302406225911822345248491)
    ·
      refine ⟨186453609338867733517872737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124302406225911822345248491 186453609338867733517872737)
      ·
        refine ⟨139840207004150800138404553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186453609338867733517872737 139840207004150800138404553)
        ·
          refine ⟨104880155253113100103803415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139840207004150800138404553 104880155253113100103803415)
          ·
            refine ⟨157320232879669650155705123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104880155253113100103803415 157320232879669650155705123)
            ·
              refine ⟨235980349319504475233557685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157320232879669650155705123 235980349319504475233557685)
              ·
                refine ⟨22123157748703544553146033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 235980349319504475233557685 22123157748703544553146033)
                ·
                  refine ⟨16592368311527658414859525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22123157748703544553146033 16592368311527658414859525)
                  ·
                    refine ⟨3111069058411435952786161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16592368311527658414859525 3111069058411435952786161)
                    ·
                      refine ⟨2333301793808576964589621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3111069058411435952786161 2333301793808576964589621)
                      ·
                        rfl

theorem cell23_4544089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 5, 2, 4, 2].length) (baseStart_4544089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4544089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4544089 prefixEnd_4544089 := by exact prefixLift 4544089
  have htrace : WordTrace (prefixWord ++ tailWord_4544089) baseStart_4544089 baseEnd_4544089 := by
    simpa [prefixWord, tailWord_4544089, baseEnd_4544089] using wordTrace_append hprefix tailTrace_4544089
  have hstable : (prefixWord ++ tailWord_4544089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4544089).length < 2 ^ (prefixWord ++ tailWord_4544089).sum := by decide
  have hdescent : baseEnd_4544089 < baseStart_4544089 := by decide
  rcases family_descends (prefixWord ++ tailWord_4544089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4544106 : List Nat := [3, 1, 3, 2, 1, 3, 2, 1, 2, 1, 4]
def baseStart_4544106 : Nat := 118140960795 + 4544106 * 2 ^ 59
def prefixEnd_4544106 : Nat := 4983230072969 + 3 ^ 40 * 4544106 * 2
def baseEnd_4544106 : Nat := 2333310522979703398077043

theorem tailTrace_4544106 : CollatzResearch.WordTrace tailWord_4544106 prefixEnd_4544106 2333310522979703398077043 := by
  unfold tailWord_4544106
  simp only [CollatzResearch.WordTrace]
  refine ⟨41434290418871877090925043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110491441116991672242466781 41434290418871877090925043)
  ·
    refine ⟨62151435628307815636387565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41434290418871877090925043 62151435628307815636387565)
    ·
      refine ⟨23306788360615430863645337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62151435628307815636387565 23306788360615430863645337)
      ·
        refine ⟨17480091270461573147734003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23306788360615430863645337 17480091270461573147734003)
        ·
          refine ⟨26220136905692359721601005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17480091270461573147734003 26220136905692359721601005)
          ·
            refine ⟨9832551339634634895600377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26220136905692359721601005 9832551339634634895600377)
            ·
              refine ⟨7374413504725976171700283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9832551339634634895600377 7374413504725976171700283)
              ·
                refine ⟨11061620257088964257550425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7374413504725976171700283 11061620257088964257550425)
                ·
                  refine ⟨8296215192816723193162819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11061620257088964257550425 8296215192816723193162819)
                  ·
                    refine ⟨12444322789225084789744229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8296215192816723193162819 12444322789225084789744229)
                    ·
                      refine ⟨2333310522979703398077043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12444322789225084789744229 2333310522979703398077043)
                      ·
                        rfl

theorem cell23_4544106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_4544106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4544106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4544106 prefixEnd_4544106 := by exact prefixLift 4544106
  have htrace : WordTrace (prefixWord ++ tailWord_4544106) baseStart_4544106 baseEnd_4544106 := by
    simpa [prefixWord, tailWord_4544106, baseEnd_4544106] using wordTrace_append hprefix tailTrace_4544106
  have hstable : (prefixWord ++ tailWord_4544106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4544106).length < 2 ^ (prefixWord ++ tailWord_4544106).sum := by decide
  have hdescent : baseEnd_4544106 < baseStart_4544106 := by decide
  rcases family_descends (prefixWord ++ tailWord_4544106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4544129 : List Nat := [1, 2, 4, 2, 1, 2, 1, 4, 6]
def baseStart_4544129 : Nat := 118140960795 + 4544129 * 2 ^ 59
def prefixEnd_4544129 : Nat := 4983230072969 + 3 ^ 40 * 4544129 * 2
def baseEnd_4544129 : Nat := 259258037003861867565493

theorem tailTrace_4544129 : CollatzResearch.WordTrace tailWord_4544129 prefixEnd_4544129 259258037003861867565493 := by
  unfold tailWord_4544129
  simp only [CollatzResearch.WordTrace]
  refine ⟨165738000554404183291787441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110492000369602788861191627 165738000554404183291787441)
  ·
    refine ⟨124303500415803137468840581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165738000554404183291787441 124303500415803137468840581)
    ·
      refine ⟨23306906327963088275407609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 124303500415803137468840581 23306906327963088275407609)
      ·
        refine ⟨17480179745972316206555707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23306906327963088275407609 17480179745972316206555707)
        ·
          refine ⟨26220269618958474309833561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17480179745972316206555707 26220269618958474309833561)
          ·
            refine ⟨19665202214218855732375171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26220269618958474309833561 19665202214218855732375171)
            ·
              refine ⟨29497803321328283598562757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19665202214218855732375171 29497803321328283598562757)
              ·
                refine ⟨5530838122749053174730517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29497803321328283598562757 5530838122749053174730517)
                ·
                  refine ⟨259258037003861867565493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5530838122749053174730517 259258037003861867565493)
                  ·
                    rfl

theorem cell23_4544129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 4, 6].length) (baseStart_4544129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4544129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4544129 prefixEnd_4544129 := by exact prefixLift 4544129
  have htrace : WordTrace (prefixWord ++ tailWord_4544129) baseStart_4544129 baseEnd_4544129 := by
    simpa [prefixWord, tailWord_4544129, baseEnd_4544129] using wordTrace_append hprefix tailTrace_4544129
  have hstable : (prefixWord ++ tailWord_4544129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4544129).length < 2 ^ (prefixWord ++ tailWord_4544129).sum := by decide
  have hdescent : baseEnd_4544129 < baseStart_4544129 := by decide
  rcases family_descends (prefixWord ++ tailWord_4544129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4544176 : List Nat := [2, 1, 1, 1, 2, 1, 8, 1, 1, 5]
def baseStart_4544176 : Nat := 118140960795 + 4544176 * 2 ^ 59
def prefixEnd_4544176 : Nat := 4983230072969 + 3 ^ 40 * 4544176 * 2
def baseEnd_4544176 : Nat := 777782155541839374733907

theorem tailTrace_4544176 : CollatzResearch.WordTrace tailWord_4544176 prefixEnd_4544176 777782155541839374733907 := by
  unfold tailWord_4544176
  simp only [CollatzResearch.WordTrace]
  refine ⟨82869857392616955159374191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110493143190155940212498921 82869857392616955159374191)
  ·
    refine ⟨124304786088925432739061287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82869857392616955159374191 124304786088925432739061287)
    ·
      refine ⟨186457179133388149108591931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124304786088925432739061287 186457179133388149108591931)
      ·
        refine ⟨279685768700082223662887897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186457179133388149108591931 279685768700082223662887897)
        ·
          refine ⟨209764326525061667747165923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 279685768700082223662887897 209764326525061667747165923)
          ·
            refine ⟨314646489787592501620748885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 209764326525061667747165923 314646489787592501620748885)
            ·
              refine ⟨3687263552198349628368151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 314646489787592501620748885 3687263552198349628368151)
              ·
                refine ⟨5530895328297524442552227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3687263552198349628368151 5530895328297524442552227)
                ·
                  refine ⟨8296342992446286663828341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5530895328297524442552227 8296342992446286663828341)
                  ·
                    refine ⟨777782155541839374733907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8296342992446286663828341 777782155541839374733907)
                    ·
                      rfl

theorem cell23_4544176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 8, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 8, 1, 1, 5].length) (baseStart_4544176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4544176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4544176 prefixEnd_4544176 := by exact prefixLift 4544176
  have htrace : WordTrace (prefixWord ++ tailWord_4544176) baseStart_4544176 baseEnd_4544176 := by
    simpa [prefixWord, tailWord_4544176, baseEnd_4544176] using wordTrace_append hprefix tailTrace_4544176
  have hstable : (prefixWord ++ tailWord_4544176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4544176).length < 2 ^ (prefixWord ++ tailWord_4544176).sum := by decide
  have hdescent : baseEnd_4544176 < baseStart_4544176 := by decide
  rcases family_descends (prefixWord ++ tailWord_4544176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4544190 : List Nat := [4, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3]
def baseStart_4544190 : Nat := 118140960795 + 4544190 * 2 ^ 59
def prefixEnd_4544190 : Nat := 4983230072969 + 3 ^ 40 * 4544190 * 2
def baseEnd_4544190 : Nat := 2333353655354681069426657

theorem tailTrace_4544190 : CollatzResearch.WordTrace tailWord_4544190 prefixEnd_4544190 2333353655354681069426657 := by
  unfold tailWord_4544190
  simp only [CollatzResearch.WordTrace]
  refine ⟨20717528175897898838719753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110493483604788793806505349 20717528175897898838719753)
  ·
    refine ⟨15538146131923424129039815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20717528175897898838719753 15538146131923424129039815)
    ·
      refine ⟨23307219197885136193559723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15538146131923424129039815 23307219197885136193559723)
      ·
        refine ⟨34960828796827704290339585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23307219197885136193559723 34960828796827704290339585)
        ·
          refine ⟨26220621597620778217754689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34960828796827704290339585 26220621597620778217754689)
          ·
            refine ⟨19665466198215583663316017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26220621597620778217754689 19665466198215583663316017)
            ·
              refine ⟨14749099648661687747487013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19665466198215583663316017 14749099648661687747487013)
              ·
                refine ⟨2765456184124066452653815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14749099648661687747487013 2765456184124066452653815)
                ·
                  refine ⟨4148184276186099678980723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2765456184124066452653815 4148184276186099678980723)
                  ·
                    refine ⟨6222276414279149518471085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4148184276186099678980723 6222276414279149518471085)
                    ·
                      refine ⟨2333353655354681069426657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6222276414279149518471085 2333353655354681069426657)
                      ·
                        rfl

theorem cell23_4544190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3].length) (baseStart_4544190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4544190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4544190 prefixEnd_4544190 := by exact prefixLift 4544190
  have htrace : WordTrace (prefixWord ++ tailWord_4544190) baseStart_4544190 baseEnd_4544190 := by
    simpa [prefixWord, tailWord_4544190, baseEnd_4544190] using wordTrace_append hprefix tailTrace_4544190
  have hstable : (prefixWord ++ tailWord_4544190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4544190).length < 2 ^ (prefixWord ++ tailWord_4544190).sum := by decide
  have hdescent : baseEnd_4544190 < baseStart_4544190 := by decide
  rcases family_descends (prefixWord ++ tailWord_4544190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4544199 : List Nat := [1, 1, 4, 1, 1, 1, 5, 2, 1, 1, 5]
def baseStart_4544199 : Nat := 118140960795 + 4544199 * 2 ^ 59
def prefixEnd_4544199 : Nat := 4983230072969 + 3 ^ 40 * 4544199 * 2
def baseEnd_4544199 : Nat := 2333358276680571534214115

theorem tailTrace_4544199 : CollatzResearch.WordTrace tailWord_4544199 prefixEnd_4544199 2333358276680571534214115 := by
  unfold tailWord_4544199
  simp only [CollatzResearch.WordTrace]
  refine ⟨165740553664150585246835651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110493702442767056831223767 165740553664150585246835651)
  ·
    refine ⟨248610830496225877870253477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165740553664150585246835651 248610830496225877870253477)
    ·
      refine ⟨46614530718042352100672527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 248610830496225877870253477 46614530718042352100672527)
      ·
        refine ⟨69921796077063528151008791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46614530718042352100672527 69921796077063528151008791)
        ·
          refine ⟨104882694115595292226513187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69921796077063528151008791 104882694115595292226513187)
          ·
            refine ⟨157324041173392938339769781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104882694115595292226513187 157324041173392938339769781)
            ·
              refine ⟨14749128860005587969353417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 157324041173392938339769781 14749128860005587969353417)
              ·
                refine ⟨11061846645004190977015063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14749128860005587969353417 11061846645004190977015063)
                ·
                  refine ⟨16592769967506286465522595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11061846645004190977015063 16592769967506286465522595)
                  ·
                    refine ⟨24889154951259429698283893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16592769967506286465522595 24889154951259429698283893)
                    ·
                      refine ⟨2333358276680571534214115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24889154951259429698283893 2333358276680571534214115)
                      ·
                        rfl

theorem cell23_4544199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 2, 1, 1, 5].length) (baseStart_4544199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4544199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4544199 prefixEnd_4544199 := by exact prefixLift 4544199
  have htrace : WordTrace (prefixWord ++ tailWord_4544199) baseStart_4544199 baseEnd_4544199 := by
    simpa [prefixWord, tailWord_4544199, baseEnd_4544199] using wordTrace_append hprefix tailTrace_4544199
  have hstable : (prefixWord ++ tailWord_4544199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4544199).length < 2 ^ (prefixWord ++ tailWord_4544199).sum := by decide
  have hdescent : baseEnd_4544199 < baseStart_4544199 := by decide
  rcases family_descends (prefixWord ++ tailWord_4544199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4544209 : List Nat := [1, 2, 2, 1, 2, 5, 1, 1, 1, 1, 6]
def baseStart_4544209 : Nat := 118140960795 + 4544209 * 2 ^ 59
def prefixEnd_4544209 : Nat := 4983230072969 + 3 ^ 40 * 4544209 * 2
def baseEnd_4544209 : Nat := 2333363411487116495089069

theorem tailTrace_4544209 : CollatzResearch.WordTrace tailWord_4544209 prefixEnd_4544209 2333363411487116495089069 := by
  unfold tailWord_4544209
  simp only [CollatzResearch.WordTrace]
  refine ⟨165740918394114356954699681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110493945596076237969799787 165740918394114356954699681)
  ·
    refine ⟨124305688795585767716024761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165740918394114356954699681 124305688795585767716024761)
    ·
      refine ⟨93229266596689325787018571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124305688795585767716024761 93229266596689325787018571)
      ·
        refine ⟨139843899895033988680527857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93229266596689325787018571 139843899895033988680527857)
        ·
          refine ⟨104882924921275491510395893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139843899895033988680527857 104882924921275491510395893)
          ·
            refine ⟨9832774211369577329099615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 104882924921275491510395893 9832774211369577329099615)
            ·
              refine ⟨14749161317054365993649423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9832774211369577329099615 14749161317054365993649423)
              ·
                refine ⟨22123741975581548990474135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14749161317054365993649423 22123741975581548990474135)
                ·
                  refine ⟨33185612963372323485711203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22123741975581548990474135 33185612963372323485711203)
                  ·
                    refine ⟨49778419445058485228566805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33185612963372323485711203 49778419445058485228566805)
                    ·
                      refine ⟨2333363411487116495089069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49778419445058485228566805 2333363411487116495089069)
                      ·
                        rfl

theorem cell23_4544209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 1, 1, 1, 6].length) (baseStart_4544209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4544209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4544209 prefixEnd_4544209 := by exact prefixLift 4544209
  have htrace : WordTrace (prefixWord ++ tailWord_4544209) baseStart_4544209 baseEnd_4544209 := by
    simpa [prefixWord, tailWord_4544209, baseEnd_4544209] using wordTrace_append hprefix tailTrace_4544209
  have hstable : (prefixWord ++ tailWord_4544209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4544209).length < 2 ^ (prefixWord ++ tailWord_4544209).sum := by decide
  have hdescent : baseEnd_4544209 < baseStart_4544209 := by decide
  rcases family_descends (prefixWord ++ tailWord_4544209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4544256 : List Nat := [2, 1, 1, 2, 1, 1, 2, 3, 5, 3, 2]
def baseStart_4544256 : Nat := 118140960795 + 4544256 * 2 ^ 59
def prefixEnd_4544256 : Nat := 4983230072969 + 3 ^ 40 * 4544256 * 2
def baseEnd_4544256 : Nat := 2333387545077877811201353

theorem tailTrace_4544256 : CollatzResearch.WordTrace tailWord_4544256 prefixEnd_4544256 2333387545077877811201353 := by
  unfold tailWord_4544256
  simp only [CollatzResearch.WordTrace]
  refine ⟨82871316312472041990830311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110495088416629389321107081 82871316312472041990830311)
  ·
    refine ⟨124306974468708062986245467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82871316312472041990830311 124306974468708062986245467)
    ·
      refine ⟨186460461703062094479368201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124306974468708062986245467 186460461703062094479368201)
      ·
        refine ⟨139845346277296570859526151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186460461703062094479368201 139845346277296570859526151)
        ·
          refine ⟨209768019415944856289289227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139845346277296570859526151 209768019415944856289289227)
          ·
            refine ⟨314652029123917284433933841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 209768019415944856289289227 314652029123917284433933841)
            ·
              refine ⟨235989021842937963325450381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 314652029123917284433933841 235989021842937963325450381)
              ·
                refine ⟨88495883191101736247043893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 235989021842937963325450381 88495883191101736247043893)
                ·
                  refine ⟨8296489049165787773160365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 88495883191101736247043893 8296489049165787773160365)
                  ·
                    refine ⟨3111183393437170414935137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8296489049165787773160365 3111183393437170414935137)
                    ·
                      refine ⟨2333387545077877811201353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3111183393437170414935137 2333387545077877811201353)
                      ·
                        rfl

theorem cell23_4544256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 5, 3, 2].length) (baseStart_4544256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4544256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4544256 prefixEnd_4544256 := by exact prefixLift 4544256
  have htrace : WordTrace (prefixWord ++ tailWord_4544256) baseStart_4544256 baseEnd_4544256 := by
    simpa [prefixWord, tailWord_4544256, baseEnd_4544256] using wordTrace_append hprefix tailTrace_4544256
  have hstable : (prefixWord ++ tailWord_4544256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4544256).length < 2 ^ (prefixWord ++ tailWord_4544256).sum := by decide
  have hdescent : baseEnd_4544256 < baseStart_4544256 := by decide
  rcases family_descends (prefixWord ++ tailWord_4544256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4544306 : List Nat := [3, 2, 1, 1, 3, 2, 1, 1, 2, 4, 3]
def baseStart_4544306 : Nat := 118140960795 + 4544306 * 2 ^ 59
def prefixEnd_4544306 : Nat := 4983230072969 + 3 ^ 40 * 4544306 * 2
def baseEnd_4544306 : Nat := 2333413219110602615576123

theorem tailTrace_4544306 : CollatzResearch.WordTrace tailWord_4544306 prefixEnd_4544306 2333413219110602615576123 := by
  unfold tailWord_4544306
  simp only [CollatzResearch.WordTrace]
  refine ⟨41436114068690735630245193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110496304183175295013987181 41436114068690735630245193)
  ·
    refine ⟨31077085551518051722683895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41436114068690735630245193 31077085551518051722683895)
    ·
      refine ⟨46615628327277077584025843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31077085551518051722683895 46615628327277077584025843)
      ·
        refine ⟨69923442490915616376038765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46615628327277077584025843 69923442490915616376038765)
        ·
          refine ⟨26221290934093356141014537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69923442490915616376038765 26221290934093356141014537)
          ·
            refine ⟨19665968200570017105760903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26221290934093356141014537 19665968200570017105760903)
            ·
              refine ⟨29498952300855025658641355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19665968200570017105760903 29498952300855025658641355)
              ·
                refine ⟨44248428451282538487962033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29498952300855025658641355 44248428451282538487962033)
                ·
                  refine ⟨33186321338461903865971525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44248428451282538487962033 33186321338461903865971525)
                  ·
                    refine ⟨6222435250961606974869661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33186321338461903865971525 6222435250961606974869661)
                    ·
                      refine ⟨2333413219110602615576123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6222435250961606974869661 2333413219110602615576123)
                      ·
                        rfl

theorem cell23_4544306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 2, 4, 3].length) (baseStart_4544306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4544306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4544306 prefixEnd_4544306 := by exact prefixLift 4544306
  have htrace : WordTrace (prefixWord ++ tailWord_4544306) baseStart_4544306 baseEnd_4544306 := by
    simpa [prefixWord, tailWord_4544306, baseEnd_4544306] using wordTrace_append hprefix tailTrace_4544306
  have hstable : (prefixWord ++ tailWord_4544306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4544306).length < 2 ^ (prefixWord ++ tailWord_4544306).sum := by decide
  have hdescent : baseEnd_4544306 < baseStart_4544306 := by decide
  rcases family_descends (prefixWord ++ tailWord_4544306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4544313 : List Nat := [1, 2, 1, 7, 1, 1, 1, 1, 2, 6]
def baseStart_4544313 : Nat := 118140960795 + 4544313 * 2 ^ 59
def prefixEnd_4544313 : Nat := 4983230072969 + 3 ^ 40 * 4544313 * 2
def baseEnd_4544313 : Nat := 777805604491728029396197

theorem tailTrace_4544313 : CollatzResearch.WordTrace tailWord_4544313 prefixEnd_4544313 777805604491728029396197 := by
  unfold tailWord_4544313
  simp only [CollatzResearch.WordTrace]
  refine ⟨165744711585737582716485593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110496474390491721810990395 165744711585737582716485593)
  ·
    refine ⟨124308533689303187037364195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165744711585737582716485593 124308533689303187037364195)
    ·
      refine ⟨186462800533954780556046293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124308533689303187037364195 186462800533954780556046293)
      ·
        refine ⟨4370221887514565169282335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 186462800533954780556046293 4370221887514565169282335)
        ·
          refine ⟨6555332831271847753923503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4370221887514565169282335 6555332831271847753923503)
          ·
            refine ⟨9832999246907771630885255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6555332831271847753923503 9832999246907771630885255)
            ·
              refine ⟨14749498870361657446327883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9832999246907771630885255 14749498870361657446327883)
              ·
                refine ⟨22124248305542486169491825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14749498870361657446327883 22124248305542486169491825)
                ·
                  refine ⟨16593186229156864627118869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22124248305542486169491825 16593186229156864627118869)
                  ·
                    refine ⟨777805604491728029396197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16593186229156864627118869 777805604491728029396197)
                    ·
                      rfl

theorem cell23_4544313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 1, 2, 6].length) (baseStart_4544313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4544313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4544313 prefixEnd_4544313 := by exact prefixLift 4544313
  have htrace : WordTrace (prefixWord ++ tailWord_4544313) baseStart_4544313 baseEnd_4544313 := by
    simpa [prefixWord, tailWord_4544313, baseEnd_4544313] using wordTrace_append hprefix tailTrace_4544313
  have hstable : (prefixWord ++ tailWord_4544313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4544313).length < 2 ^ (prefixWord ++ tailWord_4544313).sum := by decide
  have hdescent : baseEnd_4544313 < baseStart_4544313 := by decide
  rcases family_descends (prefixWord ++ tailWord_4544313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4544354 : List Nat := [3, 3, 2, 1, 2, 3, 1, 2, 2, 2, 2]
def baseStart_4544354 : Nat := 118140960795 + 4544354 * 2 ^ 59
def prefixEnd_4544354 : Nat := 4983230072969 + 3 ^ 40 * 4544354 * 2
def baseEnd_4544354 : Nat := 2333437866182018427775903

theorem tailTrace_4544354 : CollatzResearch.WordTrace tailWord_4544354 prefixEnd_4544354 2333437866182018427775903 := by
  unfold tailWord_4544354
  simp only [CollatzResearch.WordTrace]
  refine ⟨41436551744647261679682029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110497471319059364479152077 41436551744647261679682029)
  ·
    refine ⟨15538706904242723129880761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41436551744647261679682029 15538706904242723129880761)
    ·
      refine ⟨11654030178182042347410571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15538706904242723129880761 11654030178182042347410571)
      ·
        refine ⟨17481045267273063521115857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11654030178182042347410571 17481045267273063521115857)
        ·
          refine ⟨13110783950454797640836893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17481045267273063521115857 13110783950454797640836893)
          ·
            refine ⟨4916543981420549115313835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13110783950454797640836893 4916543981420549115313835)
            ·
              refine ⟨7374815972130823672970753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4916543981420549115313835 7374815972130823672970753)
              ·
                refine ⟨5531111979098117754728065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7374815972130823672970753 5531111979098117754728065)
                ·
                  refine ⟨4148333984323588316046049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5531111979098117754728065 4148333984323588316046049)
                  ·
                    refine ⟨3111250488242691237034537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4148333984323588316046049 3111250488242691237034537)
                    ·
                      refine ⟨2333437866182018427775903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3111250488242691237034537 2333437866182018427775903)
                      ·
                        rfl

theorem cell23_4544354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 2, 2, 2, 2].length) (baseStart_4544354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4544354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4544354 prefixEnd_4544354 := by exact prefixLift 4544354
  have htrace : WordTrace (prefixWord ++ tailWord_4544354) baseStart_4544354 baseEnd_4544354 := by
    simpa [prefixWord, tailWord_4544354, baseEnd_4544354] using wordTrace_append hprefix tailTrace_4544354
  have hstable : (prefixWord ++ tailWord_4544354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4544354).length < 2 ^ (prefixWord ++ tailWord_4544354).sum := by decide
  have hdescent : baseEnd_4544354 < baseStart_4544354 := by decide
  rcases family_descends (prefixWord ++ tailWord_4544354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4544413 : List Nat := [1, 4, 2, 1, 2, 2, 1, 1, 4, 2, 3]
def baseStart_4544413 : Nat := 118140960795 + 4544413 * 2 ^ 59
def prefixEnd_4544413 : Nat := 4983230072969 + 3 ^ 40 * 4544413 * 2
def baseEnd_4544413 : Nat := 2333468161540633696938131

theorem tailTrace_4544413 : CollatzResearch.WordTrace tailWord_4544413 prefixEnd_4544413 2333468161540633696938131 := by
  unfold tailWord_4544413
  simp only [CollatzResearch.WordTrace]
  refine ⟨165748358885375299795125893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110498905923583533196750595 165748358885375299795125893)
  ·
    refine ⟨31077817291007868711586105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 165748358885375299795125893 31077817291007868711586105)
    ·
      refine ⟨23308362968255901533689579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31077817291007868711586105 23308362968255901533689579)
      ·
        refine ⟨34962544452383852300534369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23308362968255901533689579 34962544452383852300534369)
        ·
          refine ⟨26221908339287889225400777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34962544452383852300534369 26221908339287889225400777)
          ·
            refine ⟨19666431254465916919050583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26221908339287889225400777 19666431254465916919050583)
            ·
              refine ⟨29499646881698875378575875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19666431254465916919050583 29499646881698875378575875)
              ·
                refine ⟨44249470322548313067863813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29499646881698875378575875 44249470322548313067863813)
                ·
                  refine ⟨8296775685477808700224465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44249470322548313067863813 8296775685477808700224465)
                  ·
                    refine ⟨6222581764108356525168349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8296775685477808700224465 6222581764108356525168349)
                    ·
                      refine ⟨2333468161540633696938131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6222581764108356525168349 2333468161540633696938131)
                      ·
                        rfl

theorem cell23_4544413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 4, 2, 3].length) (baseStart_4544413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4544413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4544413 prefixEnd_4544413 := by exact prefixLift 4544413
  have htrace : WordTrace (prefixWord ++ tailWord_4544413) baseStart_4544413 baseEnd_4544413 := by
    simpa [prefixWord, tailWord_4544413, baseEnd_4544413] using wordTrace_append hprefix tailTrace_4544413
  have hstable : (prefixWord ++ tailWord_4544413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4544413).length < 2 ^ (prefixWord ++ tailWord_4544413).sum := by decide
  have hdescent : baseEnd_4544413 < baseStart_4544413 := by decide
  rcases family_descends (prefixWord ++ tailWord_4544413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4544416 : List Nat := [2, 1, 1, 4, 1, 1, 1, 6, 6]
def baseStart_4544416 : Nat := 118140960795 + 4544416 * 2 ^ 59
def prefixEnd_4544416 : Nat := 4983230072969 + 3 ^ 40 * 4544416 * 2
def baseEnd_4544416 : Nat := 259274411331399687244513

theorem tailTrace_4544416 : CollatzResearch.WordTrace tailWord_4544416 prefixEnd_4544416 259274411331399687244513 := by
  unfold tailWord_4544416
  simp only [CollatzResearch.WordTrace]
  refine ⟨82874234152182215653742551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110498978869576287538323401 82874234152182215653742551)
  ·
    refine ⟨124311351228273323480613827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82874234152182215653742551 124311351228273323480613827)
    ·
      refine ⟨186467026842409985220920741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124311351228273323480613827 186467026842409985220920741)
      ·
        refine ⟨34962567532951872228922639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 186467026842409985220920741 34962567532951872228922639)
        ·
          refine ⟨52443851299427808343383959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34962567532951872228922639 52443851299427808343383959)
          ·
            refine ⟨78665776949141712515075939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52443851299427808343383959 78665776949141712515075939)
            ·
              refine ⟨117998665423712568772613909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78665776949141712515075939 117998665423712568772613909)
              ·
                refine ⟨5531187441736526661216277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 117998665423712568772613909 5531187441736526661216277)
                ·
                  refine ⟨259274411331399687244513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5531187441736526661216277 259274411331399687244513)
                  ·
                    rfl

theorem cell23_4544416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 6, 6].length) (baseStart_4544416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4544416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4544416 prefixEnd_4544416 := by exact prefixLift 4544416
  have htrace : WordTrace (prefixWord ++ tailWord_4544416) baseStart_4544416 baseEnd_4544416 := by
    simpa [prefixWord, tailWord_4544416, baseEnd_4544416] using wordTrace_append hprefix tailTrace_4544416
  have hstable : (prefixWord ++ tailWord_4544416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4544416).length < 2 ^ (prefixWord ++ tailWord_4544416).sum := by decide
  have hdescent : baseEnd_4544416 < baseStart_4544416 := by decide
  rcases family_descends (prefixWord ++ tailWord_4544416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4544420 : List Nat := [2, 3, 1, 2, 1, 5, 1, 1, 3, 4]
def baseStart_4544420 : Nat := 118140960795 + 4544420 * 2 ^ 59
def prefixEnd_4544420 : Nat := 4983230072969 + 3 ^ 40 * 4544420 * 2
def baseEnd_4544420 : Nat := 777823918635071723183533

theorem tailTrace_4544420 : CollatzResearch.WordTrace tailWord_4544420 prefixEnd_4544420 777823918635071723183533 := by
  unfold tailWord_4544420
  simp only [CollatzResearch.WordTrace]
  refine ⟨82874307098174969995315357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110499076130899959993753809 82874307098174969995315357)
  ·
    refine ⟨31077865161815613748243259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82874307098174969995315357 31077865161815613748243259)
    ·
      refine ⟨46616797742723420622364889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31077865161815613748243259 46616797742723420622364889)
      ·
        refine ⟨34962598307042565466773667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46616797742723420622364889 34962598307042565466773667)
        ·
          refine ⟨52443897460563848200160501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34962598307042565466773667 52443897460563848200160501)
          ·
            refine ⟨4916615386927860768765047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52443897460563848200160501 4916615386927860768765047)
            ·
              refine ⟨7374923080391791153147571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4916615386927860768765047 7374923080391791153147571)
              ·
                refine ⟨11062384620587686729721357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7374923080391791153147571 11062384620587686729721357)
                ·
                  refine ⟨4148394232720382523645509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11062384620587686729721357 4148394232720382523645509)
                  ·
                    refine ⟨777823918635071723183533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4148394232720382523645509 777823918635071723183533)
                    ·
                      rfl

theorem cell23_4544420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 1, 3, 4].length) (baseStart_4544420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4544420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4544420 prefixEnd_4544420 := by exact prefixLift 4544420
  have htrace : WordTrace (prefixWord ++ tailWord_4544420) baseStart_4544420 baseEnd_4544420 := by
    simpa [prefixWord, tailWord_4544420, baseEnd_4544420] using wordTrace_append hprefix tailTrace_4544420
  have hstable : (prefixWord ++ tailWord_4544420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4544420).length < 2 ^ (prefixWord ++ tailWord_4544420).sum := by decide
  have hdescent : baseEnd_4544420 < baseStart_4544420 := by decide
  rcases family_descends (prefixWord ++ tailWord_4544420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4544433 : List Nat := [1, 2, 2, 4, 2, 2, 1, 3, 6]
def baseStart_4544433 : Nat := 118140960795 + 4544433 * 2 ^ 59
def prefixEnd_4544433 : Nat := 4983230072969 + 3 ^ 40 * 4544433 * 2
def baseEnd_4544433 : Nat := 259275381239302624298671

theorem tailTrace_4544433 : CollatzResearch.WordTrace tailWord_4544433 prefixEnd_4544433 259275381239302624298671 := by
  unfold tailWord_4544433
  simp only [CollatzResearch.WordTrace]
  refine ⟨165749088345302843210853953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110499392230201895473902635 165749088345302843210853953)
  ·
    refine ⟨124311816258977132408140465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165749088345302843210853953 124311816258977132408140465)
    ·
      refine ⟨93233862194232849306105349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124311816258977132408140465 93233862194232849306105349)
      ·
        refine ⟨17481349161418659244894753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 93233862194232849306105349 17481349161418659244894753)
        ·
          refine ⟨13111011871063994433671065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17481349161418659244894753 13111011871063994433671065)
          ·
            refine ⟨9833258903297995825253299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13111011871063994433671065 9833258903297995825253299)
            ·
              refine ⟨14749888354946993737879949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9833258903297995825253299 14749888354946993737879949)
              ·
                refine ⟨5531208133105122651704981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14749888354946993737879949 5531208133105122651704981)
                ·
                  refine ⟨259275381239302624298671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5531208133105122651704981 259275381239302624298671)
                  ·
                    rfl

theorem cell23_4544433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 3, 6].length) (baseStart_4544433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4544433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4544433 prefixEnd_4544433 := by exact prefixLift 4544433
  have htrace : WordTrace (prefixWord ++ tailWord_4544433) baseStart_4544433 baseEnd_4544433 := by
    simpa [prefixWord, tailWord_4544433, baseEnd_4544433] using wordTrace_append hprefix tailTrace_4544433
  have hstable : (prefixWord ++ tailWord_4544433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4544433).length < 2 ^ (prefixWord ++ tailWord_4544433).sum := by decide
  have hdescent : baseEnd_4544433 < baseStart_4544433 := by decide
  rcases family_descends (prefixWord ++ tailWord_4544433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4544483 : List Nat := [1, 1, 1, 6, 1, 2, 1, 2, 3, 1, 4]
def baseStart_4544483 : Nat := 118140960795 + 4544483 * 2 ^ 59
def prefixEnd_4544483 : Nat := 4983230072969 + 3 ^ 40 * 4544483 * 2
def baseEnd_4544483 : Nat := 2333504105186448423062809

theorem tailTrace_4544483 : CollatzResearch.WordTrace tailWord_4544483 prefixEnd_4544483 2333504105186448423062809 := by
  unfold tailWord_4544483
  simp only [CollatzResearch.WordTrace]
  refine ⟨165750911995121701750174103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110500607996747801166782735 165750911995121701750174103)
  ·
    refine ⟨248626367992682552625261155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165750911995121701750174103 248626367992682552625261155)
    ·
      refine ⟨372939551989023828937891733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248626367992682552625261155 372939551989023828937891733)
      ·
        refine ⟨17481541499485491981463675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 372939551989023828937891733 17481541499485491981463675)
        ·
          refine ⟨26222312249228237972195513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17481541499485491981463675 26222312249228237972195513)
          ·
            refine ⟨19666734186921178479146635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26222312249228237972195513 19666734186921178479146635)
            ·
              refine ⟨29500101280381767718719953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19666734186921178479146635 29500101280381767718719953)
              ·
                refine ⟨22125075960286325789039965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29500101280381767718719953 22125075960286325789039965)
                ·
                  refine ⟨8296903485107372170889987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22125075960286325789039965 8296903485107372170889987)
                  ·
                    refine ⟨12445355227661058256334981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8296903485107372170889987 12445355227661058256334981)
                    ·
                      refine ⟨2333504105186448423062809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12445355227661058256334981 2333504105186448423062809)
                      ·
                        rfl

theorem cell23_4544483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_4544483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4544483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4544483 prefixEnd_4544483 := by exact prefixLift 4544483
  have htrace : WordTrace (prefixWord ++ tailWord_4544483) baseStart_4544483 baseEnd_4544483 := by
    simpa [prefixWord, tailWord_4544483, baseEnd_4544483] using wordTrace_append hprefix tailTrace_4544483
  have hstable : (prefixWord ++ tailWord_4544483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4544483).length < 2 ^ (prefixWord ++ tailWord_4544483).sum := by decide
  have hdescent : baseEnd_4544483 < baseStart_4544483 := by decide
  rcases family_descends (prefixWord ++ tailWord_4544483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4544496 : List Nat := [2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 6]
def baseStart_4544496 : Nat := 118140960795 + 4544496 * 2 ^ 59
def prefixEnd_4544496 : Nat := 4983230072969 + 3 ^ 40 * 4544496 * 2
def baseEnd_4544496 : Nat := 2333510780434956872200249

theorem tailTrace_4544496 : CollatzResearch.WordTrace tailWord_4544496 prefixEnd_4544496 2333510780434956872200249 := by
  unfold tailWord_4544496
  simp only [CollatzResearch.WordTrace]
  refine ⟨82875693072037302485198671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110500924096049736646931561 82875693072037302485198671)
  ·
    refine ⟨124313539608055953727798007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82875693072037302485198671 124313539608055953727798007)
    ·
      refine ⟨186470309412083930591697011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124313539608055953727798007 186470309412083930591697011)
      ·
        refine ⟨279705464118125895887545517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186470309412083930591697011 279705464118125895887545517)
        ·
          refine ⟨104889549044297210957829569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 279705464118125895887545517 104889549044297210957829569)
          ·
            refine ⟨78667161783222908218372177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104889549044297210957829569 78667161783222908218372177)
            ·
              refine ⟨59000371337417181163779133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78667161783222908218372177 59000371337417181163779133)
              ·
                refine ⟨22125139251531442936417175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59000371337417181163779133 22125139251531442936417175)
                ·
                  refine ⟨33187708877297164404625763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22125139251531442936417175 33187708877297164404625763)
                  ·
                    refine ⟨49781563315945746606938645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33187708877297164404625763 49781563315945746606938645)
                    ·
                      refine ⟨2333510780434956872200249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49781563315945746606938645 2333510780434956872200249)
                      ·
                        rfl

theorem cell23_4544496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 6].length) (baseStart_4544496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4544496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4544496 prefixEnd_4544496 := by exact prefixLift 4544496
  have htrace : WordTrace (prefixWord ++ tailWord_4544496) baseStart_4544496 baseEnd_4544496 := by
    simpa [prefixWord, tailWord_4544496, baseEnd_4544496] using wordTrace_append hprefix tailTrace_4544496
  have hstable : (prefixWord ++ tailWord_4544496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4544496).length < 2 ^ (prefixWord ++ tailWord_4544496).sum := by decide
  have hdescent : baseEnd_4544496 < baseStart_4544496 := by decide
  rcases family_descends (prefixWord ++ tailWord_4544496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4544510 : List Nat := [4, 2, 2, 2, 1, 1, 2, 2, 1, 6]
def baseStart_4544510 : Nat := 118140960795 + 4544510 * 2 ^ 59
def prefixEnd_4544510 : Nat := 4983230072969 + 3 ^ 40 * 4544510 * 2
def baseEnd_4544510 : Nat := 777839323054706605808395

theorem tailTrace_4544510 : CollatzResearch.WordTrace tailWord_4544510 prefixEnd_4544510 777839323054706605808395 := by
  unfold tailWord_4544510
  simp only [CollatzResearch.WordTrace]
  refine ⟨20718987095752985670175873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110501264510682590240937989 20718987095752985670175873)
  ·
    refine ⟨15539240321814739252631905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20718987095752985670175873 15539240321814739252631905)
    ·
      refine ⟨11654430241361054439473929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15539240321814739252631905 11654430241361054439473929)
      ·
        refine ⟨8740822681020790829605447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11654430241361054439473929 8740822681020790829605447)
        ·
          refine ⟨13111234021531186244408171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8740822681020790829605447 13111234021531186244408171)
          ·
            refine ⟨19666851032296779366612257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13111234021531186244408171 19666851032296779366612257)
            ·
              refine ⟨14750138274222584524959193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19666851032296779366612257 14750138274222584524959193)
              ·
                refine ⟨11062603705666938393719395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14750138274222584524959193 11062603705666938393719395)
                ·
                  refine ⟨16593905558500407590579093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11062603705666938393719395 16593905558500407590579093)
                  ·
                    refine ⟨777839323054706605808395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16593905558500407590579093 777839323054706605808395)
                    ·
                      rfl

theorem cell23_4544510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_4544510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4544510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4544510 prefixEnd_4544510 := by exact prefixLift 4544510
  have htrace : WordTrace (prefixWord ++ tailWord_4544510) baseStart_4544510 baseEnd_4544510 := by
    simpa [prefixWord, tailWord_4544510, baseEnd_4544510] using wordTrace_append hprefix tailTrace_4544510
  have hstable : (prefixWord ++ tailWord_4544510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4544510).length < 2 ^ (prefixWord ++ tailWord_4544510).sum := by decide
  have hdescent : baseEnd_4544510 < baseStart_4544510 := by decide
  rcases family_descends (prefixWord ++ tailWord_4544510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4544513 : List Nat := [1, 2, 4, 1, 2, 1, 1, 4, 1, 2, 4]
def baseStart_4544513 : Nat := 118140960795 + 4544513 * 2 ^ 59
def prefixEnd_4544513 : Nat := 4983230072969 + 3 ^ 40 * 4544513 * 2
def baseEnd_4544513 : Nat := 2333519509606083305687671

theorem tailTrace_4544513 : CollatzResearch.WordTrace tailWord_4544513 prefixEnd_4544513 2333519509606083305687671 := by
  unfold tailWord_4544513
  simp only [CollatzResearch.WordTrace]
  refine ⟨165752006185013016873766193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110501337456675344582510795 165752006185013016873766193)
  ·
    refine ⟨124314004638759762655324645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165752006185013016873766193 124314004638759762655324645)
    ·
      refine ⟨23308875869767455497873371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 124314004638759762655324645 23308875869767455497873371)
      ·
        refine ⟨34963313804651183246810057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23308875869767455497873371 34963313804651183246810057)
        ·
          refine ⟨26222485353488387435107543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34963313804651183246810057 26222485353488387435107543)
          ·
            refine ⟨39333728030232581152661315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26222485353488387435107543 39333728030232581152661315)
            ·
              refine ⟨59000592045348871728991973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39333728030232581152661315 59000592045348871728991973)
              ·
                refine ⟨11062611008502913449185995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59000592045348871728991973 11062611008502913449185995)
                ·
                  refine ⟨16593916512754370173778993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11062611008502913449185995 16593916512754370173778993)
                  ·
                    refine ⟨12445437384565777630334245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16593916512754370173778993 12445437384565777630334245)
                    ·
                      refine ⟨2333519509606083305687671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12445437384565777630334245 2333519509606083305687671)
                      ·
                        rfl

theorem cell23_4544513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_4544513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4544513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4544513 prefixEnd_4544513 := by exact prefixLift 4544513
  have htrace : WordTrace (prefixWord ++ tailWord_4544513) baseStart_4544513 baseEnd_4544513 := by
    simpa [prefixWord, tailWord_4544513, baseEnd_4544513] using wordTrace_append hprefix tailTrace_4544513
  have hstable : (prefixWord ++ tailWord_4544513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4544513).length < 2 ^ (prefixWord ++ tailWord_4544513).sum := by decide
  have hdescent : baseEnd_4544513 < baseStart_4544513 := by decide
  rcases family_descends (prefixWord ++ tailWord_4544513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4544517 : List Nat := [1, 3, 1, 1, 2, 6, 2, 1, 1, 1, 4]
def baseStart_4544517 : Nat := 118140960795 + 4544517 * 2 ^ 59
def prefixEnd_4544517 : Nat := 4983230072969 + 3 ^ 40 * 4544517 * 2
def baseEnd_4544517 : Nat := 2333521563528701290037653

theorem tailTrace_4544517 : CollatzResearch.WordTrace tailWord_4544517 prefixEnd_4544517 2333521563528701290037653 := by
  unfold tailWord_4544517
  simp only [CollatzResearch.WordTrace]
  refine ⟨165752152076998525556911805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110501434717999017037941203 165752152076998525556911805)
  ·
    refine ⟨62157057028874447083841927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165752152076998525556911805 62157057028874447083841927)
    ·
      refine ⟨93235585543311670625762891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62157057028874447083841927 93235585543311670625762891)
      ·
        refine ⟨139853378314967505938644337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93235585543311670625762891 139853378314967505938644337)
        ·
          refine ⟨104890033736225629453983253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139853378314967505938644337 104890033736225629453983253)
          ·
            refine ⟨4916720331385576380655465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 104890033736225629453983253 4916720331385576380655465)
            ·
              refine ⟨3687540248539182285491599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4916720331385576380655465 3687540248539182285491599)
              ·
                refine ⟨5531310372808773428237399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3687540248539182285491599 5531310372808773428237399)
                ·
                  refine ⟨8296965559213160142356099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5531310372808773428237399 8296965559213160142356099)
                  ·
                    refine ⟨12445448338819740213534149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8296965559213160142356099 12445448338819740213534149)
                    ·
                      refine ⟨2333521563528701290037653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12445448338819740213534149 2333521563528701290037653)
                      ·
                        rfl

theorem cell23_4544517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 2, 1, 1, 1, 4].length) (baseStart_4544517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4544517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4544517 prefixEnd_4544517 := by exact prefixLift 4544517
  have htrace : WordTrace (prefixWord ++ tailWord_4544517) baseStart_4544517 baseEnd_4544517 := by
    simpa [prefixWord, tailWord_4544517, baseEnd_4544517] using wordTrace_append hprefix tailTrace_4544517
  have hstable : (prefixWord ++ tailWord_4544517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4544517).length < 2 ^ (prefixWord ++ tailWord_4544517).sum := by decide
  have hdescent : baseEnd_4544517 < baseStart_4544517 := by decide
  rcases family_descends (prefixWord ++ tailWord_4544517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4544518 : List Nat := [6, 2, 1, 2, 2, 1, 1, 2, 6]
def baseStart_4544518 : Nat := 118140960795 + 4544518 * 2 ^ 59
def prefixEnd_4544518 : Nat := 4983230072969 + 3 ^ 40 * 4544518 * 2
def baseEnd_4544518 : Nat := 259280230778817309569461

theorem tailTrace_4544518 : CollatzResearch.WordTrace tailWord_4544518 prefixEnd_4544518 259280230778817309569461 := by
  unfold tailWord_4544518
  simp only [CollatzResearch.WordTrace]
  refine ⟨5179755892187340710240569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 110501459033329935151798805 5179755892187340710240569)
  ·
    refine ⟨3884816919140505532680427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5179755892187340710240569 3884816919140505532680427)
    ·
      refine ⟨5827225378710758299020641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3884816919140505532680427 5827225378710758299020641)
      ·
        refine ⟨4370419034033068724265481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5827225378710758299020641 4370419034033068724265481)
        ·
          refine ⟨3277814275524801543199111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4370419034033068724265481 3277814275524801543199111)
          ·
            refine ⟨4916721413287202314798667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3277814275524801543199111 4916721413287202314798667)
            ·
              refine ⟨7375082119930803472198001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4916721413287202314798667 7375082119930803472198001)
              ·
                refine ⟨5531311589948102604148501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7375082119930803472198001 5531311589948102604148501)
                ·
                  refine ⟨259280230778817309569461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5531311589948102604148501 259280230778817309569461)
                  ·
                    rfl

theorem cell23_4544518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_4544518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4544518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4544518 prefixEnd_4544518 := by exact prefixLift 4544518
  have htrace : WordTrace (prefixWord ++ tailWord_4544518) baseStart_4544518 baseEnd_4544518 := by
    simpa [prefixWord, tailWord_4544518, baseEnd_4544518] using wordTrace_append hprefix tailTrace_4544518
  have hstable : (prefixWord ++ tailWord_4544518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4544518).length < 2 ^ (prefixWord ++ tailWord_4544518).sum := by decide
  have hdescent : baseEnd_4544518 < baseStart_4544518 := by decide
  rcases family_descends (prefixWord ++ tailWord_4544518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4544520 : List Nat := [2, 1, 3, 2, 1, 2, 3, 3, 1, 2, 3]
def baseStart_4544520 : Nat := 118140960795 + 4544520 * 2 ^ 59
def prefixEnd_4544520 : Nat := 4983230072969 + 3 ^ 40 * 4544520 * 2
def baseEnd_4544520 : Nat := 2333523103970664778300139

theorem tailTrace_4544520 : CollatzResearch.WordTrace tailWord_4544520 prefixEnd_4544520 2333523103970664778300139 := by
  unfold tailWord_4544520
  simp only [CollatzResearch.WordTrace]
  refine ⟨82876130747993828534635507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110501507663991771379514009 82876130747993828534635507)
  ·
    refine ⟨124314196121990742801953261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82876130747993828534635507 124314196121990742801953261)
    ·
      refine ⟨46617823545746528550732473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124314196121990742801953261 46617823545746528550732473)
      ·
        refine ⟨34963367659309896413049355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46617823545746528550732473 34963367659309896413049355)
        ·
          refine ⟨52445051488964844619574033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34963367659309896413049355 52445051488964844619574033)
          ·
            refine ⟨39333788616723633464680525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52445051488964844619574033 39333788616723633464680525)
            ·
              refine ⟨14750170731271362549255197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39333788616723633464680525 14750170731271362549255197)
              ·
                refine ⟨5531314024226760955970699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14750170731271362549255197 5531314024226760955970699)
                ·
                  refine ⟨8296971036340141433956049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5531314024226760955970699 8296971036340141433956049)
                  ·
                    refine ⟨6222728277255106075467037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8296971036340141433956049 6222728277255106075467037)
                    ·
                      refine ⟨2333523103970664778300139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6222728277255106075467037 2333523103970664778300139)
                      ·
                        rfl

theorem cell23_4544520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 3, 1, 2, 3].length) (baseStart_4544520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4544520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4544520 prefixEnd_4544520 := by exact prefixLift 4544520
  have htrace : WordTrace (prefixWord ++ tailWord_4544520) baseStart_4544520 baseEnd_4544520 := by
    simpa [prefixWord, tailWord_4544520, baseEnd_4544520] using wordTrace_append hprefix tailTrace_4544520
  have hstable : (prefixWord ++ tailWord_4544520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4544520).length < 2 ^ (prefixWord ++ tailWord_4544520).sum := by decide
  have hdescent : baseEnd_4544520 < baseStart_4544520 := by decide
  rcases family_descends (prefixWord ++ tailWord_4544520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4544556 : List Nat := [2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 8]
def baseStart_4544556 : Nat := 118140960795 + 4544556 * 2 ^ 59
def prefixEnd_4544556 : Nat := 4983230072969 + 3 ^ 40 * 4544556 * 2
def baseEnd_4544556 : Nat := 2333541589274226637449973

theorem tailTrace_4544556 : CollatzResearch.WordTrace tailWord_4544556 prefixEnd_4544556 2333541589274226637449973 := by
  unfold tailWord_4544556
  simp only [CollatzResearch.WordTrace]
  refine ⟨82876787261928617608790761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110502383015904823478387681 82876787261928617608790761)
  ·
    refine ⟨62157590446446463206593071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82876787261928617608790761 62157590446446463206593071)
    ·
      refine ⟨93236385669669694809889607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62157590446446463206593071 93236385669669694809889607)
      ·
        refine ⟨139854578504504542214834411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93236385669669694809889607 139854578504504542214834411)
        ·
          refine ⟨209781867756756813322251617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139854578504504542214834411 209781867756756813322251617)
          ·
            refine ⟨157336400817567609991688713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 209781867756756813322251617 157336400817567609991688713)
            ·
              refine ⟨118002300613175707493766535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 157336400817567609991688713 118002300613175707493766535)
              ·
                refine ⟨177003450919763561240649803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118002300613175707493766535 177003450919763561240649803)
                ·
                  refine ⟨265505176379645341860974705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 177003450919763561240649803 265505176379645341860974705)
                  ·
                    refine ⟨199128882284734006395731029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 265505176379645341860974705 199128882284734006395731029)
                    ·
                      refine ⟨2333541589274226637449973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 199128882284734006395731029 2333541589274226637449973)
                      ·
                        rfl

theorem cell23_4544556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 8].length) (baseStart_4544556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4544556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4544556 prefixEnd_4544556 := by exact prefixLift 4544556
  have htrace : WordTrace (prefixWord ++ tailWord_4544556) baseStart_4544556 baseEnd_4544556 := by
    simpa [prefixWord, tailWord_4544556, baseEnd_4544556] using wordTrace_append hprefix tailTrace_4544556
  have hstable : (prefixWord ++ tailWord_4544556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4544556).length < 2 ^ (prefixWord ++ tailWord_4544556).sum := by decide
  have hdescent : baseEnd_4544556 < baseStart_4544556 := by decide
  rcases family_descends (prefixWord ++ tailWord_4544556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4544568 : List Nat := [2, 1, 2, 1, 7, 1, 1, 3, 1, 2, 2]
def baseStart_4544568 : Nat := 118140960795 + 4544568 * 2 ^ 59
def prefixEnd_4544568 : Nat := 4983230072969 + 3 ^ 40 * 4544568 * 2
def baseEnd_4544568 : Nat := 2333547751042080590499919

theorem tailTrace_4544568 : CollatzResearch.WordTrace tailWord_4544568 prefixEnd_4544568 2333547751042080590499919 := by
  unfold tailWord_4544568
  simp only [CollatzResearch.WordTrace]
  refine ⟨82877006099906880633509179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110502674799875840844678905 82877006099906880633509179)
  ·
    refine ⟨124315509149860320950263769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82877006099906880633509179 124315509149860320950263769)
    ·
      refine ⟨93236631862395240712697827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124315509149860320950263769 93236631862395240712697827)
      ·
        refine ⟨139854947793592861069046741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93236631862395240712697827 139854947793592861069046741)
        ·
          refine ⟨3277850338912332681305783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 139854947793592861069046741 3277850338912332681305783)
          ·
            refine ⟨4916775508368499021958675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3277850338912332681305783 4916775508368499021958675)
            ·
              refine ⟨7375163262552748532938013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4916775508368499021958675 7375163262552748532938013)
              ·
                refine ⟨2765686223457280699851755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7375163262552748532938013 2765686223457280699851755)
                ·
                  refine ⟨4148529335185921049777633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2765686223457280699851755 4148529335185921049777633)
                  ·
                    refine ⟨3111397001389440787333225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4148529335185921049777633 3111397001389440787333225)
                    ·
                      refine ⟨2333547751042080590499919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3111397001389440787333225 2333547751042080590499919)
                      ·
                        rfl

theorem cell23_4544568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 3, 1, 2, 2].length) (baseStart_4544568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4544568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4544568 prefixEnd_4544568 := by exact prefixLift 4544568
  have htrace : WordTrace (prefixWord ++ tailWord_4544568) baseStart_4544568 baseEnd_4544568 := by
    simpa [prefixWord, tailWord_4544568, baseEnd_4544568] using wordTrace_append hprefix tailTrace_4544568
  have hstable : (prefixWord ++ tailWord_4544568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4544568).length < 2 ^ (prefixWord ++ tailWord_4544568).sum := by decide
  have hdescent : baseEnd_4544568 < baseStart_4544568 := by decide
  rcases family_descends (prefixWord ++ tailWord_4544568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4544593 : List Nat := [1, 2, 2, 1, 3, 1, 1, 3, 2, 4, 3]
def baseStart_4544593 : Nat := 118140960795 + 4544593 * 2 ^ 59
def prefixEnd_4544593 : Nat := 4983230072969 + 3 ^ 40 * 4544593 * 2
def baseEnd_4544593 : Nat := 2333560588058442992687303

theorem tailTrace_4544593 : CollatzResearch.WordTrace tailWord_4544593 prefixEnd_4544593 2333560588058442992687303 := by
  unfold tailWord_4544593
  simp only [CollatzResearch.WordTrace]
  refine ⟨165754924024723190536678433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110503282683148793691118955 165754924024723190536678433)
  ·
    refine ⟨124316193018542392902508825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165754924024723190536678433 124316193018542392902508825)
    ·
      refine ⟨93237144763906794676881619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124316193018542392902508825 93237144763906794676881619)
      ·
        refine ⟨139855717145860192015322429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93237144763906794676881619 139855717145860192015322429)
        ·
          refine ⟨52445893929697572005745911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 139855717145860192015322429 52445893929697572005745911)
          ·
            refine ⟨78668840894546358008618867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52445893929697572005745911 78668840894546358008618867)
            ·
              refine ⟨118003261341819537012928301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78668840894546358008618867 118003261341819537012928301)
              ·
                refine ⟨44251223003182326379848113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 118003261341819537012928301 44251223003182326379848113)
                ·
                  refine ⟨33188417252386744784886085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44251223003182326379848113 33188417252386744784886085)
                  ·
                    refine ⟨6222828234822514647166141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33188417252386744784886085 6222828234822514647166141)
                    ·
                      refine ⟨2333560588058442992687303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6222828234822514647166141 2333560588058442992687303)
                      ·
                        rfl

theorem cell23_4544593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 2, 4, 3].length) (baseStart_4544593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4544593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4544593 prefixEnd_4544593 := by exact prefixLift 4544593
  have htrace : WordTrace (prefixWord ++ tailWord_4544593) baseStart_4544593 baseEnd_4544593 := by
    simpa [prefixWord, tailWord_4544593, baseEnd_4544593] using wordTrace_append hprefix tailTrace_4544593
  have hstable : (prefixWord ++ tailWord_4544593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4544593).length < 2 ^ (prefixWord ++ tailWord_4544593).sum := by decide
  have hdescent : baseEnd_4544593 < baseStart_4544593 := by decide
  rcases family_descends (prefixWord ++ tailWord_4544593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4544641 : List Nat := [1, 2, 4, 2, 3, 1, 2, 2, 2, 2, 2]
def baseStart_4544641 : Nat := 118140960795 + 4544641 * 2 ^ 59
def prefixEnd_4544641 : Nat := 4983230072969 + 3 ^ 40 * 4544641 * 2
def baseEnd_4544641 : Nat := 2333585235129858804887083

theorem tailTrace_4544641 : CollatzResearch.WordTrace tailWord_4544641 prefixEnd_4544641 2333585235129858804887083 := by
  unfold tailWord_4544641
  simp only [CollatzResearch.WordTrace]
  refine ⟨165756674728549294734425777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110504449819032863156283851 165756674728549294734425777)
  ·
    refine ⟨124317506046411971050819333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165756674728549294734425777 124317506046411971050819333)
    ·
      refine ⟨23309532383702244572028625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 124317506046411971050819333 23309532383702244572028625)
      ·
        refine ⟨17482149287776683429021469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23309532383702244572028625 17482149287776683429021469)
        ·
          refine ⟨6555805982916256285883051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17482149287776683429021469 6555805982916256285883051)
          ·
            refine ⟨9833708974374384428824577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6555805982916256285883051 9833708974374384428824577)
            ·
              refine ⟨7375281730780788321618433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9833708974374384428824577 7375281730780788321618433)
              ·
                refine ⟨5531461298085591241213825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7375281730780788321618433 5531461298085591241213825)
                ·
                  refine ⟨4148595973564193430910369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5531461298085591241213825 4148595973564193430910369)
                  ·
                    refine ⟨3111446980173145073182777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4148595973564193430910369 3111446980173145073182777)
                    ·
                      refine ⟨2333585235129858804887083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3111446980173145073182777 2333585235129858804887083)
                      ·
                        rfl

theorem cell23_4544641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 2, 2, 2, 2].length) (baseStart_4544641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4544641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4544641 prefixEnd_4544641 := by exact prefixLift 4544641
  have htrace : WordTrace (prefixWord ++ tailWord_4544641) baseStart_4544641 baseEnd_4544641 := by
    simpa [prefixWord, tailWord_4544641, baseEnd_4544641] using wordTrace_append hprefix tailTrace_4544641
  have hstable : (prefixWord ++ tailWord_4544641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4544641).length < 2 ^ (prefixWord ++ tailWord_4544641).sum := by decide
  have hdescent : baseEnd_4544641 < baseStart_4544641 := by decide
  rcases family_descends (prefixWord ++ tailWord_4544641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4544647 : List Nat := [1, 1, 4, 2, 1, 1, 6, 2, 5]
def baseStart_4544647 : Nat := 118140960795 + 4544647 * 2 ^ 59
def prefixEnd_4544647 : Nat := 4983230072969 + 3 ^ 40 * 4544647 * 2
def baseEnd_4544647 : Nat := 259287590668198420156895

theorem tailTrace_4544647 : CollatzResearch.WordTrace tailWord_4544647 prefixEnd_4544647 259287590668198420156895 := by
  unfold tailWord_4544647
  simp only [CollatzResearch.WordTrace]
  refine ⟨165756893566527557759144195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110504595711018371839429463 165756893566527557759144195)
  ·
    refine ⟨248635340349791336638716293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165756893566527557759144195 248635340349791336638716293)
    ·
      refine ⟨46619126315585875619759305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 248635340349791336638716293 46619126315585875619759305)
      ·
        refine ⟨34964344736689406714819479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46619126315585875619759305 34964344736689406714819479)
        ·
          refine ⟨52446517105034110072229219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34964344736689406714819479 52446517105034110072229219)
          ·
            refine ⟨78669775657551165108343829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52446517105034110072229219 78669775657551165108343829)
            ·
              refine ⟨3687645733947710864453617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 78669775657551165108343829 3687645733947710864453617)
              ·
                refine ⟨2765734300460783148340213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3687645733947710864453617 2765734300460783148340213)
                ·
                  refine ⟨259287590668198420156895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2765734300460783148340213 259287590668198420156895)
                  ·
                    rfl

theorem cell23_4544647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 6, 2, 5].length) (baseStart_4544647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4544647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4544647 prefixEnd_4544647 := by exact prefixLift 4544647
  have htrace : WordTrace (prefixWord ++ tailWord_4544647) baseStart_4544647 baseEnd_4544647 := by
    simpa [prefixWord, tailWord_4544647, baseEnd_4544647] using wordTrace_append hprefix tailTrace_4544647
  have hstable : (prefixWord ++ tailWord_4544647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4544647).length < 2 ^ (prefixWord ++ tailWord_4544647).sum := by decide
  have hdescent : baseEnd_4544647 < baseStart_4544647 := by decide
  rcases family_descends (prefixWord ++ tailWord_4544647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4544690 : List Nat := [3, 2, 1, 1, 1, 3, 1, 2, 5, 4]
def baseStart_4544690 : Nat := 118140960795 + 4544690 * 2 ^ 59
def prefixEnd_4544690 : Nat := 4983230072969 + 3 ^ 40 * 4544690 * 2
def baseEnd_4544690 : Nat := 777870131893976371058119

theorem tailTrace_4544690 : CollatzResearch.WordTrace tailWord_4544690 prefixEnd_4544690 777870131893976371058119 := by
  unfold tailWord_4544690
  simp only [CollatzResearch.WordTrace]
  refine ⟨41439615476342944025739881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110505641270247850735306349 41439615476342944025739881)
  ·
    refine ⟨31079711607257208019304911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41439615476342944025739881 31079711607257208019304911)
    ·
      refine ⟨46619567410885812028957367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31079711607257208019304911 46619567410885812028957367)
      ·
        refine ⟨69929351116328718043436051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46619567410885812028957367 69929351116328718043436051)
        ·
          refine ⟨104894026674493077065154077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69929351116328718043436051 104894026674493077065154077)
          ·
            refine ⟨39335260002934903899432779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 104894026674493077065154077 39335260002934903899432779)
            ·
              refine ⟨59002890004402355849149169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39335260002934903899432779 59002890004402355849149169)
              ·
                refine ⟨44252167503301766886861877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59002890004402355849149169 44252167503301766886861877)
                ·
                  refine ⟨4148640703434540645643301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44252167503301766886861877 4148640703434540645643301)
                  ·
                    refine ⟨777870131893976371058119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4148640703434540645643301 777870131893976371058119)
                    ·
                      rfl

theorem cell23_4544690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 5, 4].length) (baseStart_4544690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4544690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4544690 prefixEnd_4544690 := by exact prefixLift 4544690
  have htrace : WordTrace (prefixWord ++ tailWord_4544690) baseStart_4544690 baseEnd_4544690 := by
    simpa [prefixWord, tailWord_4544690, baseEnd_4544690] using wordTrace_append hprefix tailTrace_4544690
  have hstable : (prefixWord ++ tailWord_4544690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4544690).length < 2 ^ (prefixWord ++ tailWord_4544690).sum := by decide
  have hdescent : baseEnd_4544690 < baseStart_4544690 := by decide
  rcases family_descends (prefixWord ++ tailWord_4544690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4544692 : List Nat := [2, 5, 3, 1, 1, 2, 1, 2, 2, 2, 2]
def baseStart_4544692 : Nat := 118140960795 + 4544692 * 2 ^ 59
def prefixEnd_4544692 : Nat := 4983230072969 + 3 ^ 40 * 4544692 * 2
def baseEnd_4544692 : Nat := 2333611422643238105349349

theorem tailTrace_4544692 : CollatzResearch.WordTrace tailWord_4544692 prefixEnd_4544692 2333611422643238105349349 := by
  unfold tailWord_4544692
  simp only [CollatzResearch.WordTrace]
  refine ⟨82879267425682265222266165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110505689900909686963021553 82879267425682265222266165)
  ·
    refine ⟨7769931321157712364587453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 82879267425682265222266165 7769931321157712364587453)
    ·
      refine ⟨2913724245434142136720295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7769931321157712364587453 2913724245434142136720295)
      ·
        refine ⟨4370586368151213205080443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2913724245434142136720295 4370586368151213205080443)
        ·
          refine ⟨6555879552226819807620665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4370586368151213205080443 6555879552226819807620665)
          ·
            refine ⟨4916909664170114855715499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6555879552226819807620665 4916909664170114855715499)
            ·
              refine ⟨7375364496255172283573249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4916909664170114855715499 7375364496255172283573249)
              ·
                refine ⟨5531523372191379212679937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7375364496255172283573249 5531523372191379212679937)
                ·
                  refine ⟨4148642529143534409509953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5531523372191379212679937 4148642529143534409509953)
                  ·
                    refine ⟨3111481896857650807132465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4148642529143534409509953 3111481896857650807132465)
                    ·
                      refine ⟨2333611422643238105349349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3111481896857650807132465 2333611422643238105349349)
                      ·
                        rfl

theorem cell23_4544692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_4544692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4544692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4544692 prefixEnd_4544692 := by exact prefixLift 4544692
  have htrace : WordTrace (prefixWord ++ tailWord_4544692) baseStart_4544692 baseEnd_4544692 := by
    simpa [prefixWord, tailWord_4544692, baseEnd_4544692] using wordTrace_append hprefix tailTrace_4544692
  have hstable : (prefixWord ++ tailWord_4544692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4544692).length < 2 ^ (prefixWord ++ tailWord_4544692).sum := by decide
  have hdescent : baseEnd_4544692 < baseStart_4544692 := by decide
  rcases family_descends (prefixWord ++ tailWord_4544692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4544741 : List Nat := [1, 3, 1, 4, 2, 3, 1, 3, 1, 4]
def baseStart_4544741 : Nat := 118140960795 + 4544741 * 2 ^ 59
def prefixEnd_4544741 : Nat := 4983230072969 + 3 ^ 40 * 4544741 * 2
def baseEnd_4544741 : Nat := 777878861065102804545541

theorem tailTrace_4544741 : CollatzResearch.WordTrace tailWord_4544741 prefixEnd_4544741 777878861065102804545541 := by
  unfold tailWord_4544741
  simp only [CollatzResearch.WordTrace]
  refine ⟨165760322028187011813066077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110506881352124674542044051 165760322028187011813066077)
  ·
    refine ⟨62160120760570129429899779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165760322028187011813066077 62160120760570129429899779)
    ·
      refine ⟨93240181140855194144849669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62160120760570129429899779 93240181140855194144849669)
      ·
        refine ⟨17482533963910348902159313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 93240181140855194144849669 17482533963910348902159313)
        ·
          refine ⟨13111900472932761676619485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17482533963910348902159313 13111900472932761676619485)
          ·
            refine ⟨4916962677349785628732307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13111900472932761676619485 4916962677349785628732307)
            ·
              refine ⟨7375444016024678443098461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4916962677349785628732307 7375444016024678443098461)
              ·
                refine ⟨2765791506009254416161923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7375444016024678443098461 2765791506009254416161923)
                ·
                  refine ⟨4148687259013881624242885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2765791506009254416161923 4148687259013881624242885)
                  ·
                    refine ⟨777878861065102804545541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4148687259013881624242885 777878861065102804545541)
                    ·
                      rfl

theorem cell23_4544741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 3, 1, 4].length) (baseStart_4544741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4544741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4544741 prefixEnd_4544741 := by exact prefixLift 4544741
  have htrace : WordTrace (prefixWord ++ tailWord_4544741) baseStart_4544741 baseEnd_4544741 := by
    simpa [prefixWord, tailWord_4544741, baseEnd_4544741] using wordTrace_append hprefix tailTrace_4544741
  have hstable : (prefixWord ++ tailWord_4544741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4544741).length < 2 ^ (prefixWord ++ tailWord_4544741).sum := by decide
  have hdescent : baseEnd_4544741 < baseStart_4544741 := by decide
  rcases family_descends (prefixWord ++ tailWord_4544741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4544750 : List Nat := [4, 1, 2, 1, 1, 1, 1, 2, 5, 5]
def baseStart_4544750 : Nat := 118140960795 + 4544750 * 2 ^ 59
def prefixEnd_4544750 : Nat := 4983230072969 + 3 ^ 40 * 4544750 * 2
def baseEnd_4544750 : Nat := 777880401507066292808027

theorem tailTrace_4544750 : CollatzResearch.WordTrace tailWord_4544750 prefixEnd_4544750 777880401507066292808027 := by
  unfold tailWord_4544750
  simp only [CollatzResearch.WordTrace]
  refine ⟨20720081285644300793767963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110507100190102937566762469 20720081285644300793767963)
  ·
    refine ⟨31080121928466451190651945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20720081285644300793767963 31080121928466451190651945)
    ·
      refine ⟨23310091446349838392988959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31080121928466451190651945 23310091446349838392988959)
      ·
        refine ⟨34965137169524757589483439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23310091446349838392988959 34965137169524757589483439)
        ·
          refine ⟨52447705754287136384225159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34965137169524757589483439 52447705754287136384225159)
          ·
            refine ⟨78671558631430704576337739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52447705754287136384225159 78671558631430704576337739)
            ·
              refine ⟨118007337947146056864506609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78671558631430704576337739 118007337947146056864506609)
              ·
                refine ⟨88505503460359542648379957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 118007337947146056864506609 88505503460359542648379957)
                ·
                  refine ⟨8297390949408707123285621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 88505503460359542648379957 8297390949408707123285621)
                  ·
                    refine ⟨777880401507066292808027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8297390949408707123285621 777880401507066292808027)
                    ·
                      rfl

theorem cell23_4544750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 5, 5].length) (baseStart_4544750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4544750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4544750 prefixEnd_4544750 := by exact prefixLift 4544750
  have htrace : WordTrace (prefixWord ++ tailWord_4544750) baseStart_4544750 baseEnd_4544750 := by
    simpa [prefixWord, tailWord_4544750, baseEnd_4544750] using wordTrace_append hprefix tailTrace_4544750
  have hstable : (prefixWord ++ tailWord_4544750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4544750).length < 2 ^ (prefixWord ++ tailWord_4544750).sum := by decide
  have hdescent : baseEnd_4544750 < baseStart_4544750 := by decide
  rcases family_descends (prefixWord ++ tailWord_4544750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4544764 : List Nat := [2, 2, 2, 1, 4, 1, 3, 1, 3, 1, 3]
def baseStart_4544764 : Nat := 118140960795 + 4544764 * 2 ^ 59
def prefixEnd_4544764 : Nat := 4983230072969 + 3 ^ 40 * 4544764 * 2
def baseEnd_4544764 : Nat := 2333648393250361823649017

theorem tailTrace_4544764 : CollatzResearch.WordTrace tailWord_4544764 prefixEnd_4544764 2333648393250361823649017 := by
  unfold tailWord_4544764
  simp only [CollatzResearch.WordTrace]
  refine ⟨82880580453551843370576673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110507440604735791160768897 82880580453551843370576673)
  ·
    refine ⟨62160435340163882527932505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82880580453551843370576673 62160435340163882527932505)
    ·
      refine ⟨46620326505122911895949379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62160435340163882527932505 46620326505122911895949379)
      ·
        refine ⟨69930489757684367843924069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46620326505122911895949379 69930489757684367843924069)
        ·
          refine ⟨13111966829565818970735763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69930489757684367843924069 13111966829565818970735763)
          ·
            refine ⟨19667950244348728456103645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13111966829565818970735763 19667950244348728456103645)
            ·
              refine ⟨7375481341630773171038867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19667950244348728456103645 7375481341630773171038867)
              ·
                refine ⟨11063222012446159756558301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7375481341630773171038867 11063222012446159756558301)
                ·
                  refine ⟨4148708254667309908709363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11063222012446159756558301 4148708254667309908709363)
                  ·
                    refine ⟨6223062382000964863064045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4148708254667309908709363 6223062382000964863064045)
                    ·
                      refine ⟨2333648393250361823649017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6223062382000964863064045 2333648393250361823649017)
                      ·
                        rfl

theorem cell23_4544764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 1, 3, 1, 3].length) (baseStart_4544764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4544764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4544764 prefixEnd_4544764 := by exact prefixLift 4544764
  have htrace : WordTrace (prefixWord ++ tailWord_4544764) baseStart_4544764 baseEnd_4544764 := by
    simpa [prefixWord, tailWord_4544764, baseEnd_4544764] using wordTrace_append hprefix tailTrace_4544764
  have hstable : (prefixWord ++ tailWord_4544764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4544764).length < 2 ^ (prefixWord ++ tailWord_4544764).sum := by decide
  have hdescent : baseEnd_4544764 < baseStart_4544764 := by decide
  rcases family_descends (prefixWord ++ tailWord_4544764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4544780 : List Nat := [2, 2, 1, 2, 2, 2, 2, 3, 1, 6]
def baseStart_4544780 : Nat := 118140960795 + 4544780 * 2 ^ 59
def prefixEnd_4544780 : Nat := 4983230072969 + 3 ^ 40 * 4544780 * 2
def baseEnd_4544780 : Nat := 777885536313611253682981

theorem tailTrace_4544780 : CollatzResearch.WordTrace tailWord_4544780 prefixEnd_4544780 777885536313611253682981 := by
  unfold tailWord_4544780
  simp only [CollatzResearch.WordTrace]
  refine ⟨82880872237522860736867897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110507829650030480982490529 82880872237522860736867897)
  ·
    refine ⟨62160654178142145552650923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82880872237522860736867897 62160654178142145552650923)
    ·
      refine ⟨93240981267213218328976385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62160654178142145552650923 93240981267213218328976385)
      ·
        refine ⟨69930735950409913746732289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93240981267213218328976385 69930735950409913746732289)
        ·
          refine ⟨52448051962807435310049217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69930735950409913746732289 52448051962807435310049217)
          ·
            refine ⟨39336038972105576482536913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52448051962807435310049217 39336038972105576482536913)
            ·
              refine ⟨29502029229079182361902685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39336038972105576482536913 29502029229079182361902685)
              ·
                refine ⟨11063260960904693385713507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29502029229079182361902685 11063260960904693385713507)
                ·
                  refine ⟨16594891441357040078570261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11063260960904693385713507 16594891441357040078570261)
                  ·
                    refine ⟨777885536313611253682981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16594891441357040078570261 777885536313611253682981)
                    ·
                      rfl

theorem cell23_4544780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 3, 1, 6].length) (baseStart_4544780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4544780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4544780 prefixEnd_4544780 := by exact prefixLift 4544780
  have htrace : WordTrace (prefixWord ++ tailWord_4544780) baseStart_4544780 baseEnd_4544780 := by
    simpa [prefixWord, tailWord_4544780, baseEnd_4544780] using wordTrace_append hprefix tailTrace_4544780
  have hstable : (prefixWord ++ tailWord_4544780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4544780).length < 2 ^ (prefixWord ++ tailWord_4544780).sum := by decide
  have hdescent : baseEnd_4544780 < baseStart_4544780 := by decide
  rcases family_descends (prefixWord ++ tailWord_4544780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4544810 : List Nat := [3, 1, 4, 2, 13]
def baseStart_4544810 : Nat := 118140960795 + 4544810 * 2 ^ 59
def prefixEnd_4544810 : Nat := 4983230072969 + 3 ^ 40 * 4544810 * 2
def baseEnd_4544810 : Nat := 3201196177449202529045

theorem tailTrace_4544810 : CollatzResearch.WordTrace tailWord_4544810 prefixEnd_4544810 3201196177449202529045 := by
  unfold tailWord_4544810
  simp only [CollatzResearch.WordTrace]
  refine ⟨41440709666234259149331971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110508559109958024398218589 41440709666234259149331971)
  ·
    refine ⟨62161064499351388723997957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41440709666234259149331971 62161064499351388723997957)
    ·
      refine ⟨11655199593628385385749617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62161064499351388723997957 11655199593628385385749617)
      ·
        refine ⟨8741399695221289039312213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11655199593628385385749617 8741399695221289039312213)
        ·
          refine ⟨3201196177449202529045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 8741399695221289039312213 3201196177449202529045)
          ·
            rfl

theorem cell23_4544810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 13].length) (baseStart_4544810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4544810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4544810 prefixEnd_4544810 := by exact prefixLift 4544810
  have htrace : WordTrace (prefixWord ++ tailWord_4544810) baseStart_4544810 baseEnd_4544810 := by
    simpa [prefixWord, tailWord_4544810, baseEnd_4544810] using wordTrace_append hprefix tailTrace_4544810
  have hstable : (prefixWord ++ tailWord_4544810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4544810).length < 2 ^ (prefixWord ++ tailWord_4544810).sum := by decide
  have hdescent : baseEnd_4544810 < baseStart_4544810 := by decide
  rcases family_descends (prefixWord ++ tailWord_4544810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4544837 : List Nat := [1, 3, 1, 1, 1, 2, 1, 1, 8, 1, 3]
def baseStart_4544837 : Nat := 118140960795 + 4544837 * 2 ^ 59
def prefixEnd_4544837 : Nat := 4983230072969 + 3 ^ 40 * 4544837 * 2
def baseEnd_4544837 : Nat := 2333685877338140038036181

theorem tailTrace_4544837 : CollatzResearch.WordTrace tailWord_4544837 prefixEnd_4544837 2333685877338140038036181 := by
  unfold tailWord_4544837
  simp only [CollatzResearch.WordTrace]
  refine ⟨165763823435839220208560765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110509215623892813472373843 165763823435839220208560765)
  ·
    refine ⟨62161433788439707578210287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165763823435839220208560765 62161433788439707578210287)
    ·
      refine ⟨93242150682659561367315431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62161433788439707578210287 93242150682659561367315431)
      ·
        refine ⟨139863226023989342050973147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93242150682659561367315431 139863226023989342050973147)
        ·
          refine ⟨209794839035984013076459721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139863226023989342050973147 209794839035984013076459721)
          ·
            refine ⟨157346129276988009807344791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 209794839035984013076459721 157346129276988009807344791)
            ·
              refine ⟨236019193915482014711017187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157346129276988009807344791 236019193915482014711017187)
              ·
                refine ⟨354028790873223022066525781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 236019193915482014711017187 354028790873223022066525781)
                ·
                  refine ⟨4148774893045582289842099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 354028790873223022066525781 4148774893045582289842099)
                  ·
                    refine ⟨6223162339568373434763149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4148774893045582289842099 6223162339568373434763149)
                    ·
                      refine ⟨2333685877338140038036181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6223162339568373434763149 2333685877338140038036181)
                      ·
                        rfl

theorem cell23_4544837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 8, 1, 3].length) (baseStart_4544837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4544837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4544837 prefixEnd_4544837 := by exact prefixLift 4544837
  have htrace : WordTrace (prefixWord ++ tailWord_4544837) baseStart_4544837 baseEnd_4544837 := by
    simpa [prefixWord, tailWord_4544837, baseEnd_4544837] using wordTrace_append hprefix tailTrace_4544837
  have hstable : (prefixWord ++ tailWord_4544837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4544837).length < 2 ^ (prefixWord ++ tailWord_4544837).sum := by decide
  have hdescent : baseEnd_4544837 < baseStart_4544837 := by decide
  rcases family_descends (prefixWord ++ tailWord_4544837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4544871 : List Nat := [1, 1, 5, 1, 3, 1, 3, 2, 2, 1, 3]
def baseStart_4544871 : Nat := 118140960795 + 4544871 * 2 ^ 59
def prefixEnd_4544871 : Nat := 4983230072969 + 3 ^ 40 * 4544871 * 2
def baseEnd_4544871 : Nat := 2333703335680392905011025

theorem tailTrace_4544871 : CollatzResearch.WordTrace tailWord_4544871 prefixEnd_4544871 2333703335680392905011025 := by
  unfold tailWord_4544871
  simp only [CollatzResearch.WordTrace]
  refine ⟨165765063517716044015298467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110510042345144029343532311 165765063517716044015298467)
  ·
    refine ⟨248647595276574066022947701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165765063517716044015298467 248647595276574066022947701)
    ·
      refine ⟨23310712057178818689651347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 248647595276574066022947701 23310712057178818689651347)
      ·
        refine ⟨34966068085768228034477021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23310712057178818689651347 34966068085768228034477021)
        ·
          refine ⟨13112275532163085512928883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34966068085768228034477021 13112275532163085512928883)
          ·
            refine ⟨19668413298244628269393325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13112275532163085512928883 19668413298244628269393325)
            ·
              refine ⟨7375654986841735601022497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19668413298244628269393325 7375654986841735601022497)
              ·
                refine ⟨5531741240131301700766873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7375654986841735601022497 5531741240131301700766873)
                ·
                  refine ⟨4148805930098476275575155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5531741240131301700766873 4148805930098476275575155)
                  ·
                    refine ⟨6223208895147714413362733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4148805930098476275575155 6223208895147714413362733)
                    ·
                      refine ⟨2333703335680392905011025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6223208895147714413362733 2333703335680392905011025)
                      ·
                        rfl

theorem cell23_4544871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 2, 2, 1, 3].length) (baseStart_4544871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4544871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4544871 prefixEnd_4544871 := by exact prefixLift 4544871
  have htrace : WordTrace (prefixWord ++ tailWord_4544871) baseStart_4544871 baseEnd_4544871 := by
    simpa [prefixWord, tailWord_4544871, baseEnd_4544871] using wordTrace_append hprefix tailTrace_4544871
  have hstable : (prefixWord ++ tailWord_4544871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4544871).length < 2 ^ (prefixWord ++ tailWord_4544871).sum := by decide
  have hdescent : baseEnd_4544871 < baseStart_4544871 := by decide
  rcases family_descends (prefixWord ++ tailWord_4544871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4544945 : List Nat := [1, 2, 2, 4, 1, 4, 2, 1, 2, 2, 2]
def baseStart_4544945 : Nat := 118140960795 + 4544945 * 2 ^ 59
def prefixEnd_4544945 : Nat := 4983230072969 + 3 ^ 40 * 4544945 * 2
def baseEnd_4544945 : Nat := 2333741333248825615485685

theorem tailTrace_4544945 : CollatzResearch.WordTrace tailWord_4544945 prefixEnd_4544945 2333741333248825615485685 := by
  unfold tailWord_4544945
  simp only [CollatzResearch.WordTrace]
  refine ⟨165767762519447954653492289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110511841679631969768994859 165767762519447954653492289)
  ·
    refine ⟨124325821889585965990119217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165767762519447954653492289 124325821889585965990119217)
    ·
      refine ⟨93244366417189474492589413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124325821889585965990119217 93244366417189474492589413)
      ·
        refine ⟨17483318703223026467360515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 93244366417189474492589413 17483318703223026467360515)
        ·
          refine ⟨26224978054834539701040773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17483318703223026467360515 26224978054834539701040773)
          ·
            refine ⟨4917183385281476193945145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26224978054834539701040773 4917183385281476193945145)
            ·
              refine ⟨3687887538961107145458859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4917183385281476193945145 3687887538961107145458859)
              ·
                refine ⟨5531831308441660718188289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3687887538961107145458859 5531831308441660718188289)
                ·
                  refine ⟨4148873481331245538641217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5531831308441660718188289 4148873481331245538641217)
                  ·
                    refine ⟨3111655110998434153980913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4148873481331245538641217 3111655110998434153980913)
                    ·
                      refine ⟨2333741333248825615485685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3111655110998434153980913 2333741333248825615485685)
                      ·
                        rfl

theorem cell23_4544945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 2, 1, 2, 2, 2].length) (baseStart_4544945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4544945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4544945 prefixEnd_4544945 := by exact prefixLift 4544945
  have htrace : WordTrace (prefixWord ++ tailWord_4544945) baseStart_4544945 baseEnd_4544945 := by
    simpa [prefixWord, tailWord_4544945, baseEnd_4544945] using wordTrace_append hprefix tailTrace_4544945
  have hstable : (prefixWord ++ tailWord_4544945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4544945).length < 2 ^ (prefixWord ++ tailWord_4544945).sum := by decide
  have hdescent : baseEnd_4544945 < baseStart_4544945 := by decide
  rcases family_descends (prefixWord ++ tailWord_4544945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4544984 : List Nat := [2, 1, 2, 2, 2, 1, 1, 4, 2, 4, 2]
def baseStart_4544984 : Nat := 118140960795 + 4544984 * 2 ^ 59
def prefixEnd_4544984 : Nat := 4983230072969 + 3 ^ 40 * 4544984 * 2
def baseEnd_4544984 : Nat := 2333761358994350962898005

theorem tailTrace_4544984 : CollatzResearch.WordTrace tailWord_4544984 prefixEnd_4544984 2333761358994350962898005 := by
  unfold tailWord_4544984
  simp only [CollatzResearch.WordTrace]
  refine ⟨82884592483153332157081003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110512789977537776209441337 82884592483153332157081003)
  ·
    refine ⟨124326888724729998235621505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82884592483153332157081003 124326888724729998235621505)
    ·
      refine ⟨93245166543547498676716129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124326888724729998235621505 93245166543547498676716129)
      ·
        refine ⟨69933874907660624007537097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93245166543547498676716129 69933874907660624007537097)
        ·
          refine ⟨52450406180745468005652823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69933874907660624007537097 52450406180745468005652823)
          ·
            refine ⟨78675609271118202008479235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52450406180745468005652823 78675609271118202008479235)
            ·
              refine ⟨118013413906677303012718853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78675609271118202008479235 118013413906677303012718853)
              ·
                refine ⟨22127515107501994314884785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 118013413906677303012718853 22127515107501994314884785)
                ·
                  refine ⟨16595636330626495736163589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22127515107501994314884785 16595636330626495736163589)
                  ·
                    refine ⟨3111681811992467950530673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16595636330626495736163589 3111681811992467950530673)
                    ·
                      refine ⟨2333761358994350962898005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3111681811992467950530673 2333761358994350962898005)
                      ·
                        rfl

theorem cell23_4544984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 4, 2, 4, 2].length) (baseStart_4544984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4544984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4544984 prefixEnd_4544984 := by exact prefixLift 4544984
  have htrace : WordTrace (prefixWord ++ tailWord_4544984) baseStart_4544984 baseEnd_4544984 := by
    simpa [prefixWord, tailWord_4544984, baseEnd_4544984] using wordTrace_append hprefix tailTrace_4544984
  have hstable : (prefixWord ++ tailWord_4544984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4544984).length < 2 ^ (prefixWord ++ tailWord_4544984).sum := by decide
  have hdescent : baseEnd_4544984 < baseStart_4544984 := by decide
  rcases family_descends (prefixWord ++ tailWord_4544984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4545028 : List Nat := [2, 3, 2, 3, 1, 1, 1, 5, 1, 4]
def baseStart_4545028 : Nat := 118140960795 + 4545028 * 2 ^ 59
def prefixEnd_4545028 : Nat := 4983230072969 + 3 ^ 40 * 4545028 * 2
def baseEnd_4545028 : Nat := 777927984047716263582601

theorem tailTrace_4545028 : CollatzResearch.WordTrace tailWord_4545028 prefixEnd_4545028 777927984047716263582601 := by
  unfold tailWord_4545028
  simp only [CollatzResearch.WordTrace]
  refine ⟨82885394889073629914381869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110513859852098173219175825 82885394889073629914381869)
  ·
    refine ⟨31082023083402611217893201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82885394889073629914381869 31082023083402611217893201)
    ·
      refine ⟨23311517312551958413419901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31082023083402611217893201 23311517312551958413419901)
      ·
        refine ⟨8741818992206984405032463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23311517312551958413419901 8741818992206984405032463)
        ·
          refine ⟨13112728488310476607548695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8741818992206984405032463 13112728488310476607548695)
          ·
            refine ⟨19669092732465714911323043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13112728488310476607548695 19669092732465714911323043)
            ·
              refine ⟨29503639098698572366984565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19669092732465714911323043 29503639098698572366984565)
              ·
                refine ⟨2765966165502991159404803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29503639098698572366984565 2765966165502991159404803)
                ·
                  refine ⟨4148949248254486739107205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2765966165502991159404803 4148949248254486739107205)
                  ·
                    refine ⟨777927984047716263582601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4148949248254486739107205 777927984047716263582601)
                    ·
                      rfl

theorem cell23_4545028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 5, 1, 4].length) (baseStart_4545028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4545028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4545028 prefixEnd_4545028 := by exact prefixLift 4545028
  have htrace : WordTrace (prefixWord ++ tailWord_4545028) baseStart_4545028 baseEnd_4545028 := by
    simpa [prefixWord, tailWord_4545028, baseEnd_4545028] using wordTrace_append hprefix tailTrace_4545028
  have hstable : (prefixWord ++ tailWord_4545028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4545028).length < 2 ^ (prefixWord ++ tailWord_4545028).sum := by decide
  have hdescent : baseEnd_4545028 < baseStart_4545028 := by decide
  rcases family_descends (prefixWord ++ tailWord_4545028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4545074 : List Nat := [3, 2, 1, 1, 2, 1, 2, 3, 3, 1, 4]
def baseStart_4545074 : Nat := 118140960795 + 4545074 * 2 ^ 59
def prefixEnd_4545074 : Nat := 4983230072969 + 3 ^ 40 * 4545074 * 2
def baseEnd_4545074 : Nat := 2333807572253255610772591

theorem tailTrace_4545074 : CollatzResearch.WordTrace tailWord_4545074 prefixEnd_4545074 2333807572253255610772591 := by
  unfold tailWord_4545074
  simp only [CollatzResearch.WordTrace]
  refine ⟨41443116883995152421234569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110514978357320406456625517 41443116883995152421234569)
  ·
    refine ⟨31082337662996364315925927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41443116883995152421234569 31082337662996364315925927)
    ·
      refine ⟨46623506494494546473888891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31082337662996364315925927 46623506494494546473888891)
      ·
        refine ⟨69935259741741819710833337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46623506494494546473888891 69935259741741819710833337)
        ·
          refine ⟨52451444806306364783125003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69935259741741819710833337 52451444806306364783125003)
          ·
            refine ⟨78677167209459547174687505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52451444806306364783125003 78677167209459547174687505)
            ·
              refine ⟨59007875407094660381015629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78677167209459547174687505 59007875407094660381015629)
              ·
                refine ⟨22127953277660497642880861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59007875407094660381015629 22127953277660497642880861)
                ·
                  refine ⟨8297982479122686616080323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22127953277660497642880861 8297982479122686616080323)
                  ·
                    refine ⟨12446973718684029924120485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8297982479122686616080323 12446973718684029924120485)
                    ·
                      refine ⟨2333807572253255610772591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12446973718684029924120485 2333807572253255610772591)
                      ·
                        rfl

theorem cell23_4545074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 3, 3, 1, 4].length) (baseStart_4545074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4545074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4545074 prefixEnd_4545074 := by exact prefixLift 4545074
  have htrace : WordTrace (prefixWord ++ tailWord_4545074) baseStart_4545074 baseEnd_4545074 := by
    simpa [prefixWord, tailWord_4545074, baseEnd_4545074] using wordTrace_append hprefix tailTrace_4545074
  have hstable : (prefixWord ++ tailWord_4545074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4545074).length < 2 ^ (prefixWord ++ tailWord_4545074).sum := by decide
  have hdescent : baseEnd_4545074 < baseStart_4545074 := by decide
  rcases family_descends (prefixWord ++ tailWord_4545074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4545078 : List Nat := [5, 1, 2, 1, 2, 1, 2, 1, 1, 5, 2]
def baseStart_4545078 : Nat := 118140960795 + 4545078 * 2 ^ 59
def prefixEnd_4545078 : Nat := 4983230072969 + 3 ^ 40 * 4545078 * 2
def baseEnd_4545078 : Nat := 2333809626175873595122573

theorem tailTrace_4545078 : CollatzResearch.WordTrace tailWord_4545078 prefixEnd_4545078 2333809626175873595122573 := by
  unfold tailWord_4545078
  simp only [CollatzResearch.WordTrace]
  refine ⟨10360788339247882398005243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 110515075618644078912055925 10360788339247882398005243)
  ·
    refine ⟨15541182508871823597007865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10360788339247882398005243 15541182508871823597007865)
    ·
      refine ⟨11655886881653867697755899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15541182508871823597007865 11655886881653867697755899)
      ·
        refine ⟨17483830322480801546633849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11655886881653867697755899 17483830322480801546633849)
        ·
          refine ⟨13112872741860601159975387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17483830322480801546633849 13112872741860601159975387)
          ·
            refine ⟨19669309112790901739963081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13112872741860601159975387 19669309112790901739963081)
            ·
              refine ⟨14751981834593176304972311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19669309112790901739963081 14751981834593176304972311)
              ·
                refine ⟨22127972751889764457458467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14751981834593176304972311 22127972751889764457458467)
                ·
                  refine ⟨33191959127834646686187701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22127972751889764457458467 33191959127834646686187701)
                  ·
                    refine ⟨3111746168234498126830097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33191959127834646686187701 3111746168234498126830097)
                    ·
                      refine ⟨2333809626175873595122573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3111746168234498126830097 2333809626175873595122573)
                      ·
                        rfl

theorem cell23_4545078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 1, 1, 5, 2].length) (baseStart_4545078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4545078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4545078 prefixEnd_4545078 := by exact prefixLift 4545078
  have htrace : WordTrace (prefixWord ++ tailWord_4545078) baseStart_4545078 baseEnd_4545078 := by
    simpa [prefixWord, tailWord_4545078, baseEnd_4545078] using wordTrace_append hprefix tailTrace_4545078
  have hstable : (prefixWord ++ tailWord_4545078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4545078).length < 2 ^ (prefixWord ++ tailWord_4545078).sum := by decide
  have hdescent : baseEnd_4545078 < baseStart_4545078 := by decide
  rcases family_descends (prefixWord ++ tailWord_4545078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4545085 : List Nat := [1, 4, 1, 3, 2, 1, 3, 3, 1, 1, 3]
def baseStart_4545085 : Nat := 118140960795 + 4545085 * 2 ^ 59
def prefixEnd_4545085 : Nat := 4983230072969 + 3 ^ 40 * 4545085 * 2
def baseEnd_4545085 : Nat := 2333813220540455067735041

theorem tailTrace_4545085 : CollatzResearch.WordTrace tailWord_4545085 prefixEnd_4545085 2333813220540455067735041 := by
  unfold tailWord_4545085
  simp only [CollatzResearch.WordTrace]
  refine ⟨165772868738940758563588709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110515245825960505709059139 165772868738940758563588709)
  ·
    refine ⟨31082412888551392230672883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 165772868738940758563588709 31082412888551392230672883)
    ·
      refine ⟨46623619332827088346009325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31082412888551392230672883 46623619332827088346009325)
      ·
        refine ⟨17483857249810158129753497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46623619332827088346009325 17483857249810158129753497)
        ·
          refine ⟨13112892937357618597315123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17483857249810158129753497 13112892937357618597315123)
          ·
            refine ⟨19669339406036427895972685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13112892937357618597315123 19669339406036427895972685)
            ·
              refine ⟨7376002277263660460989757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19669339406036427895972685 7376002277263660460989757)
              ·
                refine ⟨2766000853973872672871159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7376002277263660460989757 2766000853973872672871159)
                ·
                  refine ⟨4149001280960809009306739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2766000853973872672871159 4149001280960809009306739)
                  ·
                    refine ⟨6223501921441213513960109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4149001280960809009306739 6223501921441213513960109)
                    ·
                      refine ⟨2333813220540455067735041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6223501921441213513960109 2333813220540455067735041)
                      ·
                        rfl

theorem cell23_4545085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 3, 1, 1, 3].length) (baseStart_4545085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4545085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4545085 prefixEnd_4545085 := by exact prefixLift 4545085
  have htrace : WordTrace (prefixWord ++ tailWord_4545085) baseStart_4545085 baseEnd_4545085 := by
    simpa [prefixWord, tailWord_4545085, baseEnd_4545085] using wordTrace_append hprefix tailTrace_4545085
  have hstable : (prefixWord ++ tailWord_4545085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4545085).length < 2 ^ (prefixWord ++ tailWord_4545085).sum := by decide
  have hdescent : baseEnd_4545085 < baseStart_4545085 := by decide
  rcases family_descends (prefixWord ++ tailWord_4545085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4545091 : List Nat := [1, 1, 1, 3, 1, 2, 1, 4, 5, 2, 2]
def baseStart_4545091 : Nat := 118140960795 + 4545091 * 2 ^ 59
def prefixEnd_4545091 : Nat := 4983230072969 + 3 ^ 40 * 4545091 * 2
def baseEnd_4545091 : Nat := 2333816301424382044260013

theorem tailTrace_4545091 : CollatzResearch.WordTrace tailWord_4545091 prefixEnd_4545091 2333816301424382044260013 := by
  unfold tailWord_4545091
  simp only [CollatzResearch.WordTrace]
  refine ⟨165773087576919021588307127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110515391717946014392204751 165773087576919021588307127)
  ·
    refine ⟨248659631365378532382460691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165773087576919021588307127 248659631365378532382460691)
    ·
      refine ⟨372989447048067798573691037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248659631365378532382460691 372989447048067798573691037)
      ·
        refine ⟨139871042643025424465134139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 372989447048067798573691037 139871042643025424465134139)
        ·
          refine ⟨209806563964538136697701209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139871042643025424465134139 209806563964538136697701209)
          ·
            refine ⟨157354922973403602523275907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 209806563964538136697701209 157354922973403602523275907)
            ·
              refine ⟨236032384460105403784913861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157354922973403602523275907 236032384460105403784913861)
              ·
                refine ⟨44256072086269763209671349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 236032384460105403784913861 44256072086269763209671349)
                ·
                  refine ⟨4149006758087790300906689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44256072086269763209671349 4149006758087790300906689)
                  ·
                    refine ⟨3111755068565842725680017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4149006758087790300906689 3111755068565842725680017)
                    ·
                      refine ⟨2333816301424382044260013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3111755068565842725680017 2333816301424382044260013)
                      ·
                        rfl

theorem cell23_4545091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 5, 2, 2].length) (baseStart_4545091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4545091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4545091 prefixEnd_4545091 := by exact prefixLift 4545091
  have htrace : WordTrace (prefixWord ++ tailWord_4545091) baseStart_4545091 baseEnd_4545091 := by
    simpa [prefixWord, tailWord_4545091, baseEnd_4545091] using wordTrace_append hprefix tailTrace_4545091
  have hstable : (prefixWord ++ tailWord_4545091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4545091).length < 2 ^ (prefixWord ++ tailWord_4545091).sum := by decide
  have hdescent : baseEnd_4545091 < baseStart_4545091 := by decide
  rcases family_descends (prefixWord ++ tailWord_4545091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4545122 : List Nat := [3, 3, 2, 3, 2, 1, 1, 2, 1, 5]
def baseStart_4545122 : Nat := 118140960795 + 4545122 * 2 ^ 59
def prefixEnd_4545122 : Nat := 4983230072969 + 3 ^ 40 * 4545122 * 2
def baseEnd_4545122 : Nat := 777944073108223807657457

theorem tailTrace_4545122 : CollatzResearch.WordTrace tailWord_4545122 prefixEnd_4545122 777944073108223807657457 := by
  unfold tailWord_4545122
  simp only [CollatzResearch.WordTrace]
  refine ⟨41443554559951678470671405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110516145493204475921790413 41443554559951678470671405)
  ·
    refine ⟨15541332959981879426501777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41443554559951678470671405 15541332959981879426501777)
    ·
      refine ⟨11655999719986409569876333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15541332959981879426501777 11655999719986409569876333)
      ·
        refine ⟨4370999894994903588703625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11655999719986409569876333 4370999894994903588703625)
        ·
          refine ⟨3278249921246177691527719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4370999894994903588703625 3278249921246177691527719)
          ·
            refine ⟨4917374881869266537291579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3278249921246177691527719 4917374881869266537291579)
            ·
              refine ⟨7376062322803899805937369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4917374881869266537291579 7376062322803899805937369)
              ·
                refine ⟨5532046742102924854453027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7376062322803899805937369 5532046742102924854453027)
                ·
                  refine ⟨8298070113154387281679541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5532046742102924854453027 8298070113154387281679541)
                  ·
                    refine ⟨777944073108223807657457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8298070113154387281679541 777944073108223807657457)
                    ·
                      rfl

theorem cell23_4545122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_4545122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4545122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4545122 prefixEnd_4545122 := by exact prefixLift 4545122
  have htrace : WordTrace (prefixWord ++ tailWord_4545122) baseStart_4545122 baseEnd_4545122 := by
    simpa [prefixWord, tailWord_4545122, baseEnd_4545122] using wordTrace_append hprefix tailTrace_4545122
  have hstable : (prefixWord ++ tailWord_4545122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4545122).length < 2 ^ (prefixWord ++ tailWord_4545122).sum := by decide
  have hdescent : baseEnd_4545122 < baseStart_4545122 := by decide
  rcases family_descends (prefixWord ++ tailWord_4545122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4545125 : List Nat := [1, 3, 1, 3, 5, 1, 1, 2, 1, 1, 4]
def baseStart_4545125 : Nat := 118140960795 + 4545125 * 2 ^ 59
def prefixEnd_4545125 : Nat := 4983230072969 + 3 ^ 40 * 4545125 * 2
def baseEnd_4545125 : Nat := 2333833759766634911234857

theorem tailTrace_4545125 : CollatzResearch.WordTrace tailWord_4545125 prefixEnd_4545125 2333833759766634911234857 := by
  unfold tailWord_4545125
  simp only [CollatzResearch.WordTrace]
  refine ⟨165774327658795845395044829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110516218439197230263363219 165774327658795845395044829)
  ·
    refine ⟨62165372872048442023141811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165774327658795845395044829 62165372872048442023141811)
    ·
      refine ⟨93248059308072663034712717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62165372872048442023141811 93248059308072663034712717)
      ·
        refine ⟨34968022240527248638017269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93248059308072663034712717 34968022240527248638017269)
        ·
          refine ⟨3278252085049429559814119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34968022240527248638017269 3278252085049429559814119)
          ·
            refine ⟨4917378127574144339721179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3278252085049429559814119 4917378127574144339721179)
            ·
              refine ⟨7376067191361216509581769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4917378127574144339721179 7376067191361216509581769)
              ·
                refine ⟨5532050393520912382186327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7376067191361216509581769 5532050393520912382186327)
                ·
                  refine ⟨8298075590281368573279491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5532050393520912382186327 8298075590281368573279491)
                  ·
                    refine ⟨12447113385422052859919237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8298075590281368573279491 12447113385422052859919237)
                    ·
                      refine ⟨2333833759766634911234857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12447113385422052859919237 2333833759766634911234857)
                      ·
                        rfl

theorem cell23_4545125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 2, 1, 1, 4].length) (baseStart_4545125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4545125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4545125 prefixEnd_4545125 := by exact prefixLift 4545125
  have htrace : WordTrace (prefixWord ++ tailWord_4545125) baseStart_4545125 baseEnd_4545125 := by
    simpa [prefixWord, tailWord_4545125, baseEnd_4545125] using wordTrace_append hprefix tailTrace_4545125
  have hstable : (prefixWord ++ tailWord_4545125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4545125).length < 2 ^ (prefixWord ++ tailWord_4545125).sum := by decide
  have hdescent : baseEnd_4545125 < baseStart_4545125 := by decide
  rcases family_descends (prefixWord ++ tailWord_4545125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4545128 : List Nat := [2, 1, 4, 3, 2, 1, 1, 1, 3, 2, 3]
def baseStart_4545128 : Nat := 118140960795 + 4545128 * 2 ^ 59
def prefixEnd_4545128 : Nat := 4983230072969 + 3 ^ 40 * 4545128 * 2
def baseEnd_4545128 : Nat := 2333835300208598399497343

theorem tailTrace_4545128 : CollatzResearch.WordTrace tailWord_4545128 prefixEnd_4545128 2333835300208598399497343 := by
  unfold tailWord_4545128
  simp only [CollatzResearch.WordTrace]
  refine ⟨82887218538892488453702019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110516291385189984604936025 82887218538892488453702019)
  ·
    refine ⟨124330827808338732680553029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82887218538892488453702019 124330827808338732680553029)
    ·
      refine ⟨23312030214063512377603693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 124330827808338732680553029 23312030214063512377603693)
      ·
        refine ⟨8742011330273817141601385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23312030214063512377603693 8742011330273817141601385)
        ·
          refine ⟨6556508497705362856201039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8742011330273817141601385 6556508497705362856201039)
          ·
            refine ⟨9834762746558044284301559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6556508497705362856201039 9834762746558044284301559)
            ·
              refine ⟨14752144119837066426452339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9834762746558044284301559 14752144119837066426452339)
              ·
                refine ⟨22128216179755599639678509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14752144119837066426452339 22128216179755599639678509)
                ·
                  refine ⟨8298081067408349864879441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22128216179755599639678509 8298081067408349864879441)
                  ·
                    refine ⟨6223560800556262398659581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8298081067408349864879441 6223560800556262398659581)
                    ·
                      refine ⟨2333835300208598399497343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6223560800556262398659581 2333835300208598399497343)
                      ·
                        rfl

theorem cell23_4545128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_4545128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4545128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4545128 prefixEnd_4545128 := by exact prefixLift 4545128
  have htrace : WordTrace (prefixWord ++ tailWord_4545128) baseStart_4545128 baseEnd_4545128 := by
    simpa [prefixWord, tailWord_4545128, baseEnd_4545128] using wordTrace_append hprefix tailTrace_4545128
  have hstable : (prefixWord ++ tailWord_4545128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4545128).length < 2 ^ (prefixWord ++ tailWord_4545128).sum := by decide
  have hdescent : baseEnd_4545128 < baseStart_4545128 := by decide
  rcases family_descends (prefixWord ++ tailWord_4545128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4545215 : List Nat := [1, 1, 2, 2, 2, 4, 3, 2, 2, 2, 2]
def baseStart_4545215 : Nat := 118140960795 + 4545215 * 2 ^ 59
def prefixEnd_4545215 : Nat := 4983230072969 + 3 ^ 40 * 4545215 * 2
def baseEnd_4545215 : Nat := 2333879973025539559109443

theorem tailTrace_4545215 : CollatzResearch.WordTrace tailWord_4545215 prefixEnd_4545215 2333879973025539559109443 := by
  unfold tailWord_4545215
  simp only [CollatzResearch.WordTrace]
  refine ⟨165777610228469790765821099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110518406818979860510547399 165777610228469790765821099)
  ·
    refine ⟨248666415342704686148731649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165777610228469790765821099 248666415342704686148731649)
    ·
      refine ⟨186499811507028514611548737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 248666415342704686148731649 186499811507028514611548737)
      ·
        refine ⟨139874858630271385958661553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186499811507028514611548737 139874858630271385958661553)
        ·
          refine ⟨104906143972703539468996165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139874858630271385958661553 104906143972703539468996165)
          ·
            refine ⟨19669901994881913650436781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 104906143972703539468996165 19669901994881913650436781)
            ·
              refine ⟨7376213248080717618913793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19669901994881913650436781 7376213248080717618913793)
              ·
                refine ⟨5532159936060538214185345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7376213248080717618913793 5532159936060538214185345)
                ·
                  refine ⟨4149119952045403660639009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5532159936060538214185345 4149119952045403660639009)
                  ·
                    refine ⟨3111839964034052745479257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4149119952045403660639009 3111839964034052745479257)
                    ·
                      refine ⟨2333879973025539559109443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3111839964034052745479257 2333879973025539559109443)
                      ·
                        rfl

theorem cell23_4545215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 2, 2, 2, 2].length) (baseStart_4545215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4545215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4545215 prefixEnd_4545215 := by exact prefixLift 4545215
  have htrace : WordTrace (prefixWord ++ tailWord_4545215) baseStart_4545215 baseEnd_4545215 := by
    simpa [prefixWord, tailWord_4545215, baseEnd_4545215] using wordTrace_append hprefix tailTrace_4545215
  have hstable : (prefixWord ++ tailWord_4545215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4545215).length < 2 ^ (prefixWord ++ tailWord_4545215).sum := by decide
  have hdescent : baseEnd_4545215 < baseStart_4545215 := by decide
  rcases family_descends (prefixWord ++ tailWord_4545215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4545251 : List Nat := [1, 1, 1, 7, 1, 1, 2, 1, 1, 7]
def baseStart_4545251 : Nat := 118140960795 + 4545251 * 2 ^ 59
def prefixEnd_4545251 : Nat := 4983230072969 + 3 ^ 40 * 4545251 * 2
def baseEnd_4545251 : Nat := 777966152776367139419759

theorem tailTrace_4545251 : CollatzResearch.WordTrace tailWord_4545251 prefixEnd_4545251 777966152776367139419759 := by
  unfold tailWord_4545251
  simp only [CollatzResearch.WordTrace]
  refine ⟨165778923256339368914131607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110519282170892912609421071 165778923256339368914131607)
  ·
    refine ⟨248668384884509053371197411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165778923256339368914131607 248668384884509053371197411)
    ·
      refine ⟨373002577326763580056796117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248668384884509053371197411 373002577326763580056796117)
      ·
        refine ⟨8742247906096021407581159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 373002577326763580056796117 8742247906096021407581159)
        ·
          refine ⟨13113371859144032111371739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8742247906096021407581159 13113371859144032111371739)
          ·
            refine ⟨19670057788716048167057609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13113371859144032111371739 19670057788716048167057609)
            ·
              refine ⟨14752543341537036125293207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19670057788716048167057609 14752543341537036125293207)
              ·
                refine ⟨22128815012305554187939811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14752543341537036125293207 22128815012305554187939811)
                ·
                  refine ⟨33193222518458331281909717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22128815012305554187939811 33193222518458331281909717)
                  ·
                    refine ⟨777966152776367139419759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33193222518458331281909717 777966152776367139419759)
                    ·
                      rfl

theorem cell23_4545251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 1, 1, 7].length) (baseStart_4545251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4545251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4545251 prefixEnd_4545251 := by exact prefixLift 4545251
  have htrace : WordTrace (prefixWord ++ tailWord_4545251) baseStart_4545251 baseEnd_4545251 := by
    simpa [prefixWord, tailWord_4545251, baseEnd_4545251] using wordTrace_append hprefix tailTrace_4545251
  have hstable : (prefixWord ++ tailWord_4545251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4545251).length < 2 ^ (prefixWord ++ tailWord_4545251).sum := by decide
  have hdescent : baseEnd_4545251 < baseStart_4545251 := by decide
  rcases family_descends (prefixWord ++ tailWord_4545251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4545261 : List Nat := [1, 5, 1, 2, 1, 1, 2, 2, 1, 2, 5]
def baseStart_4545261 : Nat := 118140960795 + 4545261 * 2 ^ 59
def prefixEnd_4545261 : Nat := 4983230072969 + 3 ^ 40 * 4545261 * 2
def baseEnd_4545261 : Nat := 2333903593135646379134231

theorem tailTrace_4545261 : CollatzResearch.WordTrace tailWord_4545261 prefixEnd_4545261 2333903593135646379134231 := by
  unfold tailWord_4545261
  simp only [CollatzResearch.WordTrace]
  refine ⟨165779287986303140621995637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110519525324202093747997091 165779287986303140621995637)
  ·
    refine ⟨15541808248715919433312091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 165779287986303140621995637 15541808248715919433312091)
    ·
      refine ⟨23312712373073879149968137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15541808248715919433312091 23312712373073879149968137)
      ·
        refine ⟨17484534279805409362476103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23312712373073879149968137 17484534279805409362476103)
        ·
          refine ⟨26226801419708114043714155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17484534279805409362476103 26226801419708114043714155)
          ·
            refine ⟨39340202129562171065571233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26226801419708114043714155 39340202129562171065571233)
            ·
              refine ⟨29505151597171628299178425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39340202129562171065571233 29505151597171628299178425)
              ·
                refine ⟨22128863697878721224383819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29505151597171628299178425 22128863697878721224383819)
                ·
                  refine ⟨33193295546818081836575729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22128863697878721224383819 33193295546818081836575729)
                  ·
                    refine ⟨24894971660113561377431797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33193295546818081836575729 24894971660113561377431797)
                    ·
                      refine ⟨2333903593135646379134231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24894971660113561377431797 2333903593135646379134231)
                      ·
                        rfl

theorem cell23_4545261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_4545261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4545261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4545261 prefixEnd_4545261 := by exact prefixLift 4545261
  have htrace : WordTrace (prefixWord ++ tailWord_4545261) baseStart_4545261 baseEnd_4545261 := by
    simpa [prefixWord, tailWord_4545261, baseEnd_4545261] using wordTrace_append hprefix tailTrace_4545261
  have hstable : (prefixWord ++ tailWord_4545261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4545261).length < 2 ^ (prefixWord ++ tailWord_4545261).sum := by decide
  have hdescent : baseEnd_4545261 < baseStart_4545261 := by decide
  rcases family_descends (prefixWord ++ tailWord_4545261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4545278 : List Nat := [4, 2, 2, 1, 2, 2, 1, 1, 1, 2, 5]
def baseStart_4545278 : Nat := 118140960795 + 4545278 * 2 ^ 59
def prefixEnd_4545278 : Nat := 4983230072969 + 3 ^ 40 * 4545278 * 2
def baseEnd_4545278 : Nat := 2333912322306772812621653

theorem tailTrace_4545278 : CollatzResearch.WordTrace tailWord_4545278 prefixEnd_4545278 2333912322306772812621653 := by
  unfold tailWord_4545278
  simp only [CollatzResearch.WordTrace]
  refine ⟨20722488503405194065670561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110519938684827701683576325 20722488503405194065670561)
  ·
    refine ⟨15541866377553895549252921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20722488503405194065670561 15541866377553895549252921)
    ·
      refine ⟨11656399783165421661939691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15541866377553895549252921 11656399783165421661939691)
      ·
        refine ⟨17484599674748132492909537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11656399783165421661939691 17484599674748132492909537)
        ·
          refine ⟨13113449756061099369682153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17484599674748132492909537 13113449756061099369682153)
          ·
            refine ⟨9835087317045824527261615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13113449756061099369682153 9835087317045824527261615)
            ·
              refine ⟨14752630975568736790892423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9835087317045824527261615 14752630975568736790892423)
              ·
                refine ⟨22128946463353105186338635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14752630975568736790892423 22128946463353105186338635)
                ·
                  refine ⟨33193419695029657779507953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22128946463353105186338635 33193419695029657779507953)
                  ·
                    refine ⟨24895064771272243334630965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33193419695029657779507953 24895064771272243334630965)
                    ·
                      refine ⟨2333912322306772812621653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24895064771272243334630965 2333912322306772812621653)
                      ·
                        rfl

theorem cell23_4545278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_4545278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4545278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4545278 prefixEnd_4545278 := by exact prefixLift 4545278
  have htrace : WordTrace (prefixWord ++ tailWord_4545278) baseStart_4545278 baseEnd_4545278 := by
    simpa [prefixWord, tailWord_4545278, baseEnd_4545278] using wordTrace_append hprefix tailTrace_4545278
  have hstable : (prefixWord ++ tailWord_4545278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4545278).length < 2 ^ (prefixWord ++ tailWord_4545278).sum := by decide
  have hdescent : baseEnd_4545278 < baseStart_4545278 := by decide
  rcases family_descends (prefixWord ++ tailWord_4545278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4545291 : List Nat := [1, 1, 1, 1, 5, 1, 1, 1, 6, 2, 3]
def baseStart_4545291 : Nat := 118140960795 + 4545291 * 2 ^ 59
def prefixEnd_4545291 : Nat := 4983230072969 + 3 ^ 40 * 4545291 * 2
def baseEnd_4545291 : Nat := 2333918997555281261759093

theorem tailTrace_4545291 : CollatzResearch.WordTrace tailWord_4545291 prefixEnd_4545291 2333918997555281261759093 := by
  unfold tailWord_4545291
  simp only [CollatzResearch.WordTrace]
  refine ⟨165780382176194455745587727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110520254784129637163725151 165780382176194455745587727)
  ·
    refine ⟨248670573264291683618381591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165780382176194455745587727 248670573264291683618381591)
    ·
      refine ⟨373005859896437525427572387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248670573264291683618381591 373005859896437525427572387)
      ·
        refine ⟨559508789844656288141358581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 373005859896437525427572387 559508789844656288141358581)
        ·
          refine ⟨52453949047936527013252367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 559508789844656288141358581 52453949047936527013252367)
          ·
            refine ⟨78680923571904790519878551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52453949047936527013252367 78680923571904790519878551)
            ·
              refine ⟨118021385357857185779817827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78680923571904790519878551 118021385357857185779817827)
              ·
                refine ⟨177032078036785778669726741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118021385357857185779817827 177032078036785778669726741)
                ·
                  refine ⟨8298378657974333375143441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 177032078036785778669726741 8298378657974333375143441)
                  ·
                    refine ⟨6223783993480750031357581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8298378657974333375143441 6223783993480750031357581)
                    ·
                      refine ⟨2333918997555281261759093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6223783993480750031357581 2333918997555281261759093)
                      ·
                        rfl

theorem cell23_4545291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 6, 2, 3].length) (baseStart_4545291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4545291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4545291 prefixEnd_4545291 := by exact prefixLift 4545291
  have htrace : WordTrace (prefixWord ++ tailWord_4545291) baseStart_4545291 baseEnd_4545291 := by
    simpa [prefixWord, tailWord_4545291, baseEnd_4545291] using wordTrace_append hprefix tailTrace_4545291
  have hstable : (prefixWord ++ tailWord_4545291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4545291).length < 2 ^ (prefixWord ++ tailWord_4545291).sum := by decide
  have hdescent : baseEnd_4545291 < baseStart_4545291 := by decide
  rcases family_descends (prefixWord ++ tailWord_4545291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4545308 : List Nat := [2, 2, 3, 1, 1, 3, 1, 3, 2, 2, 3]
def baseStart_4545308 : Nat := 118140960795 + 4545308 * 2 ^ 59
def prefixEnd_4545308 : Nat := 4983230072969 + 3 ^ 40 * 4545308 * 2
def baseEnd_4545308 : Nat := 2333927726726407695246515

theorem tailTrace_4545308 : CollatzResearch.WordTrace tailWord_4545308 prefixEnd_4545308 2333927726726407695246515 := by
  unfold tailWord_4545308
  simp only [CollatzResearch.WordTrace]
  refine ⟨82890501108566433824478289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110520668144755245099304385 82890501108566433824478289)
  ·
    refine ⟨62167875831424825368358717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82890501108566433824478289 62167875831424825368358717)
    ·
      refine ⟨23312953436784309513134519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62167875831424825368358717 23312953436784309513134519)
      ·
        refine ⟨34969430155176464269701779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23312953436784309513134519 34969430155176464269701779)
        ·
          refine ⟨52454145232764696404552669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34969430155176464269701779 52454145232764696404552669)
          ·
            refine ⟨19670304462286761151707251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52454145232764696404552669 19670304462286761151707251)
            ·
              refine ⟨29505456693430141727560877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19670304462286761151707251 29505456693430141727560877)
              ·
                refine ⟨11064546260036303147835329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29505456693430141727560877 11064546260036303147835329)
                ·
                  refine ⟨8298409695027227360876497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11064546260036303147835329 8298409695027227360876497)
                  ·
                    refine ⟨6223807271270420520657373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8298409695027227360876497 6223807271270420520657373)
                    ·
                      refine ⟨2333927726726407695246515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6223807271270420520657373 2333927726726407695246515)
                      ·
                        rfl

theorem cell23_4545308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 3, 2, 2, 3].length) (baseStart_4545308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4545308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4545308 prefixEnd_4545308 := by exact prefixLift 4545308
  have htrace : WordTrace (prefixWord ++ tailWord_4545308) baseStart_4545308 baseEnd_4545308 := by
    simpa [prefixWord, tailWord_4545308, baseEnd_4545308] using wordTrace_append hprefix tailTrace_4545308
  have hstable : (prefixWord ++ tailWord_4545308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4545308).length < 2 ^ (prefixWord ++ tailWord_4545308).sum := by decide
  have hdescent : baseEnd_4545308 < baseStart_4545308 := by decide
  rcases family_descends (prefixWord ++ tailWord_4545308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4545388 : List Nat := [2, 2, 1, 1, 4, 1, 3, 1, 4, 4]
def baseStart_4545388 : Nat := 118140960795 + 4545388 * 2 ^ 59
def prefixEnd_4545388 : Nat := 4983230072969 + 3 ^ 40 * 4545388 * 2
def baseEnd_4545388 : Nat := 777989601726255794082049

theorem tailTrace_4545388 : CollatzResearch.WordTrace tailWord_4545388 prefixEnd_4545388 777989601726255794082049 := by
  unfold tailWord_4545388
  simp only [CollatzResearch.WordTrace]
  refine ⟨82891960028421520655934409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110522613371228694207912545 82891960028421520655934409)
  ·
    refine ⟨62168970021316140491950807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82891960028421520655934409 62168970021316140491950807)
    ·
      refine ⟨93253455031974210737926211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62168970021316140491950807 93253455031974210737926211)
      ·
        refine ⟨139880182547961316106889317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93253455031974210737926211 139880182547961316106889317)
        ·
          refine ⟨26227534227742746770041747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 139880182547961316106889317 26227534227742746770041747)
          ·
            refine ⟨39341301341614120155062621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26227534227742746770041747 39341301341614120155062621)
            ·
              refine ⟨14752988003105295058148483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39341301341614120155062621 14752988003105295058148483)
              ·
                refine ⟨22129482004657942587222725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14752988003105295058148483 22129482004657942587222725)
                ·
                  refine ⟨4149277875873364235104261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22129482004657942587222725 4149277875873364235104261)
                  ·
                    refine ⟨777989601726255794082049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4149277875873364235104261 777989601726255794082049)
                    ·
                      rfl

theorem cell23_4545388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 4].length) (baseStart_4545388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4545388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4545388 prefixEnd_4545388 := by exact prefixLift 4545388
  have htrace : WordTrace (prefixWord ++ tailWord_4545388) baseStart_4545388 baseEnd_4545388 := by
    simpa [prefixWord, tailWord_4545388, baseEnd_4545388] using wordTrace_append hprefix tailTrace_4545388
  have hstable : (prefixWord ++ tailWord_4545388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4545388).length < 2 ^ (prefixWord ++ tailWord_4545388).sum := by decide
  have hdescent : baseEnd_4545388 < baseStart_4545388 := by decide
  rcases family_descends (prefixWord ++ tailWord_4545388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4545391 : List Nat := [1, 1, 2, 1, 3, 1, 1, 4, 3, 2, 4]
def baseStart_4545391 : Nat := 118140960795 + 4545391 * 2 ^ 59
def prefixEnd_4545391 : Nat := 4983230072969 + 3 ^ 40 * 4545391 * 2
def baseEnd_4545391 : Nat := 2333970345620730870508633

theorem tailTrace_4545391 : CollatzResearch.WordTrace tailWord_4545391 prefixEnd_4545391 2333970345620730870508633 := by
  unfold tailWord_4545391
  simp only [CollatzResearch.WordTrace]
  refine ⟨165784029475832172824228027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110522686317221448549485351 165784029475832172824228027)
  ·
    refine ⟨248676044213748259236342041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165784029475832172824228027 248676044213748259236342041)
    ·
      refine ⟨186507033160311194427256531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 248676044213748259236342041 186507033160311194427256531)
      ·
        refine ⟨279760549740466791640884797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186507033160311194427256531 279760549740466791640884797)
        ·
          refine ⟨104910206152675046865331799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 279760549740466791640884797 104910206152675046865331799)
          ·
            refine ⟨157365309229012570297997699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104910206152675046865331799 157365309229012570297997699)
            ·
              refine ⟨236047963843518855446996549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157365309229012570297997699 236047963843518855446996549)
              ·
                refine ⟨44258993220659785396311853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 236047963843518855446996549 44258993220659785396311853)
                ·
                  refine ⟨16597122457747419523616945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44258993220659785396311853 16597122457747419523616945)
                  ·
                    refine ⟨12447841843310564642712709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16597122457747419523616945 12447841843310564642712709)
                    ·
                      refine ⟨2333970345620730870508633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12447841843310564642712709 2333970345620730870508633)
                      ·
                        rfl

theorem cell23_4545391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 3, 2, 4].length) (baseStart_4545391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4545391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4545391 prefixEnd_4545391 := by exact prefixLift 4545391
  have htrace : WordTrace (prefixWord ++ tailWord_4545391) baseStart_4545391 baseEnd_4545391 := by
    simpa [prefixWord, tailWord_4545391, baseEnd_4545391] using wordTrace_append hprefix tailTrace_4545391
  have hstable : (prefixWord ++ tailWord_4545391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4545391).length < 2 ^ (prefixWord ++ tailWord_4545391).sum := by decide
  have hdescent : baseEnd_4545391 < baseStart_4545391 := by decide
  rcases family_descends (prefixWord ++ tailWord_4545391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4545395 : List Nat := [1, 1, 1, 2, 2, 1, 5, 3, 3, 2, 2]
def baseStart_4545395 : Nat := 118140960795 + 4545395 * 2 ^ 59
def prefixEnd_4545395 : Nat := 4983230072969 + 3 ^ 40 * 4545395 * 2
def baseEnd_4545395 : Nat := 2333972399543348854858615

theorem tailTrace_4545395 : CollatzResearch.WordTrace tailWord_4545395 prefixEnd_4545395 2333972399543348854858615 := by
  unfold tailWord_4545395
  simp only [CollatzResearch.WordTrace]
  refine ⟨165784175367817681507373639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110522783578545121004915759 165784175367817681507373639)
  ·
    refine ⟨248676263051726522261060459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165784175367817681507373639 248676263051726522261060459)
    ·
      refine ⟨373014394577589783391590689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248676263051726522261060459 373014394577589783391590689)
      ·
        refine ⟨279760795933192337543693017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 373014394577589783391590689 279760795933192337543693017)
        ·
          refine ⟨209820596949894253157769763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 279760795933192337543693017 209820596949894253157769763)
          ·
            refine ⟨314730895424841379736654645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 209820596949894253157769763 314730895424841379736654645)
            ·
              refine ⟨29506021446078879350311373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 314730895424841379736654645 29506021446078879350311373)
              ·
                refine ⟨11064758042279579756366765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29506021446078879350311373 11064758042279579756366765)
                ·
                  refine ⟨4149284265854842408637537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11064758042279579756366765 4149284265854842408637537)
                  ·
                    refine ⟨3111963199391131806478153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4149284265854842408637537 3111963199391131806478153)
                    ·
                      refine ⟨2333972399543348854858615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3111963199391131806478153 2333972399543348854858615)
                      ·
                        rfl

theorem cell23_4545395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 3, 3, 2, 2].length) (baseStart_4545395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4545395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4545395 prefixEnd_4545395 := by exact prefixLift 4545395
  have htrace : WordTrace (prefixWord ++ tailWord_4545395) baseStart_4545395 baseEnd_4545395 := by
    simpa [prefixWord, tailWord_4545395, baseEnd_4545395] using wordTrace_append hprefix tailTrace_4545395
  have hstable : (prefixWord ++ tailWord_4545395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4545395).length < 2 ^ (prefixWord ++ tailWord_4545395).sum := by decide
  have hdescent : baseEnd_4545395 < baseStart_4545395 := by decide
  rcases family_descends (prefixWord ++ tailWord_4545395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4545415 : List Nat := [1, 1, 4, 2, 3, 1, 1, 4, 1, 2, 3]
def baseStart_4545415 : Nat := 118140960795 + 4545415 * 2 ^ 59
def prefixEnd_4545415 : Nat := 4983230072969 + 3 ^ 40 * 4545415 * 2
def baseEnd_4545415 : Nat := 2333982669156438776608523

theorem tailTrace_4545415 : CollatzResearch.WordTrace tailWord_4545415 prefixEnd_4545415 2333982669156438776608523 := by
  unfold tailWord_4545415
  simp only [CollatzResearch.WordTrace]
  refine ⟨165784904827745224923101699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110523269885163483282067799 165784904827745224923101699)
  ·
    refine ⟨248677357241617837384652549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165784904827745224923101699 248677357241617837384652549)
    ·
      refine ⟨46627004482803344509622353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 248677357241617837384652549 46627004482803344509622353)
      ·
        refine ⟨34970253362102508382216765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46627004482803344509622353 34970253362102508382216765)
        ·
          refine ⟨13113845010788440643331287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34970253362102508382216765 13113845010788440643331287)
          ·
            refine ⟨19670767516182660964996931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13113845010788440643331287 19670767516182660964996931)
            ·
              refine ⟨29506151274273991447495397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19670767516182660964996931 29506151274273991447495397)
              ·
                refine ⟨5532403363926373396405387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29506151274273991447495397 5532403363926373396405387)
                ·
                  refine ⟨8298605045889560094608081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5532403363926373396405387 8298605045889560094608081)
                  ·
                    refine ⟨6223953784417170070956061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8298605045889560094608081 6223953784417170070956061)
                    ·
                      refine ⟨2333982669156438776608523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6223953784417170070956061 2333982669156438776608523)
                      ·
                        rfl

theorem cell23_4545415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 4, 1, 2, 3].length) (baseStart_4545415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4545415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4545415 prefixEnd_4545415 := by exact prefixLift 4545415
  have htrace : WordTrace (prefixWord ++ tailWord_4545415) baseStart_4545415 baseEnd_4545415 := by
    simpa [prefixWord, tailWord_4545415, baseEnd_4545415] using wordTrace_append hprefix tailTrace_4545415
  have hstable : (prefixWord ++ tailWord_4545415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4545415).length < 2 ^ (prefixWord ++ tailWord_4545415).sum := by decide
  have hdescent : baseEnd_4545415 < baseStart_4545415 := by decide
  rcases family_descends (prefixWord ++ tailWord_4545415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4545418 : List Nat := [3, 1, 2, 4, 1, 2, 1, 9]
def baseStart_4545418 : Nat := 118140960795 + 4545418 * 2 ^ 59
def prefixEnd_4545418 : Nat := 4983230072969 + 3 ^ 40 * 4545418 * 2
def baseEnd_4545418 : Nat := 86443859614755639439667

theorem tailTrace_4545418 : CollatzResearch.WordTrace tailWord_4545418 prefixEnd_4545418 86443859614755639439667 := by
  unfold tailWord_4545418
  simp only [CollatzResearch.WordTrace]
  refine ⟨41446253561683589108865227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110523342831156237623640605 41446253561683589108865227)
  ·
    refine ⟨62169380342525383663297841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41446253561683589108865227 62169380342525383663297841)
    ·
      refine ⟨46627035256894037747473381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62169380342525383663297841 46627035256894037747473381)
      ·
        refine ⟨8742569110667632077651259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46627035256894037747473381 8742569110667632077651259)
        ·
          refine ⟨13113853666001448116476889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8742569110667632077651259 13113853666001448116476889)
          ·
            refine ⟨9835390249501086087357667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13113853666001448116476889 9835390249501086087357667)
            ·
              refine ⟨14753085374251629131036501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9835390249501086087357667 14753085374251629131036501)
              ·
                refine ⟨86443859614755639439667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14753085374251629131036501 86443859614755639439667)
                ·
                  rfl

theorem cell23_4545418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 9].length) (baseStart_4545418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4545418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4545418 prefixEnd_4545418 := by exact prefixLift 4545418
  have htrace : WordTrace (prefixWord ++ tailWord_4545418) baseStart_4545418 baseEnd_4545418 := by
    simpa [prefixWord, tailWord_4545418, baseEnd_4545418] using wordTrace_append hprefix tailTrace_4545418
  have hstable : (prefixWord ++ tailWord_4545418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4545418).length < 2 ^ (prefixWord ++ tailWord_4545418).sum := by decide
  have hdescent : baseEnd_4545418 < baseStart_4545418 := by decide
  rcases family_descends (prefixWord ++ tailWord_4545418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4545429 : List Nat := [1, 3, 2, 1, 1, 4, 3, 3, 1, 2, 2]
def baseStart_4545429 : Nat := 118140960795 + 4545429 * 2 ^ 59
def prefixEnd_4545429 : Nat := 4983230072969 + 3 ^ 40 * 4545429 * 2
def baseEnd_4545429 : Nat := 2333989857885601721833459

theorem tailTrace_4545429 : CollatzResearch.WordTrace tailWord_4545429 prefixEnd_4545429 2333989857885601721833459 := by
  unfold tailWord_4545429
  simp only [CollatzResearch.WordTrace]
  refine ⟨165785415449694505314111341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110523610299796336876074227 165785415449694505314111341)
  ·
    refine ⟨62169530793635439492791753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165785415449694505314111341 62169530793635439492791753)
    ·
      refine ⟨46627148095226579619593815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62169530793635439492791753 46627148095226579619593815)
      ·
        refine ⟨69940722142839869429390723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46627148095226579619593815 69940722142839869429390723)
        ·
          refine ⟨104911083214259804144086085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69940722142839869429390723 104911083214259804144086085)
          ·
            refine ⟨19670828102673713277016141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 104911083214259804144086085 19670828102673713277016141)
            ·
              refine ⟨7376560538502642478881053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19670828102673713277016141 7376560538502642478881053)
              ·
                refine ⟨2766210201938490929580395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7376560538502642478881053 2766210201938490929580395)
                ·
                  refine ⟨4149315302907736394370593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2766210201938490929580395 4149315302907736394370593)
                  ·
                    refine ⟨3111986477180802295777945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4149315302907736394370593 3111986477180802295777945)
                    ·
                      refine ⟨2333989857885601721833459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3111986477180802295777945 2333989857885601721833459)
                      ·
                        rfl

theorem cell23_4545429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 3, 1, 2, 2].length) (baseStart_4545429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4545429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4545429 prefixEnd_4545429 := by exact prefixLift 4545429
  have htrace : WordTrace (prefixWord ++ tailWord_4545429) baseStart_4545429 baseEnd_4545429 := by
    simpa [prefixWord, tailWord_4545429, baseEnd_4545429] using wordTrace_append hprefix tailTrace_4545429
  have hstable : (prefixWord ++ tailWord_4545429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4545429).length < 2 ^ (prefixWord ++ tailWord_4545429).sum := by decide
  have hdescent : baseEnd_4545429 < baseStart_4545429 := by decide
  rcases family_descends (prefixWord ++ tailWord_4545429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4545451 : List Nat := [1, 1, 1, 1, 2, 1, 1, 5, 1, 5, 4]
def baseStart_4545451 : Nat := 118140960795 + 4545451 * 2 ^ 59
def prefixEnd_4545451 : Nat := 4983230072969 + 3 ^ 40 * 4545451 * 2
def baseEnd_4545451 : Nat := 2334001154460000635758357

theorem tailTrace_4545451 : CollatzResearch.WordTrace tailWord_4545451 prefixEnd_4545451 2334001154460000635758357 := by
  unfold tailWord_4545451
  simp only [CollatzResearch.WordTrace]
  refine ⟨165786217855614803071412207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110524145237076535380941471 165786217855614803071412207)
  ·
    refine ⟨248679326783422204607118311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165786217855614803071412207 248679326783422204607118311)
    ·
      refine ⟨373018990175133306910677467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248679326783422204607118311 373018990175133306910677467)
      ·
        refine ⟨559528485262699960366016201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 373018990175133306910677467 559528485262699960366016201)
        ·
          refine ⟨419646363947024970274512151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 559528485262699960366016201 419646363947024970274512151)
          ·
            refine ⟨629469545920537455411768227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 419646363947024970274512151 629469545920537455411768227)
            ·
              refine ⟨944204318880806183117652341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 629469545920537455411768227 944204318880806183117652341)
              ·
                refine ⟨88519154895075579667279907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 944204318880806183117652341 88519154895075579667279907)
                ·
                  refine ⟨132778732342613369500919861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 88519154895075579667279907 132778732342613369500919861)
                  ·
                    refine ⟨12448006157120003390711237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 132778732342613369500919861 12448006157120003390711237)
                    ·
                      refine ⟨2334001154460000635758357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12448006157120003390711237 2334001154460000635758357)
                      ·
                        rfl

theorem cell23_4545451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 5, 4].length) (baseStart_4545451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4545451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4545451 prefixEnd_4545451 := by exact prefixLift 4545451
  have htrace : WordTrace (prefixWord ++ tailWord_4545451) baseStart_4545451 baseEnd_4545451 := by
    simpa [prefixWord, tailWord_4545451, baseEnd_4545451] using wordTrace_append hprefix tailTrace_4545451
  have hstable : (prefixWord ++ tailWord_4545451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4545451).length < 2 ^ (prefixWord ++ tailWord_4545451).sum := by decide
  have hdescent : baseEnd_4545451 < baseStart_4545451 := by decide
  rcases family_descends (prefixWord ++ tailWord_4545451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4545472 : List Nat := [2, 1, 1, 2, 3, 3, 3, 2, 1, 3, 2]
def baseStart_4545472 : Nat := 118140960795 + 4545472 * 2 ^ 59
def prefixEnd_4545472 : Nat := 4983230072969 + 3 ^ 40 * 4545472 * 2
def baseEnd_4545472 : Nat := 2334011937553745053595761

theorem tailTrace_4545472 : CollatzResearch.WordTrace tailWord_4545472 prefixEnd_4545472 2334011937553745053595761 := by
  unfold tailWord_4545472
  simp only [CollatzResearch.WordTrace]
  refine ⟨82893491894269361828963335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110524655859025815771951113 82893491894269361828963335)
  ·
    refine ⟨124340237841404042743445003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82893491894269361828963335 124340237841404042743445003)
    ·
      refine ⟨186510356762106064115167505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124340237841404042743445003 186510356762106064115167505)
      ·
        refine ⟨139882767571579548086375629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186510356762106064115167505 139882767571579548086375629)
        ·
          refine ⟨52456037839342330532390861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 139882767571579548086375629 52456037839342330532390861)
          ·
            refine ⟨19671014189753373949646573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52456037839342330532390861 19671014189753373949646573)
            ·
              refine ⟨7376630321157515231117465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19671014189753373949646573 7376630321157515231117465)
              ·
                refine ⟨5532472740868136423338099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7376630321157515231117465 5532472740868136423338099)
                ·
                  refine ⟨8298709111302204635007149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5532472740868136423338099 8298709111302204635007149)
                  ·
                    refine ⟨3112015916738326738127681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8298709111302204635007149 3112015916738326738127681)
                    ·
                      refine ⟨2334011937553745053595761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3112015916738326738127681 2334011937553745053595761)
                      ·
                        rfl

theorem cell23_4545472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 2, 1, 3, 2].length) (baseStart_4545472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4545472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4545472 prefixEnd_4545472 := by exact prefixLift 4545472
  have htrace : WordTrace (prefixWord ++ tailWord_4545472) baseStart_4545472 baseEnd_4545472 := by
    simpa [prefixWord, tailWord_4545472, baseEnd_4545472] using wordTrace_append hprefix tailTrace_4545472
  have hstable : (prefixWord ++ tailWord_4545472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4545472).length < 2 ^ (prefixWord ++ tailWord_4545472).sum := by decide
  have hdescent : baseEnd_4545472 < baseStart_4545472 := by decide
  rcases family_descends (prefixWord ++ tailWord_4545472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4545585 : List Nat := [1, 2, 2, 3, 1, 2, 1, 4, 3, 4]
def baseStart_4545585 : Nat := 118140960795 + 4545585 * 2 ^ 59
def prefixEnd_4545585 : Nat := 4983230072969 + 3 ^ 40 * 4545585 * 2
def baseEnd_4545585 : Nat := 778023320289234370494247

theorem tailTrace_4545585 : CollatzResearch.WordTrace tailWord_4545585 prefixEnd_4545585 778023320289234370494247 := by
  unfold tailWord_4545585
  simp only [CollatzResearch.WordTrace]
  refine ⟨165791105237129343956790209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110527403491419562637860139 165791105237129343956790209)
  ·
    refine ⟨124343328927847007967592657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165791105237129343956790209 124343328927847007967592657)
    ·
      refine ⟨93257496695885255975694493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124343328927847007967592657 93257496695885255975694493)
      ·
        refine ⟨34971561260956970990885435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93257496695885255975694493 34971561260956970990885435)
        ·
          refine ⟨52457341891435456486328153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34971561260956970990885435 52457341891435456486328153)
          ·
            refine ⟨39343006418576592364746115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52457341891435456486328153 39343006418576592364746115)
            ·
              refine ⟨59014509627864888547119173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39343006418576592364746115 59014509627864888547119173)
              ·
                refine ⟨11065220555224666602584845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59014509627864888547119173 11065220555224666602584845)
                ·
                  refine ⟨4149457708209249975969317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11065220555224666602584845 4149457708209249975969317)
                  ·
                    refine ⟨778023320289234370494247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4149457708209249975969317 778023320289234370494247)
                    ·
                      rfl

theorem cell23_4545585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 4, 3, 4].length) (baseStart_4545585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4545585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4545585 prefixEnd_4545585 := by exact prefixLift 4545585
  have htrace : WordTrace (prefixWord ++ tailWord_4545585) baseStart_4545585 baseEnd_4545585 := by
    simpa [prefixWord, tailWord_4545585, baseEnd_4545585] using wordTrace_append hprefix tailTrace_4545585
  have hstable : (prefixWord ++ tailWord_4545585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4545585).length < 2 ^ (prefixWord ++ tailWord_4545585).sum := by decide
  have hdescent : baseEnd_4545585 < baseStart_4545585 := by decide
  rcases family_descends (prefixWord ++ tailWord_4545585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4545675 : List Nat := [1, 1, 1, 1, 4, 1, 1, 5, 4, 4]
def baseStart_4545675 : Nat := 118140960795 + 4545675 * 2 ^ 59
def prefixEnd_4545675 : Nat := 4983230072969 + 3 ^ 40 * 4545675 * 2
def baseEnd_4545675 : Nat := 778038724708869253119109

theorem tailTrace_4545675 : CollatzResearch.WordTrace tailWord_4545675 prefixEnd_4545675 778038724708869253119109 := by
  unfold tailWord_4545675
  simp only [CollatzResearch.WordTrace]
  refine ⟨165794387806803289327566479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110529591871202192885044319 165794387806803289327566479)
  ·
    refine ⟨248691581710204933991349719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165794387806803289327566479 248691581710204933991349719)
    ·
      refine ⟨373037372565307400987024579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248691581710204933991349719 373037372565307400987024579)
      ·
        refine ⟨559556058847961101480536869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 373037372565307400987024579 559556058847961101480536869)
        ·
          refine ⟨104916761033992706527600663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 559556058847961101480536869 104916761033992706527600663)
          ·
            refine ⟨157375141550989059791400995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104916761033992706527600663 157375141550989059791400995)
            ·
              refine ⟨236062712326483589687101493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157375141550989059791400995 236062712326483589687101493)
              ·
                refine ⟨22130879280607836533165765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 236062712326483589687101493 22130879280607836533165765)
                ·
                  refine ⟨4149539865113969349968581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22130879280607836533165765 4149539865113969349968581)
                  ·
                    refine ⟨778038724708869253119109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4149539865113969349968581 778038724708869253119109)
                    ·
                      rfl

theorem cell23_4545675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 5, 4, 4].length) (baseStart_4545675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4545675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4545675 prefixEnd_4545675 := by exact prefixLift 4545675
  have htrace : WordTrace (prefixWord ++ tailWord_4545675) baseStart_4545675 baseEnd_4545675 := by
    simpa [prefixWord, tailWord_4545675, baseEnd_4545675] using wordTrace_append hprefix tailTrace_4545675
  have hstable : (prefixWord ++ tailWord_4545675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4545675).length < 2 ^ (prefixWord ++ tailWord_4545675).sum := by decide
  have hdescent : baseEnd_4545675 < baseStart_4545675 := by decide
  rcases family_descends (prefixWord ++ tailWord_4545675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4545682 : List Nat := [3, 2, 3, 1, 1, 2, 1, 2, 3, 1, 4]
def baseStart_4545682 : Nat := 118140960795 + 4545682 * 2 ^ 59
def prefixEnd_4545682 : Nat := 4983230072969 + 3 ^ 40 * 4545682 * 2
def baseEnd_4545682 : Nat := 2334119768491189231969795

theorem tailTrace_4545682 : CollatzResearch.WordTrace tailWord_4545682 prefixEnd_4545682 2334119768491189231969795 := by
  unfold tailWord_4545682
  simp only [CollatzResearch.WordTrace]
  refine ⟨41448660779444482380767825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110529762078518619682047533 41448660779444482380767825)
  ·
    refine ⟨31086495584583361785575869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41448660779444482380767825 31086495584583361785575869)
    ·
      refine ⟨11657435844218760669590951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31086495584583361785575869 11657435844218760669590951)
      ·
        refine ⟨17486153766328141004386427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11657435844218760669590951 17486153766328141004386427)
        ·
          refine ⟨26229230649492211506579641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17486153766328141004386427 26229230649492211506579641)
          ·
            refine ⟨19671922987119158629934731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26229230649492211506579641 19671922987119158629934731)
            ·
              refine ⟨29507884480678737944902097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19671922987119158629934731 29507884480678737944902097)
              ·
                refine ⟨22130913360509053458676573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29507884480678737944902097 22130913360509053458676573)
                ·
                  refine ⟨8299092510190895047003715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22130913360509053458676573 8299092510190895047003715)
                  ·
                    refine ⟨12448638765286342570505573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8299092510190895047003715 12448638765286342570505573)
                    ·
                      refine ⟨2334119768491189231969795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12448638765286342570505573 2334119768491189231969795)
                      ·
                        rfl

theorem cell23_4545682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_4545682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4545682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4545682 prefixEnd_4545682 := by exact prefixLift 4545682
  have htrace : WordTrace (prefixWord ++ tailWord_4545682) baseStart_4545682 baseEnd_4545682 := by
    simpa [prefixWord, tailWord_4545682, baseEnd_4545682] using wordTrace_append hprefix tailTrace_4545682
  have hstable : (prefixWord ++ tailWord_4545682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4545682).length < 2 ^ (prefixWord ++ tailWord_4545682).sum := by decide
  have hdescent : baseEnd_4545682 < baseStart_4545682 := by decide
  rcases family_descends (prefixWord ++ tailWord_4545682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4545692 : List Nat := [2, 2, 3, 2, 1, 3, 2, 1, 1, 6]
def baseStart_4545692 : Nat := 118140960795 + 4545692 * 2 ^ 59
def prefixEnd_4545692 : Nat := 4983230072969 + 3 ^ 40 * 4545692 * 2
def baseEnd_4545692 : Nat := 778041634432578064281583

theorem tailTrace_4545692 : CollatzResearch.WordTrace tailWord_4545692 prefixEnd_4545692 778041634432578064281583 := by
  unfold tailWord_4545692
  simp only [CollatzResearch.WordTrace]
  refine ⟨82897503923870850615467665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110530005231827800820623553 82897503923870850615467665)
  ·
    refine ⟨62173127942903137961600749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82897503923870850615467665 62173127942903137961600749)
    ·
      refine ⟨23314922978588676735600281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62173127942903137961600749 23314922978588676735600281)
      ·
        refine ⟨17486192233941507551700211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23314922978588676735600281 17486192233941507551700211)
        ·
          refine ⟨26229288350912261327550317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17486192233941507551700211 26229288350912261327550317)
          ·
            refine ⟨9835983131592097997831369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26229288350912261327550317 9835983131592097997831369)
            ·
              refine ⟨7376987348694073498373527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9835983131592097997831369 7376987348694073498373527)
              ·
                refine ⟨11065481023041110247560291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7376987348694073498373527 11065481023041110247560291)
                ·
                  refine ⟨16598221534561665371340437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11065481023041110247560291 16598221534561665371340437)
                  ·
                    refine ⟨778041634432578064281583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16598221534561665371340437 778041634432578064281583)
                    ·
                      rfl

theorem cell23_4545692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 1, 1, 6].length) (baseStart_4545692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4545692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4545692 prefixEnd_4545692 := by exact prefixLift 4545692
  have htrace : WordTrace (prefixWord ++ tailWord_4545692) baseStart_4545692 baseEnd_4545692 := by
    simpa [prefixWord, tailWord_4545692, baseEnd_4545692] using wordTrace_append hprefix tailTrace_4545692
  have hstable : (prefixWord ++ tailWord_4545692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4545692).length < 2 ^ (prefixWord ++ tailWord_4545692).sum := by decide
  have hdescent : baseEnd_4545692 < baseStart_4545692 := by decide
  rcases family_descends (prefixWord ++ tailWord_4545692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4545726 : List Nat := [4, 2, 1, 1, 3, 3, 1, 2, 2, 4]
def baseStart_4545726 : Nat := 118140960795 + 4545726 * 2 ^ 59
def prefixEnd_4545726 : Nat := 4983230072969 + 3 ^ 40 * 4545726 * 2
def baseEnd_4545726 : Nat := 778047453879995686606531

theorem tailTrace_4545726 : CollatzResearch.WordTrace tailWord_4545726 prefixEnd_4545726 778047453879995686606531 := by
  unfold tailWord_4545726
  simp only [CollatzResearch.WordTrace]
  refine ⟨20724530991202315629709129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110530831953079016691782021 20724530991202315629709129)
  ·
    refine ⟨15543398243401736722281847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20724530991202315629709129 15543398243401736722281847)
    ·
      refine ⟨23315097365102605083422771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15543398243401736722281847 23315097365102605083422771)
      ·
        refine ⟨34972646047653907625134157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23315097365102605083422771 34972646047653907625134157)
        ·
          refine ⟨13114742267870215359425309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34972646047653907625134157 13114742267870215359425309)
          ·
            refine ⟨4918028350451330759784491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13114742267870215359425309 4918028350451330759784491)
            ·
              refine ⟨7377042525676996139676737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4918028350451330759784491 7377042525676996139676737)
              ·
                refine ⟨5532781894257747104757553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7377042525676996139676737 5532781894257747104757553)
                ·
                  refine ⟨4149586420693310328568165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5532781894257747104757553 4149586420693310328568165)
                  ·
                    refine ⟨778047453879995686606531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4149586420693310328568165 778047453879995686606531)
                    ·
                      rfl

theorem cell23_4545726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 2, 2, 4].length) (baseStart_4545726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4545726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4545726 prefixEnd_4545726 := by exact prefixLift 4545726
  have htrace : WordTrace (prefixWord ++ tailWord_4545726) baseStart_4545726 baseEnd_4545726 := by
    simpa [prefixWord, tailWord_4545726, baseEnd_4545726] using wordTrace_append hprefix tailTrace_4545726
  have hstable : (prefixWord ++ tailWord_4545726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4545726).length < 2 ^ (prefixWord ++ tailWord_4545726).sum := by decide
  have hdescent : baseEnd_4545726 < baseStart_4545726 := by decide
  rcases family_descends (prefixWord ++ tailWord_4545726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4545749 : List Nat := [1, 3, 2, 4, 1, 1, 3, 1, 1, 3, 3]
def baseStart_4545749 : Nat := 118140960795 + 4545749 * 2 ^ 59
def prefixEnd_4545749 : Nat := 4983230072969 + 3 ^ 40 * 4545749 * 2
def baseEnd_4545749 : Nat := 2334154171695040469831987

theorem tailTrace_4545749 : CollatzResearch.WordTrace tailWord_4545749 prefixEnd_4545749 2334154171695040469831987 := by
  unfold tailWord_4545749
  simp only [CollatzResearch.WordTrace]
  refine ⟨165797086808535199965760301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110531391205690133310506867 165797086808535199965760301)
  ·
    refine ⟨62173907553200699987160113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165797086808535199965760301 62173907553200699987160113)
    ·
      refine ⟨46630430664900524990370085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62173907553200699987160113 46630430664900524990370085)
      ·
        refine ⟨8743205749668848435694391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46630430664900524990370085 8743205749668848435694391)
        ·
          refine ⟨13114808624503272653541587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8743205749668848435694391 13114808624503272653541587)
          ·
            refine ⟨19672212936754908980312381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13114808624503272653541587 19672212936754908980312381)
            ·
              refine ⟨7377079851283090867617143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19672212936754908980312381 7377079851283090867617143)
              ·
                refine ⟨11065619776924636301425715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7377079851283090867617143 11065619776924636301425715)
                ·
                  refine ⟨16598429665386954452138573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11065619776924636301425715 16598429665386954452138573)
                  ·
                    refine ⟨6224411124520107919551965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16598429665386954452138573 6224411124520107919551965)
                    ·
                      refine ⟨2334154171695040469831987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6224411124520107919551965 2334154171695040469831987)
                      ·
                        rfl

theorem cell23_4545749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_4545749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4545749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4545749 prefixEnd_4545749 := by exact prefixLift 4545749
  have htrace : WordTrace (prefixWord ++ tailWord_4545749) baseStart_4545749 baseEnd_4545749 := by
    simpa [prefixWord, tailWord_4545749, baseEnd_4545749] using wordTrace_append hprefix tailTrace_4545749
  have hstable : (prefixWord ++ tailWord_4545749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4545749).length < 2 ^ (prefixWord ++ tailWord_4545749).sum := by decide
  have hdescent : baseEnd_4545749 < baseStart_4545749 := by decide
  rcases family_descends (prefixWord ++ tailWord_4545749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4545759 : List Nat := [1, 1, 2, 3, 2, 1, 3, 4, 1, 3, 2]
def baseStart_4545759 : Nat := 118140960795 + 4545759 * 2 ^ 59
def prefixEnd_4545759 : Nat := 4983230072969 + 3 ^ 40 * 4545759 * 2
def baseEnd_4545759 : Nat := 2334159306501585430706941

theorem tailTrace_4545759 : CollatzResearch.WordTrace tailWord_4545759 prefixEnd_4545759 2334159306501585430706941 := by
  unfold tailWord_4545759
  simp only [CollatzResearch.WordTrace]
  refine ⟨165797451538498971673624331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110531634358999314449082887 165797451538498971673624331)
  ·
    refine ⟨248696177307748457510436497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165797451538498971673624331 248696177307748457510436497)
    ·
      refine ⟨186522132980811343132827373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 248696177307748457510436497 186522132980811343132827373)
      ·
        refine ⟨69945799867804253674810265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 186522132980811343132827373 69945799867804253674810265)
        ·
          refine ⟨52459349900853190256107699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69945799867804253674810265 52459349900853190256107699)
          ·
            refine ⟨78689024851279785384161549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52459349900853190256107699 78689024851279785384161549)
            ·
              refine ⟨29508384319229919519060581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78689024851279785384161549 29508384319229919519060581)
              ·
                refine ⟨5532822059855609909823859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29508384319229919519060581 5532822059855609909823859)
                ·
                  refine ⟨8299233089783414864735789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5532822059855609909823859 8299233089783414864735789)
                  ·
                    refine ⟨3112212408668780574275921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8299233089783414864735789 3112212408668780574275921)
                    ·
                      refine ⟨2334159306501585430706941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3112212408668780574275921 2334159306501585430706941)
                      ·
                        rfl

theorem cell23_4545759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 4, 1, 3, 2].length) (baseStart_4545759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4545759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4545759 prefixEnd_4545759 := by exact prefixLift 4545759
  have htrace : WordTrace (prefixWord ++ tailWord_4545759) baseStart_4545759 baseEnd_4545759 := by
    simpa [prefixWord, tailWord_4545759, baseEnd_4545759] using wordTrace_append hprefix tailTrace_4545759
  have hstable : (prefixWord ++ tailWord_4545759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4545759).length < 2 ^ (prefixWord ++ tailWord_4545759).sum := by decide
  have hdescent : baseEnd_4545759 < baseStart_4545759 := by decide
  rcases family_descends (prefixWord ++ tailWord_4545759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4545767 : List Nat := [1, 1, 5, 3, 3, 1, 1, 3, 1, 2, 2]
def baseStart_4545767 : Nat := 118140960795 + 4545767 * 2 ^ 59
def prefixEnd_4545767 : Nat := 4983230072969 + 3 ^ 40 * 4545767 * 2
def baseEnd_4545767 : Nat := 2334163414346821399406905

theorem tailTrace_4545767 : CollatzResearch.WordTrace tailWord_4545767 prefixEnd_4545767 2334163414346821399406905 := by
  unfold tailWord_4545767
  simp only [CollatzResearch.WordTrace]
  refine ⟨165797743322469989039915555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110531828881646659359943703 165797743322469989039915555)
  ·
    refine ⟨248696614983704983559873333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165797743322469989039915555 248696614983704983559873333)
    ·
      refine ⟨23315307654722342208738125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 248696614983704983559873333 23315307654722342208738125)
      ·
        refine ⟨8743240370520878328276797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23315307654722342208738125 8743240370520878328276797)
        ·
          refine ⟨3278715138945329373103799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8743240370520878328276797 3278715138945329373103799)
          ·
            refine ⟨4918072708417994059655699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3278715138945329373103799 4918072708417994059655699)
            ·
              refine ⟨7377109062626991089483549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4918072708417994059655699 7377109062626991089483549)
              ·
                refine ⟨2766415898485121658556331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7377109062626991089483549 2766415898485121658556331)
                ·
                  refine ⟨4149623847727682487834497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2766415898485121658556331 4149623847727682487834497)
                  ·
                    refine ⟨3112217885795761865875873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4149623847727682487834497 3112217885795761865875873)
                    ·
                      refine ⟨2334163414346821399406905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3112217885795761865875873 2334163414346821399406905)
                      ·
                        rfl

theorem cell23_4545767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_4545767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4545767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4545767 prefixEnd_4545767 := by exact prefixLift 4545767
  have htrace : WordTrace (prefixWord ++ tailWord_4545767) baseStart_4545767 baseEnd_4545767 := by
    simpa [prefixWord, tailWord_4545767, baseEnd_4545767] using wordTrace_append hprefix tailTrace_4545767
  have hstable : (prefixWord ++ tailWord_4545767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4545767).length < 2 ^ (prefixWord ++ tailWord_4545767).sum := by decide
  have hdescent : baseEnd_4545767 < baseStart_4545767 := by decide
  rcases family_descends (prefixWord ++ tailWord_4545767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4545800 : List Nat := [2, 1, 3, 2, 5, 1, 2, 1, 2, 1, 3]
def baseStart_4545800 : Nat := 118140960795 + 4545800 * 2 ^ 59
def prefixEnd_4545800 : Nat := 4983230072969 + 3 ^ 40 * 4545800 * 2
def baseEnd_4545800 : Nat := 2334180359208419770294253

theorem tailTrace_4545800 : CollatzResearch.WordTrace tailWord_4545800 prefixEnd_4545800 2334180359208419770294253 := by
  unfold tailWord_4545800
  simp only [CollatzResearch.WordTrace]
  refine ⟨82899473465675217837933427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110532631287566957117244569 82899473465675217837933427)
  ·
    refine ⟨124349210198512826756900141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82899473465675217837933427 124349210198512826756900141)
    ·
      refine ⟨46630953824442310033837553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124349210198512826756900141 46630953824442310033837553)
      ·
        refine ⟨34973215368331732525378165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46630953824442310033837553 34973215368331732525378165)
        ·
          refine ⟨3278738940781099924254203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34973215368331732525378165 3278738940781099924254203)
          ·
            refine ⟨4918108411171649886381305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3278738940781099924254203 4918108411171649886381305)
            ·
              refine ⟨3688581308378737414785979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4918108411171649886381305 3688581308378737414785979)
              ·
                refine ⟨5532871962568106122178969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3688581308378737414785979 5532871962568106122178969)
                ·
                  refine ⟨4149653971926079591634227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5532871962568106122178969 4149653971926079591634227)
                  ·
                    refine ⟨6224480957889119387451341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4149653971926079591634227 6224480957889119387451341)
                    ·
                      refine ⟨2334180359208419770294253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6224480957889119387451341 2334180359208419770294253)
                      ·
                        rfl

theorem cell23_4545800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 2, 1, 2, 1, 3].length) (baseStart_4545800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4545800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4545800 prefixEnd_4545800 := by exact prefixLift 4545800
  have htrace : WordTrace (prefixWord ++ tailWord_4545800) baseStart_4545800 baseEnd_4545800 := by
    simpa [prefixWord, tailWord_4545800, baseEnd_4545800] using wordTrace_append hprefix tailTrace_4545800
  have hstable : (prefixWord ++ tailWord_4545800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4545800).length < 2 ^ (prefixWord ++ tailWord_4545800).sum := by decide
  have hdescent : baseEnd_4545800 < baseStart_4545800 := by decide
  rcases family_descends (prefixWord ++ tailWord_4545800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4545852 : List Nat := [2, 2, 2, 2, 1, 3, 2, 1, 1, 2, 5]
def baseStart_4545852 : Nat := 118140960795 + 4545852 * 2 ^ 59
def prefixEnd_4545852 : Nat := 4983230072969 + 3 ^ 40 * 4545852 * 2
def baseEnd_4545852 : Nat := 2334207060202453566844013

theorem tailTrace_4545852 : CollatzResearch.WordTrace tailWord_4545852 prefixEnd_4545852 2334207060202453566844013 := by
  unfold tailWord_4545852
  simp only [CollatzResearch.WordTrace]
  refine ⟨82900421763581024278379905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110533895684774699037839873 82900421763581024278379905)
  ·
    refine ⟨62175316322685768208784929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82900421763581024278379905 62175316322685768208784929)
    ·
      refine ⟨46631487242014326156588697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62175316322685768208784929 46631487242014326156588697)
      ·
        refine ⟨34973615431510744617441523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46631487242014326156588697 34973615431510744617441523)
        ·
          refine ⟨52460423147266116926162285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34973615431510744617441523 52460423147266116926162285)
          ·
            refine ⟨19672658680224793847310857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52460423147266116926162285 19672658680224793847310857)
            ·
              refine ⟨14754494010168595385483143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19672658680224793847310857 14754494010168595385483143)
              ·
                refine ⟨22131741015252893078224715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14754494010168595385483143 22131741015252893078224715)
                ·
                  refine ⟨33197611522879339617337073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22131741015252893078224715 33197611522879339617337073)
                  ·
                    refine ⟨24898208642159504713002805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33197611522879339617337073 24898208642159504713002805)
                    ·
                      refine ⟨2334207060202453566844013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24898208642159504713002805 2334207060202453566844013)
                      ·
                        rfl

theorem cell23_4545852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_4545852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4545852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4545852 prefixEnd_4545852 := by exact prefixLift 4545852
  have htrace : WordTrace (prefixWord ++ tailWord_4545852) baseStart_4545852 baseEnd_4545852 := by
    simpa [prefixWord, tailWord_4545852, baseEnd_4545852] using wordTrace_append hprefix tailTrace_4545852
  have hstable : (prefixWord ++ tailWord_4545852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4545852).length < 2 ^ (prefixWord ++ tailWord_4545852).sum := by decide
  have hdescent : baseEnd_4545852 < baseStart_4545852 := by decide
  rcases family_descends (prefixWord ++ tailWord_4545852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4545879 : List Nat := [1, 1, 3, 2, 3, 2, 3, 1, 2, 1, 4]
def baseStart_4545879 : Nat := 118140960795 + 4545879 * 2 ^ 59
def prefixEnd_4545879 : Nat := 4983230072969 + 3 ^ 40 * 4545879 * 2
def baseEnd_4545879 : Nat := 2334220924180124961206389

theorem tailTrace_4545879 : CollatzResearch.WordTrace tailWord_4545879 prefixEnd_4545879 2334220924180124961206389 := by
  unfold tailWord_4545879
  simp only [CollatzResearch.WordTrace]
  refine ⟨165801828298064232167992691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110534552198709488111995127 165801828298064232167992691)
  ·
    refine ⟨248702742447096348251989037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165801828298064232167992691 248702742447096348251989037)
    ·
      refine ⟨93263528417661130594495889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 248702742447096348251989037 93263528417661130594495889)
      ·
        refine ⟨69947646313245847945871917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93263528417661130594495889 69947646313245847945871917)
        ·
          refine ⟨26230367367467192979701969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69947646313245847945871917 26230367367467192979701969)
          ·
            refine ⟨19672775525600394734776477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26230367367467192979701969 19672775525600394734776477)
            ·
              refine ⟨7377290822100148025541179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19672775525600394734776477 7377290822100148025541179)
              ·
                refine ⟨11065936233150222038311769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7377290822100148025541179 11065936233150222038311769)
                ·
                  refine ⟨8299452174862666528733827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11065936233150222038311769 8299452174862666528733827)
                  ·
                    refine ⟨12449178262293999793100741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8299452174862666528733827 12449178262293999793100741)
                    ·
                      refine ⟨2334220924180124961206389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12449178262293999793100741 2334220924180124961206389)
                      ·
                        rfl

theorem cell23_4545879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 1, 2, 1, 4].length) (baseStart_4545879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4545879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4545879 prefixEnd_4545879 := by exact prefixLift 4545879
  have htrace : WordTrace (prefixWord ++ tailWord_4545879) baseStart_4545879 baseEnd_4545879 := by
    simpa [prefixWord, tailWord_4545879, baseEnd_4545879] using wordTrace_append hprefix tailTrace_4545879
  have hstable : (prefixWord ++ tailWord_4545879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4545879).length < 2 ^ (prefixWord ++ tailWord_4545879).sum := by decide
  have hdescent : baseEnd_4545879 < baseStart_4545879 := by decide
  rcases family_descends (prefixWord ++ tailWord_4545879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4545892 : List Nat := [2, 3, 1, 1, 3, 2, 1, 1, 2, 1, 6]
def baseStart_4545892 : Nat := 118140960795 + 4545892 * 2 ^ 59
def prefixEnd_4545892 : Nat := 4983230072969 + 3 ^ 40 * 4545892 * 2
def baseEnd_4545892 : Nat := 2334227599428633410343829

theorem tailTrace_4545892 : CollatzResearch.WordTrace tailWord_4545892 prefixEnd_4545892 2334227599428633410343829 := by
  unfold tailWord_4545892
  simp only [CollatzResearch.WordTrace]
  refine ⟨82901151223508567694107965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110534868298011423592143953 82901151223508567694107965)
  ·
    refine ⟨31087931708815712885290487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82901151223508567694107965 31087931708815712885290487)
    ·
      refine ⟨46631897563223569327935731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31087931708815712885290487 46631897563223569327935731)
      ·
        refine ⟨69947846344835353991903597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46631897563223569327935731 69947846344835353991903597)
        ·
          refine ⟨26230442379313257746963849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69947846344835353991903597 26230442379313257746963849)
          ·
            refine ⟨19672831784484943310222887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26230442379313257746963849 19672831784484943310222887)
            ·
              refine ⟨29509247676727414965334331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19672831784484943310222887 29509247676727414965334331)
              ·
                refine ⟨44263871515091122448001497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29509247676727414965334331 44263871515091122448001497)
                ·
                  refine ⟨33197903636318341836001123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44263871515091122448001497 33197903636318341836001123)
                  ·
                    refine ⟨49796855454477512754001685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33197903636318341836001123 49796855454477512754001685)
                    ·
                      refine ⟨2334227599428633410343829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49796855454477512754001685 2334227599428633410343829)
                      ·
                        rfl

theorem cell23_4545892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 2, 1, 6].length) (baseStart_4545892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4545892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4545892 prefixEnd_4545892 := by exact prefixLift 4545892
  have htrace : WordTrace (prefixWord ++ tailWord_4545892) baseStart_4545892 baseEnd_4545892 := by
    simpa [prefixWord, tailWord_4545892, baseEnd_4545892] using wordTrace_append hprefix tailTrace_4545892
  have hstable : (prefixWord ++ tailWord_4545892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4545892).length < 2 ^ (prefixWord ++ tailWord_4545892).sum := by decide
  have hdescent : baseEnd_4545892 < baseStart_4545892 := by decide
  rcases family_descends (prefixWord ++ tailWord_4545892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4545906 : List Nat := [3, 2, 1, 2, 1, 2, 1, 6, 1, 4]
def baseStart_4545906 : Nat := 118140960795 + 4545906 * 2 ^ 59
def prefixEnd_4545906 : Nat := 4983230072969 + 3 ^ 40 * 4545906 * 2
def baseEnd_4545906 : Nat := 778078262719265451856255

theorem tailTrace_4545906 : CollatzResearch.WordTrace tailWord_4545906 prefixEnd_4545906 778078262719265451856255 := by
  unfold tailWord_4545906
  simp only [CollatzResearch.WordTrace]
  refine ⟨41450703267241603944806393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110535208712644277186150381 41450703267241603944806393)
  ·
    refine ⟨31088027450431202958604795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41450703267241603944806393 31088027450431202958604795)
    ·
      refine ⟨46632041175646804437907193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31088027450431202958604795 46632041175646804437907193)
      ·
        refine ⟨34974030881735103328430395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46632041175646804437907193 34974030881735103328430395)
        ·
          refine ⟨52461046322602654992645593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34974030881735103328430395 52461046322602654992645593)
          ·
            refine ⟨39345784741951991244484195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52461046322602654992645593 39345784741951991244484195)
            ·
              refine ⟨59018677112927986866726293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39345784741951991244484195 59018677112927986866726293)
              ·
                refine ⟨2766500489668499384377795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 59018677112927986866726293 2766500489668499384377795)
                ·
                  refine ⟨4149750734502749076566693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2766500489668499384377795 4149750734502749076566693)
                  ·
                    refine ⟨778078262719265451856255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4149750734502749076566693 778078262719265451856255)
                    ·
                      rfl

theorem cell23_4545906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 6, 1, 4].length) (baseStart_4545906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4545906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4545906 prefixEnd_4545906 := by exact prefixLift 4545906
  have htrace : WordTrace (prefixWord ++ tailWord_4545906) baseStart_4545906 baseEnd_4545906 := by
    simpa [prefixWord, tailWord_4545906, baseEnd_4545906] using wordTrace_append hprefix tailTrace_4545906
  have hstable : (prefixWord ++ tailWord_4545906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4545906).length < 2 ^ (prefixWord ++ tailWord_4545906).sum := by decide
  have hdescent : baseEnd_4545906 < baseStart_4545906 := by decide
  rcases family_descends (prefixWord ++ tailWord_4545906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4545939 : List Nat := [1, 1, 1, 2, 1, 2, 1, 1, 8, 3, 2]
def baseStart_4545939 : Nat := 118140960795 + 4545939 * 2 ^ 59
def prefixEnd_4545939 : Nat := 4983230072969 + 3 ^ 40 * 4545939 * 2
def baseEnd_4545939 : Nat := 2334251733019394726456113

theorem tailTrace_4545939 : CollatzResearch.WordTrace tailWord_4545939 prefixEnd_4545939 2334251733019394726456113 := by
  unfold tailWord_4545939
  simp only [CollatzResearch.WordTrace]
  refine ⟨165804016677846862415176871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110536011118564574943451247 165804016677846862415176871)
  ·
    refine ⟨248706025016770293622765307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165804016677846862415176871 248706025016770293622765307)
    ·
      refine ⟨373059037525155440434147961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248706025016770293622765307 373059037525155440434147961)
      ·
        refine ⟨279794278143866580325610971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 373059037525155440434147961 279794278143866580325610971)
        ·
          refine ⟨419691417215799870488416457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 279794278143866580325610971 419691417215799870488416457)
          ·
            refine ⟨314768562911849902866312343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 419691417215799870488416457 314768562911849902866312343)
            ·
              refine ⟨472152844367774854299468515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 314768562911849902866312343 472152844367774854299468515)
              ·
                refine ⟨708229266551662281449202773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 472152844367774854299468515 708229266551662281449202773)
                ·
                  refine ⟨8299561717402292360732845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 708229266551662281449202773 8299561717402292360732845)
                  ·
                    refine ⟨3112335644025859635274817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8299561717402292360732845 3112335644025859635274817)
                    ·
                      refine ⟨2334251733019394726456113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3112335644025859635274817 2334251733019394726456113)
                      ·
                        rfl

theorem cell23_4545939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 8, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 8, 3, 2].length) (baseStart_4545939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4545939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4545939 prefixEnd_4545939 := by exact prefixLift 4545939
  have htrace : WordTrace (prefixWord ++ tailWord_4545939) baseStart_4545939 baseEnd_4545939 := by
    simpa [prefixWord, tailWord_4545939, baseEnd_4545939] using wordTrace_append hprefix tailTrace_4545939
  have hstable : (prefixWord ++ tailWord_4545939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4545939).length < 2 ^ (prefixWord ++ tailWord_4545939).sum := by decide
  have hdescent : baseEnd_4545939 < baseStart_4545939 := by decide
  rcases family_descends (prefixWord ++ tailWord_4545939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4545940 : List Nat := [2, 4, 2, 1, 2, 3, 1, 3, 1, 4]
def baseStart_4545940 : Nat := 118140960795 + 4545940 * 2 ^ 59
def prefixEnd_4545940 : Nat := 4983230072969 + 3 ^ 40 * 4545940 * 2
def baseEnd_4545940 : Nat := 778084082166683074181203

theorem tailTrace_4545940 : CollatzResearch.WordTrace tailWord_4545940 prefixEnd_4545940 778084082166683074181203 := by
  unfold tailWord_4545940
  simp only [CollatzResearch.WordTrace]
  refine ⟨82902026575421619792981637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110536035433895493057308849 82902026575421619792981637)
  ·
    refine ⟨15544129982891553711184057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82902026575421619792981637 15544129982891553711184057)
    ·
      refine ⟨11658097487168665283388043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15544129982891553711184057 11658097487168665283388043)
      ·
        refine ⟨17487146230752997925082065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11658097487168665283388043 17487146230752997925082065)
        ·
          refine ⟨13115359673064748443811549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17487146230752997925082065 13115359673064748443811549)
          ·
            refine ⟨4918259877399280666429331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13115359673064748443811549 4918259877399280666429331)
            ·
              refine ⟨7377389816098920999643997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4918259877399280666429331 7377389816098920999643997)
              ·
                refine ⟨2766521181037095374866499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7377389816098920999643997 2766521181037095374866499)
                ·
                  refine ⟨4149781771555643062299749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2766521181037095374866499 4149781771555643062299749)
                  ·
                    refine ⟨778084082166683074181203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4149781771555643062299749 778084082166683074181203)
                    ·
                      rfl

theorem cell23_4545940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_4545940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4545940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4545940 prefixEnd_4545940 := by exact prefixLift 4545940
  have htrace : WordTrace (prefixWord ++ tailWord_4545940) baseStart_4545940 baseEnd_4545940 := by
    simpa [prefixWord, tailWord_4545940, baseEnd_4545940] using wordTrace_append hprefix tailTrace_4545940
  have hstable : (prefixWord ++ tailWord_4545940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4545940).length < 2 ^ (prefixWord ++ tailWord_4545940).sum := by decide
  have hdescent : baseEnd_4545940 < baseStart_4545940 := by decide
  rcases family_descends (prefixWord ++ tailWord_4545940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4545969 : List Nat := [1, 2, 2, 4, 1, 1, 2, 2, 3, 1, 4]
def baseStart_4545969 : Nat := 118140960795 + 4545969 * 2 ^ 59
def prefixEnd_4545969 : Nat := 4983230072969 + 3 ^ 40 * 4545969 * 2
def baseEnd_4545969 : Nat := 2334267137439029609080975

theorem tailTrace_4545969 : CollatzResearch.WordTrace tailWord_4545969 prefixEnd_4545969 2334267137439029609080975 := by
  unfold tailWord_4545969
  simp only [CollatzResearch.WordTrace]
  refine ⟨165805110867738177538768961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110536740578492118359179307 165805110867738177538768961)
  ·
    refine ⟨124353833150803633154076721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165805110867738177538768961 124353833150803633154076721)
    ·
      refine ⟨93265374863102724865557541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124353833150803633154076721 93265374863102724865557541)
      ·
        refine ⟨17487257786831760912292039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 93265374863102724865557541 17487257786831760912292039)
        ·
          refine ⟨26230886680247641368438059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17487257786831760912292039 26230886680247641368438059)
          ·
            refine ⟨39346330020371462052657089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26230886680247641368438059 39346330020371462052657089)
            ·
              refine ⟨29509747515278596539492817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39346330020371462052657089 29509747515278596539492817)
              ·
                refine ⟨22132310636458947404619613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29509747515278596539492817 22132310636458947404619613)
                ·
                  refine ⟨8299616488672105276732355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22132310636458947404619613 8299616488672105276732355)
                  ·
                    refine ⟨12449424733008157915098533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8299616488672105276732355 12449424733008157915098533)
                    ·
                      refine ⟨2334267137439029609080975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12449424733008157915098533 2334267137439029609080975)
                      ·
                        rfl

theorem cell23_4545969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_4545969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4545969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4545969 prefixEnd_4545969 := by exact prefixLift 4545969
  have htrace : WordTrace (prefixWord ++ tailWord_4545969) baseStart_4545969 baseEnd_4545969 := by
    simpa [prefixWord, tailWord_4545969, baseEnd_4545969] using wordTrace_append hprefix tailTrace_4545969
  have hstable : (prefixWord ++ tailWord_4545969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4545969).length < 2 ^ (prefixWord ++ tailWord_4545969).sum := by decide
  have hdescent : baseEnd_4545969 < baseStart_4545969 := by decide
  rcases family_descends (prefixWord ++ tailWord_4545969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4545992 : List Nat := [2, 1, 3, 1, 3, 1, 1, 11]
def baseStart_4545992 : Nat := 118140960795 + 4545992 * 2 ^ 59
def prefixEnd_4545992 : Nat := 4983230072969 + 3 ^ 40 * 4545992 * 2
def baseEnd_4545992 : Nat := 86454775833114185892347

theorem tailTrace_4545992 : CollatzResearch.WordTrace tailWord_4545992 prefixEnd_4545992 86454775833114185892347 := by
  unfold tailWord_4545992
  simp only [CollatzResearch.WordTrace]
  refine ⟨82902974873327426233428115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110537299831103234977904153 82902974873327426233428115)
  ·
    refine ⟨124354462309991139350142173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82902974873327426233428115 124354462309991139350142173)
    ·
      refine ⟨46632923366246677256303315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124354462309991139350142173 46632923366246677256303315)
      ·
        refine ⟨69949385049370015884454973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46632923366246677256303315 69949385049370015884454973)
        ·
          refine ⟨26231019393513755956670615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69949385049370015884454973 26231019393513755956670615)
          ·
            refine ⟨39346529090270633935005923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26231019393513755956670615 39346529090270633935005923)
            ·
              refine ⟨59019793635405950902508885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39346529090270633935005923 59019793635405950902508885)
              ·
                refine ⟨86454775833114185892347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 59019793635405950902508885 86454775833114185892347)
                ·
                  rfl

theorem cell23_4545992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 11].length) (baseStart_4545992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4545992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4545992 prefixEnd_4545992 := by exact prefixLift 4545992
  have htrace : WordTrace (prefixWord ++ tailWord_4545992) baseStart_4545992 baseEnd_4545992 := by
    simpa [prefixWord, tailWord_4545992, baseEnd_4545992] using wordTrace_append hprefix tailTrace_4545992
  have hstable : (prefixWord ++ tailWord_4545992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4545992).length < 2 ^ (prefixWord ++ tailWord_4545992).sum := by decide
  have hdescent : baseEnd_4545992 < baseStart_4545992 := by decide
  rcases family_descends (prefixWord ++ tailWord_4545992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4546013 : List Nat := [1, 4, 3, 1, 1, 3, 2, 2, 2, 4]
def baseStart_4546013 : Nat := 118140960795 + 4546013 * 2 ^ 59
def prefixEnd_4546013 : Nat := 4983230072969 + 3 ^ 40 * 4546013 * 2
def baseEnd_4546013 : Nat := 778096576862609145643591

theorem tailTrace_4546013 : CollatzResearch.WordTrace tailWord_4546013 prefixEnd_4546013 778096576862609145643591 := by
  unfold tailWord_4546013
  simp only [CollatzResearch.WordTrace]
  refine ⟨165806715679578773053370693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110537810453052515368913795 165806715679578773053370693)
  ·
    refine ⟨31088759189921019947507005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 165806715679578773053370693 31088759189921019947507005)
    ·
      refine ⟨11658284696220382480315127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31088759189921019947507005 11658284696220382480315127)
      ·
        refine ⟨17487427044330573720472691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11658284696220382480315127 17487427044330573720472691)
        ·
          refine ⟨26231140566495860580709037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17487427044330573720472691 26231140566495860580709037)
          ·
            refine ⟨9836677712435947717765889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26231140566495860580709037 9836677712435947717765889)
            ·
              refine ⟨7377508284326960788324417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9836677712435947717765889 7377508284326960788324417)
              ·
                refine ⟨5533131213245220591243313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7377508284326960788324417 5533131213245220591243313)
                ·
                  refine ⟨4149848409933915443432485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5533131213245220591243313 4149848409933915443432485)
                  ·
                    refine ⟨778096576862609145643591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4149848409933915443432485 778096576862609145643591)
                    ·
                      rfl

theorem cell23_4546013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_4546013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4546013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4546013 prefixEnd_4546013 := by exact prefixLift 4546013
  have htrace : WordTrace (prefixWord ++ tailWord_4546013) baseStart_4546013 baseEnd_4546013 := by
    simpa [prefixWord, tailWord_4546013, baseEnd_4546013] using wordTrace_append hprefix tailTrace_4546013
  have hstable : (prefixWord ++ tailWord_4546013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4546013).length < 2 ^ (prefixWord ++ tailWord_4546013).sum := by decide
  have hdescent : baseEnd_4546013 < baseStart_4546013 := by decide
  rcases family_descends (prefixWord ++ tailWord_4546013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4546026 : List Nat := [3, 1, 3, 1, 4, 2, 1, 8]
def baseStart_4546026 : Nat := 118140960795 + 4546026 * 2 ^ 59
def prefixEnd_4546026 : Nat := 4983230072969 + 3 ^ 40 * 4546026 * 2
def baseEnd_4546026 : Nat := 86455422438382810595119

theorem tailTrace_4546026 : CollatzResearch.WordTrace tailWord_4546026 prefixEnd_4546026 86455422438382810595119 := by
  unfold tailWord_4546026
  simp only [CollatzResearch.WordTrace]
  refine ⟨41451797457132919068398483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110538126552354450849062621 41451797457132919068398483)
  ·
    refine ⟨62177696185699378602597725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41451797457132919068398483 62177696185699378602597725)
    ·
      refine ⟨23316636069637266975974147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62177696185699378602597725 23316636069637266975974147)
      ·
        refine ⟨34974954104455900463961221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23316636069637266975974147 34974954104455900463961221)
        ·
          refine ⟨6557803894585481336992729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34974954104455900463961221 6557803894585481336992729)
          ·
            refine ⟨4918352920939111002744547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6557803894585481336992729 4918352920939111002744547)
            ·
              refine ⟨7377529381408666504116821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4918352920939111002744547 7377529381408666504116821)
              ·
                refine ⟨86455422438382810595119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7377529381408666504116821 86455422438382810595119)
                ·
                  rfl

theorem cell23_4546026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 8].length) (baseStart_4546026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4546026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4546026 prefixEnd_4546026 := by exact prefixLift 4546026
  have htrace : WordTrace (prefixWord ++ tailWord_4546026) baseStart_4546026 baseEnd_4546026 := by
    simpa [prefixWord, tailWord_4546026, baseEnd_4546026] using wordTrace_append hprefix tailTrace_4546026
  have hstable : (prefixWord ++ tailWord_4546026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4546026).length < 2 ^ (prefixWord ++ tailWord_4546026).sum := by decide
  have hdescent : baseEnd_4546026 < baseStart_4546026 := by decide
  rcases family_descends (prefixWord ++ tailWord_4546026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4546069 : List Nat := [1, 3, 2, 1, 3, 2, 1, 2, 2, 6]
def baseStart_4546069 : Nat := 118140960795 + 4546069 * 2 ^ 59
def prefixEnd_4546069 : Nat := 4983230072969 + 3 ^ 40 * 4546069 * 2
def baseEnd_4546069 : Nat := 778106161834826405943505

theorem tailTrace_4546069 : CollatzResearch.WordTrace tailWord_4546069 prefixEnd_4546069 778106161834826405943505 := by
  unfold tailWord_4546069
  simp only [CollatzResearch.WordTrace]
  refine ⟨165808758167375894617409261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110539172111583929744939507 165808758167375894617409261)
  ·
    refine ⟨62178284312765960481528473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165808758167375894617409261 62178284312765960481528473)
    ·
      refine ⟨46633713234574470361146355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62178284312765960481528473 46633713234574470361146355)
      ·
        refine ⟨69950569851861705541719533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46633713234574470361146355 69950569851861705541719533)
        ·
          refine ⟨26231463694448139578144825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69950569851861705541719533 26231463694448139578144825)
          ·
            refine ⟨19673597770836104683608619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26231463694448139578144825 19673597770836104683608619)
            ·
              refine ⟨29510396656254157025412929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19673597770836104683608619 29510396656254157025412929)
              ·
                refine ⟨22132797492190617769059697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29510396656254157025412929 22132797492190617769059697)
                ·
                  refine ⟨16599598119142963326794773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22132797492190617769059697 16599598119142963326794773)
                  ·
                    refine ⟨778106161834826405943505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16599598119142963326794773 778106161834826405943505)
                    ·
                      rfl

theorem cell23_4546069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 2, 2, 6].length) (baseStart_4546069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4546069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4546069 prefixEnd_4546069 := by exact prefixLift 4546069
  have htrace : WordTrace (prefixWord ++ tailWord_4546069) baseStart_4546069 baseEnd_4546069 := by
    simpa [prefixWord, tailWord_4546069, baseEnd_4546069] using wordTrace_append hprefix tailTrace_4546069
  have hstable : (prefixWord ++ tailWord_4546069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4546069).length < 2 ^ (prefixWord ++ tailWord_4546069).sum := by decide
  have hdescent : baseEnd_4546069 < baseStart_4546069 := by decide
  rcases family_descends (prefixWord ++ tailWord_4546069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4546079 : List Nat := [1, 1, 2, 4, 1, 1, 2, 1, 1, 6, 3]
def baseStart_4546079 : Nat := 118140960795 + 4546079 * 2 ^ 59
def prefixEnd_4546079 : Nat := 4983230072969 + 3 ^ 40 * 4546079 * 2
def baseEnd_4546079 : Nat := 2334323620311024178705469

theorem tailTrace_4546079 : CollatzResearch.WordTrace tailWord_4546079 prefixEnd_4546079 2334323620311024178705469 := by
  unfold tailWord_4546079
  simp only [CollatzResearch.WordTrace]
  refine ⟨165809122897339666325273291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110539415264893110883515527 165809122897339666325273291)
  ·
    refine ⟨248713684346009499487909937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165809122897339666325273291 248713684346009499487909937)
    ·
      refine ⟨186535263259507124615932453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 248713684346009499487909937 186535263259507124615932453)
      ·
        refine ⟨34975361861157585865487335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 186535263259507124615932453 34975361861157585865487335)
        ·
          refine ⟨52463042791736378798231003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34975361861157585865487335 52463042791736378798231003)
          ·
            refine ⟨78694564187604568197346505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52463042791736378798231003 78694564187604568197346505)
            ·
              refine ⟨59020923140703426148009879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78694564187604568197346505 59020923140703426148009879)
              ·
                refine ⟨88531384711055139222014819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59020923140703426148009879 88531384711055139222014819)
                ·
                  refine ⟨132797077066582708833022229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 88531384711055139222014819 132797077066582708833022229)
                  ·
                    refine ⟨6224862987496064476547917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 132797077066582708833022229 6224862987496064476547917)
                    ·
                      refine ⟨2334323620311024178705469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6224862987496064476547917 2334323620311024178705469)
                      ·
                        rfl

theorem cell23_4546079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 6, 3].length) (baseStart_4546079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4546079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4546079 prefixEnd_4546079 := by exact prefixLift 4546079
  have htrace : WordTrace (prefixWord ++ tailWord_4546079) baseStart_4546079 baseEnd_4546079 := by
    simpa [prefixWord, tailWord_4546079, baseEnd_4546079] using wordTrace_append hprefix tailTrace_4546079
  have hstable : (prefixWord ++ tailWord_4546079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4546079).length < 2 ^ (prefixWord ++ tailWord_4546079).sum := by decide
  have hdescent : baseEnd_4546079 < baseStart_4546079 := by decide
  rcases family_descends (prefixWord ++ tailWord_4546079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4546099 : List Nat := [1, 1, 1, 2, 4, 3, 2, 2, 7]
def baseStart_4546099 : Nat := 118140960795 + 4546099 * 2 ^ 59
def prefixEnd_4546099 : Nat := 4983230072969 + 3 ^ 40 * 4546099 * 2
def baseEnd_4546099 : Nat := 259370432213790455606153

theorem tailTrace_4546099 : CollatzResearch.WordTrace tailWord_4546099 prefixEnd_4546099 259370432213790455606153 := by
  unfold tailWord_4546099
  simp only [CollatzResearch.WordTrace]
  refine ⟨165809852357267209741001351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110539901571511473160667567 165809852357267209741001351)
  ·
    refine ⟨248714778535900814611502027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165809852357267209741001351 248714778535900814611502027)
    ·
      refine ⟨373072167803851221917253041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248714778535900814611502027 373072167803851221917253041)
      ·
        refine ⟨279804125852888416437939781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 373072167803851221917253041 279804125852888416437939781)
        ·
          refine ⟨52463273597416578082113709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 279804125852888416437939781 52463273597416578082113709)
          ·
            refine ⟨19673727599031216780792641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52463273597416578082113709 19673727599031216780792641)
            ·
              refine ⟨14755295699273412585594481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19673727599031216780792641 14755295699273412585594481)
              ·
                refine ⟨11066471774455059439195861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14755295699273412585594481 11066471774455059439195861)
                ·
                  refine ⟨259370432213790455606153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11066471774455059439195861 259370432213790455606153)
                  ·
                    rfl

theorem cell23_4546099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 2, 7].length) (baseStart_4546099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4546099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4546099 prefixEnd_4546099 := by exact prefixLift 4546099
  have htrace : WordTrace (prefixWord ++ tailWord_4546099) baseStart_4546099 baseEnd_4546099 := by
    simpa [prefixWord, tailWord_4546099, baseEnd_4546099] using wordTrace_append hprefix tailTrace_4546099
  have hstable : (prefixWord ++ tailWord_4546099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4546099).length < 2 ^ (prefixWord ++ tailWord_4546099).sum := by decide
  have hdescent : baseEnd_4546099 < baseStart_4546099 := by decide
  rcases family_descends (prefixWord ++ tailWord_4546099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4546136 : List Nat := [2, 1, 2, 2, 1, 2, 1, 3, 2, 5, 2]
def baseStart_4546136 : Nat := 118140960795 + 4546136 * 2 ^ 59
def prefixEnd_4546136 : Nat := 4983230072969 + 3 ^ 40 * 4546136 * 2
def baseEnd_4546136 : Nat := 2334352888708330455692707

theorem tailTrace_4546136 : CollatzResearch.WordTrace tailWord_4546136 prefixEnd_4546136 2334352888708330455692707 := by
  unfold tailWord_4546136
  simp only [CollatzResearch.WordTrace]
  refine ⟨82905600929066582530049131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110540801238755443373398841 82905600929066582530049131)
  ·
    refine ⟨124358401393599873795073697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82905600929066582530049131 124358401393599873795073697)
    ·
      refine ⟨93268801045199905346305273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124358401393599873795073697 93268801045199905346305273)
      ·
        refine ⟨69951600783899929009728955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93268801045199905346305273 69951600783899929009728955)
        ·
          refine ⟨104927401175849893514593433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69951600783899929009728955 104927401175849893514593433)
          ·
            refine ⟨78695550881887420135945075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104927401175849893514593433 78695550881887420135945075)
            ·
              refine ⟨118043326322831130203917613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78695550881887420135945075 118043326322831130203917613)
              ·
                refine ⟨44266247371061673826469105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 118043326322831130203917613 44266247371061673826469105)
                ·
                  refine ⟨33199685528296255369851829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44266247371061673826469105 33199685528296255369851829)
                  ·
                    refine ⟨3112470518277773940923609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33199685528296255369851829 3112470518277773940923609)
                    ·
                      refine ⟨2334352888708330455692707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3112470518277773940923609 2334352888708330455692707)
                      ·
                        rfl

theorem cell23_4546136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 2, 5, 2].length) (baseStart_4546136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4546136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4546136 prefixEnd_4546136 := by exact prefixLift 4546136
  have htrace : WordTrace (prefixWord ++ tailWord_4546136) baseStart_4546136 baseEnd_4546136 := by
    simpa [prefixWord, tailWord_4546136, baseEnd_4546136] using wordTrace_append hprefix tailTrace_4546136
  have hstable : (prefixWord ++ tailWord_4546136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4546136).length < 2 ^ (prefixWord ++ tailWord_4546136).sum := by decide
  have hdescent : baseEnd_4546136 < baseStart_4546136 := by decide
  rcases family_descends (prefixWord ++ tailWord_4546136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4546179 : List Nat := [1, 1, 1, 3, 3, 1, 1, 3, 2, 1, 6]
def baseStart_4546179 : Nat := 118140960795 + 4546179 * 2 ^ 59
def prefixEnd_4546179 : Nat := 4983230072969 + 3 ^ 40 * 4546179 * 2
def baseEnd_4546179 : Nat := 2334374968376473787455009

theorem tailTrace_4546179 : CollatzResearch.WordTrace tailWord_4546179 prefixEnd_4546179 2334374968376473787455009 := by
  unfold tailWord_4546179
  simp only [CollatzResearch.WordTrace]
  refine ⟨165812770196977383403913591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110541846797984922269275727 165812770196977383403913591)
  ·
    refine ⟨248719155295466075105870387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165812770196977383403913591 248719155295466075105870387)
    ·
      refine ⟨373078732943199112658805581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248719155295466075105870387 373078732943199112658805581)
      ·
        refine ⟨139904524853699667247052093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 373078732943199112658805581 139904524853699667247052093)
        ·
          refine ⟨52464196820137375217644535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 139904524853699667247052093 52464196820137375217644535)
          ·
            refine ⟨78696295230206062826466803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52464196820137375217644535 78696295230206062826466803)
            ·
              refine ⟨118044442845309094239700205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78696295230206062826466803 118044442845309094239700205)
              ·
                refine ⟨44266666066990910339887577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 118044442845309094239700205 44266666066990910339887577)
                ·
                  refine ⟨33199999550243182754915683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44266666066990910339887577 33199999550243182754915683)
                  ·
                    refine ⟨49799999325364774132373525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33199999550243182754915683 49799999325364774132373525)
                    ·
                      refine ⟨2334374968376473787455009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49799999325364774132373525 2334374968376473787455009)
                      ·
                        rfl

theorem cell23_4546179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 2, 1, 6].length) (baseStart_4546179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4546179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4546179 prefixEnd_4546179 := by exact prefixLift 4546179
  have htrace : WordTrace (prefixWord ++ tailWord_4546179) baseStart_4546179 baseEnd_4546179 := by
    simpa [prefixWord, tailWord_4546179, baseEnd_4546179] using wordTrace_append hprefix tailTrace_4546179
  have hstable : (prefixWord ++ tailWord_4546179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4546179).length < 2 ^ (prefixWord ++ tailWord_4546179).sum := by decide
  have hdescent : baseEnd_4546179 < baseStart_4546179 := by decide
  rcases family_descends (prefixWord ++ tailWord_4546179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4546184 : List Nat := [2, 1, 3, 5, 2, 1, 2, 2, 5]
def baseStart_4546184 : Nat := 118140960795 + 4546184 * 2 ^ 59
def prefixEnd_4546184 : Nat := 4983230072969 + 3 ^ 40 * 4546184 * 2
def baseEnd_4546184 : Nat := 259375281753305140876943

theorem tailTrace_4546184 : CollatzResearch.WordTrace tailWord_4546184 prefixEnd_4546184 259375281753305140876943 := by
  unfold tailWord_4546184
  simp only [CollatzResearch.WordTrace]
  refine ⟨82906476280979634628922803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110541968374639512838563737 82906476280979634628922803)
  ·
    refine ⟨124359714421469451943384205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82906476280979634628922803 124359714421469451943384205)
    ·
      refine ⟨46634892908051044478769077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124359714421469451943384205 46634892908051044478769077)
      ·
        refine ⟨4372021210129785419884601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46634892908051044478769077 4372021210129785419884601)
        ·
          refine ⟨3279015907597339064913451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4372021210129785419884601 3279015907597339064913451)
          ·
            refine ⟨4918523861396008597370177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3279015907597339064913451 4918523861396008597370177)
            ·
              refine ⟨3688892896047006448027633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4918523861396008597370177 3688892896047006448027633)
              ·
                refine ⟨2766669672035254836020725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3688892896047006448027633 2766669672035254836020725)
                ·
                  refine ⟨259375281753305140876943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2766669672035254836020725 259375281753305140876943)
                  ·
                    rfl

theorem cell23_4546184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 2, 2, 5].length) (baseStart_4546184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4546184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4546184 prefixEnd_4546184 := by exact prefixLift 4546184
  have htrace : WordTrace (prefixWord ++ tailWord_4546184) baseStart_4546184 baseEnd_4546184 := by
    simpa [prefixWord, tailWord_4546184, baseEnd_4546184] using wordTrace_append hprefix tailTrace_4546184
  have hstable : (prefixWord ++ tailWord_4546184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4546184).length < 2 ^ (prefixWord ++ tailWord_4546184).sum := by decide
  have hdescent : baseEnd_4546184 < baseStart_4546184 := by decide
  rcases family_descends (prefixWord ++ tailWord_4546184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4546249 : List Nat := [1, 2, 1, 1, 2, 1, 1, 1, 1, 12]
def baseStart_4546249 : Nat := 118140960795 + 4546249 * 2 ^ 59
def prefixEnd_4546249 : Nat := 4983230072969 + 3 ^ 40 * 4546249 * 2
def baseEnd_4546249 : Nat := 778136970674096171193229

theorem tailTrace_4546249 : CollatzResearch.WordTrace tailWord_4546249 prefixEnd_4546249 778136970674096171193229 := by
  unfold tailWord_4546249
  simp only [CollatzResearch.WordTrace]
  refine ⟨165815323306723785358961801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110543548871149190239307867 165815323306723785358961801)
  ·
    refine ⟨124361492480042839019221351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165815323306723785358961801 124361492480042839019221351)
    ·
      refine ⟨186542238720064258528832027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124361492480042839019221351 186542238720064258528832027)
      ·
        refine ⟨279813358080096387793248041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186542238720064258528832027 279813358080096387793248041)
        ·
          refine ⟨209860018560072290844936031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 279813358080096387793248041 209860018560072290844936031)
          ·
            refine ⟨314790027840108436267404047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 209860018560072290844936031 314790027840108436267404047)
            ·
              refine ⟨472185041760162654401106071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 314790027840108436267404047 472185041760162654401106071)
              ·
                refine ⟨708277562640243981601659107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 472185041760162654401106071 708277562640243981601659107)
                ·
                  refine ⟨1062416343960365972402488661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 708277562640243981601659107 1062416343960365972402488661)
                  ·
                    refine ⟨778136970674096171193229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 12 1062416343960365972402488661 778136970674096171193229)
                    ·
                      rfl

theorem cell23_4546249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 12].length) (baseStart_4546249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4546249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4546249 prefixEnd_4546249 := by exact prefixLift 4546249
  have htrace : WordTrace (prefixWord ++ tailWord_4546249) baseStart_4546249 baseEnd_4546249 := by
    simpa [prefixWord, tailWord_4546249, baseEnd_4546249] using wordTrace_append hprefix tailTrace_4546249
  have hstable : (prefixWord ++ tailWord_4546249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4546249).length < 2 ^ (prefixWord ++ tailWord_4546249).sum := by decide
  have hdescent : baseEnd_4546249 < baseStart_4546249 := by decide
  rcases family_descends (prefixWord ++ tailWord_4546249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4546256 : List Nat := [2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 4]
def baseStart_4546256 : Nat := 118140960795 + 4546256 * 2 ^ 59
def prefixEnd_4546256 : Nat := 4983230072969 + 3 ^ 40 * 4546256 * 2
def baseEnd_4546256 : Nat := 2334414506386869986192155

theorem tailTrace_4546256 : CollatzResearch.WordTrace tailWord_4546256 prefixEnd_4546256 2334414506386869986192155 := by
  unfold tailWord_4546256
  simp only [CollatzResearch.WordTrace]
  refine ⟨82907789308849212777233311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110543719078465617036311081 82907789308849212777233311)
  ·
    refine ⟨124361683963273819165849967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82907789308849212777233311 124361683963273819165849967)
    ·
      refine ⟨186542525944910728748774951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124361683963273819165849967 186542525944910728748774951)
      ·
        refine ⟨279813788917366093123162427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186542525944910728748774951 279813788917366093123162427)
        ·
          refine ⟨419720683376049139684743641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 279813788917366093123162427 419720683376049139684743641)
          ·
            refine ⟨314790512532036854763557731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 419720683376049139684743641 314790512532036854763557731)
            ·
              refine ⟨472185768798055282145336597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 314790512532036854763557731 472185768798055282145336597)
              ·
                refine ⟨22133707912408841350562653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 472185768798055282145336597 22133707912408841350562653)
                ·
                  refine ⟨8300140467153315506460995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22133707912408841350562653 8300140467153315506460995)
                  ·
                    refine ⟨12450210700729973259691493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8300140467153315506460995 12450210700729973259691493)
                    ·
                      refine ⟨2334414506386869986192155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12450210700729973259691493 2334414506386869986192155)
                      ·
                        rfl

theorem cell23_4546256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 4].length) (baseStart_4546256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4546256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4546256 prefixEnd_4546256 := by exact prefixLift 4546256
  have htrace : WordTrace (prefixWord ++ tailWord_4546256) baseStart_4546256 baseEnd_4546256 := by
    simpa [prefixWord, tailWord_4546256, baseEnd_4546256] using wordTrace_append hprefix tailTrace_4546256
  have hstable : (prefixWord ++ tailWord_4546256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4546256).length < 2 ^ (prefixWord ++ tailWord_4546256).sum := by decide
  have hdescent : baseEnd_4546256 < baseStart_4546256 := by decide
  rcases family_descends (prefixWord ++ tailWord_4546256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4546260 : List Nat := [2, 4, 1, 3, 1, 1, 1, 2, 1, 5, 2]
def baseStart_4546260 : Nat := 118140960795 + 4546260 * 2 ^ 59
def prefixEnd_4546260 : Nat := 4983230072969 + 3 ^ 40 * 4546260 * 2
def baseEnd_4546260 : Nat := 2334416560309487970542137

theorem tailTrace_4546260 : CollatzResearch.WordTrace tailWord_4546260 prefixEnd_4546260 2334416560309487970542137 := by
  unfold tailWord_4546260
  simp only [CollatzResearch.WordTrace]
  refine ⟨82907862254841967118806117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110543816339789289491741489 82907862254841967118806117)
  ·
    refine ⟨15545224172782868834776147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82907862254841967118806117 15545224172782868834776147)
    ·
      refine ⟨23317836259174303252164221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15545224172782868834776147 23317836259174303252164221)
      ·
        refine ⟨8744188597190363719561583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23317836259174303252164221 8744188597190363719561583)
        ·
          refine ⟨13116282895785545579342375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8744188597190363719561583 13116282895785545579342375)
          ·
            refine ⟨19674424343678318369013563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13116282895785545579342375 19674424343678318369013563)
            ·
              refine ⟨29511636515517477553520345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19674424343678318369013563 29511636515517477553520345)
              ·
                refine ⟨22133727386638108165140259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29511636515517477553520345 22133727386638108165140259)
                ·
                  refine ⟨33200591079957162247710389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22133727386638108165140259 33200591079957162247710389)
                  ·
                    refine ⟨3112555413745983960722849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33200591079957162247710389 3112555413745983960722849)
                    ·
                      refine ⟨2334416560309487970542137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3112555413745983960722849 2334416560309487970542137)
                      ·
                        rfl

theorem cell23_4546260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_4546260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4546260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4546260 prefixEnd_4546260 := by exact prefixLift 4546260
  have htrace : WordTrace (prefixWord ++ tailWord_4546260) baseStart_4546260 baseEnd_4546260 := by
    simpa [prefixWord, tailWord_4546260, baseEnd_4546260] using wordTrace_append hprefix tailTrace_4546260
  have hstable : (prefixWord ++ tailWord_4546260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4546260).length < 2 ^ (prefixWord ++ tailWord_4546260).sum := by decide
  have hdescent : baseEnd_4546260 < baseStart_4546260 := by decide
  rcases family_descends (prefixWord ++ tailWord_4546260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4546276 : List Nat := [2, 3, 1, 1, 1, 3, 1, 2, 3, 1, 5]
def baseStart_4546276 : Nat := 118140960795 + 4546276 * 2 ^ 59
def prefixEnd_4546276 : Nat := 4983230072969 + 3 ^ 40 * 4546276 * 2
def baseEnd_4546276 : Nat := 2334424775999959907942063

theorem tailTrace_4546276 : CollatzResearch.WordTrace tailWord_4546276 prefixEnd_4546276 2334424775999959907942063 := by
  unfold tailWord_4546276
  simp only [CollatzResearch.WordTrace]
  refine ⟨82908154038812984485097341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110544205385083979313463121 82908154038812984485097341)
  ·
    refine ⟨31090557764554869181911503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82908154038812984485097341 31090557764554869181911503)
    ·
      refine ⟨46635836646832303772867255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31090557764554869181911503 46635836646832303772867255)
      ·
        refine ⟨69953754970248455659300883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46635836646832303772867255 69953754970248455659300883)
        ·
          refine ⟨104930632455372683488951325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69953754970248455659300883 104930632455372683488951325)
          ·
            refine ⟨39348987170764756308356747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 104930632455372683488951325 39348987170764756308356747)
            ·
              refine ⟨59023480756147134462535121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39348987170764756308356747 59023480756147134462535121)
              ·
                refine ⟨44267610567110350846901341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59023480756147134462535121 44267610567110350846901341)
                ·
                  refine ⟨16600353962666381567588003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44267610567110350846901341 16600353962666381567588003)
                  ·
                    refine ⟨24900530943999572351382005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16600353962666381567588003 24900530943999572351382005)
                    ·
                      refine ⟨2334424775999959907942063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24900530943999572351382005 2334424775999959907942063)
                      ·
                        rfl

theorem cell23_4546276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 3, 1, 5].length) (baseStart_4546276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4546276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4546276 prefixEnd_4546276 := by exact prefixLift 4546276
  have htrace : WordTrace (prefixWord ++ tailWord_4546276) baseStart_4546276 baseEnd_4546276 := by
    simpa [prefixWord, tailWord_4546276, baseEnd_4546276] using wordTrace_append hprefix tailTrace_4546276
  have hstable : (prefixWord ++ tailWord_4546276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4546276).length < 2 ^ (prefixWord ++ tailWord_4546276).sum := by decide
  have hdescent : baseEnd_4546276 < baseStart_4546276 := by decide
  rcases family_descends (prefixWord ++ tailWord_4546276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4546307 : List Nat := [1, 1, 1, 3, 2, 2, 2, 6, 1, 2, 2]
def baseStart_4546307 : Nat := 118140960795 + 4546307 * 2 ^ 59
def prefixEnd_4546307 : Nat := 4983230072969 + 3 ^ 40 * 4546307 * 2
def baseEnd_4546307 : Nat := 2334440693900249286654421

theorem tailTrace_4546307 : CollatzResearch.WordTrace tailWord_4546307 prefixEnd_4546307 2334440693900249286654421 := by
  unfold tailWord_4546307
  simp only [CollatzResearch.WordTrace]
  refine ⟨165817438740513661264573175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110544959160342440843048783 165817438740513661264573175)
  ·
    refine ⟨248726158110770491896859763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165817438740513661264573175 248726158110770491896859763)
    ·
      refine ⟨373089237166155737845289645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248726158110770491896859763 373089237166155737845289645)
      ·
        refine ⟨139908463937308401691983617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 373089237166155737845289645 139908463937308401691983617)
        ·
          refine ⟨104931347952981301268987713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139908463937308401691983617 104931347952981301268987713)
          ·
            refine ⟨78698510964735975951740785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104931347952981301268987713 78698510964735975951740785)
            ·
              refine ⟨59023883223551981963805589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78698510964735975951740785 59023883223551981963805589)
              ·
                refine ⟨2766744526103999154553387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 59023883223551981963805589 2766744526103999154553387)
                ·
                  refine ⟨4150116789155998731830081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2766744526103999154553387 4150116789155998731830081)
                  ·
                    refine ⟨3112587591866999048872561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4150116789155998731830081 3112587591866999048872561)
                    ·
                      refine ⟨2334440693900249286654421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3112587591866999048872561 2334440693900249286654421)
                      ·
                        rfl

theorem cell23_4546307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 6, 1, 2, 2].length) (baseStart_4546307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4546307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4546307 prefixEnd_4546307 := by exact prefixLift 4546307
  have htrace : WordTrace (prefixWord ++ tailWord_4546307) baseStart_4546307 baseEnd_4546307 := by
    simpa [prefixWord, tailWord_4546307, baseEnd_4546307] using wordTrace_append hprefix tailTrace_4546307
  have hstable : (prefixWord ++ tailWord_4546307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4546307).length < 2 ^ (prefixWord ++ tailWord_4546307).sum := by decide
  have hdescent : baseEnd_4546307 < baseStart_4546307 := by decide
  rcases family_descends (prefixWord ++ tailWord_4546307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4546323 : List Nat := [1, 1, 1, 2, 1, 3, 2, 2, 6, 1, 3]
def baseStart_4546323 : Nat := 118140960795 + 4546323 * 2 ^ 59
def prefixEnd_4546323 : Nat := 4983230072969 + 3 ^ 40 * 4546323 * 2
def baseEnd_4546323 : Nat := 2334448909590721224054347

theorem tailTrace_4546323 : CollatzResearch.WordTrace tailWord_4546323 prefixEnd_4546323 2334448909590721224054347 := by
  unfold tailWord_4546323
  simp only [CollatzResearch.WordTrace]
  refine ⟨165818022308455695997155623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110545348205637130664770415 165818022308455695997155623)
  ·
    refine ⟨248727033462683543995733435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165818022308455695997155623 248727033462683543995733435)
    ·
      refine ⟨373090550194025315993600153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248727033462683543995733435 373090550194025315993600153)
      ·
        refine ⟨279817912645518986995200115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 373090550194025315993600153 279817912645518986995200115)
        ·
          refine ⟨419726868968278480492800173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 279817912645518986995200115 419726868968278480492800173)
          ·
            refine ⟨157397575863104430184800065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 419726868968278480492800173 157397575863104430184800065)
            ·
              refine ⟨118048181897328322638600049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 157397575863104430184800065 118048181897328322638600049)
              ·
                refine ⟨88536136422996241978950037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 118048181897328322638600049 88536136422996241978950037)
                ·
                  refine ⟨4150131394827948842763283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 88536136422996241978950037 4150131394827948842763283)
                  ·
                    refine ⟨6225197092241923264144925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4150131394827948842763283 6225197092241923264144925)
                    ·
                      refine ⟨2334448909590721224054347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6225197092241923264144925 2334448909590721224054347)
                      ·
                        rfl

theorem cell23_4546323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 6, 1, 3].length) (baseStart_4546323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4546323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4546323 prefixEnd_4546323 := by exact prefixLift 4546323
  have htrace : WordTrace (prefixWord ++ tailWord_4546323) baseStart_4546323 baseEnd_4546323 := by
    simpa [prefixWord, tailWord_4546323, baseEnd_4546323] using wordTrace_append hprefix tailTrace_4546323
  have hstable : (prefixWord ++ tailWord_4546323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4546323).length < 2 ^ (prefixWord ++ tailWord_4546323).sum := by decide
  have hdescent : baseEnd_4546323 < baseStart_4546323 := by decide
  rcases family_descends (prefixWord ++ tailWord_4546323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4546324 : List Nat := [2, 4, 4, 1, 1, 1, 1, 1, 3, 1, 4]
def baseStart_4546324 : Nat := 118140960795 + 4546324 * 2 ^ 59
def prefixEnd_4546324 : Nat := 4983230072969 + 3 ^ 40 * 4546324 * 2
def baseEnd_4546324 : Nat := 2334449423071375720141843

theorem tailTrace_4546324 : CollatzResearch.WordTrace tailWord_4546324 prefixEnd_4546324 2334449423071375720141843 := by
  unfold tailWord_4546324
  simp only [CollatzResearch.WordTrace]
  refine ⟨82909029390726036583971013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110545372520968048778628017 82909029390726036583971013)
  ·
    refine ⟨15545443010761131859494565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82909029390726036583971013 15545443010761131859494565)
    ·
      refine ⟨2914770564517712223655231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15545443010761131859494565 2914770564517712223655231)
      ·
        refine ⟨4372155846776568335482847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2914770564517712223655231 4372155846776568335482847)
        ·
          refine ⟨6558233770164852503224271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4372155846776568335482847 6558233770164852503224271)
          ·
            refine ⟨9837350655247278754836407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6558233770164852503224271 9837350655247278754836407)
            ·
              refine ⟨14756025982870918132254611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9837350655247278754836407 14756025982870918132254611)
              ·
                refine ⟨22134038974306377198381917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14756025982870918132254611 22134038974306377198381917)
                ·
                  refine ⟨8300264615364891449393219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22134038974306377198381917 8300264615364891449393219)
                  ·
                    refine ⟨12450396923047337174089829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8300264615364891449393219 12450396923047337174089829)
                    ·
                      refine ⟨2334449423071375720141843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12450396923047337174089829 2334449423071375720141843)
                      ·
                        rfl

theorem cell23_4546324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_4546324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4546324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4546324 prefixEnd_4546324 := by exact prefixLift 4546324
  have htrace : WordTrace (prefixWord ++ tailWord_4546324) baseStart_4546324 baseEnd_4546324 := by
    simpa [prefixWord, tailWord_4546324, baseEnd_4546324] using wordTrace_append hprefix tailTrace_4546324
  have hstable : (prefixWord ++ tailWord_4546324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4546324).length < 2 ^ (prefixWord ++ tailWord_4546324).sum := by decide
  have hdescent : baseEnd_4546324 < baseStart_4546324 := by decide
  rcases family_descends (prefixWord ++ tailWord_4546324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4546327 : List Nat := [1, 1, 3, 4, 2, 3, 1, 2, 1, 2, 3]
def baseStart_4546327 : Nat := 118140960795 + 4546327 * 2 ^ 59
def prefixEnd_4546327 : Nat := 4983230072969 + 3 ^ 40 * 4546327 * 2
def baseEnd_4546327 : Nat := 2334450963513339208404329

theorem tailTrace_4546327 : CollatzResearch.WordTrace tailWord_4546327 prefixEnd_4546327 2334450963513339208404329 := by
  unfold tailWord_4546327
  simp only [CollatzResearch.WordTrace]
  refine ⟨165818168200441204680301235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110545445466960803120200823 165818168200441204680301235)
  ·
    refine ⟨248727252300661807020451853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165818168200441204680301235 248727252300661807020451853)
    ·
      refine ⟨93272719612748177632669445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 248727252300661807020451853 93272719612748177632669445)
      ·
        refine ⟨17488634927390283306125521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 93272719612748177632669445 17488634927390283306125521)
        ·
          refine ⟨13116476195542712479594141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17488634927390283306125521 13116476195542712479594141)
          ·
            refine ⟨4918678573328517179847803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13116476195542712479594141 4918678573328517179847803)
            ·
              refine ⟨7378017859992775769771705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4918678573328517179847803 7378017859992775769771705)
              ·
                refine ⟨5533513394994581827328779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7378017859992775769771705 5533513394994581827328779)
                ·
                  refine ⟨8300270092491872740993169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5533513394994581827328779 8300270092491872740993169)
                  ·
                    refine ⟨6225202569368904555744877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8300270092491872740993169 6225202569368904555744877)
                    ·
                      refine ⟨2334450963513339208404329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6225202569368904555744877 2334450963513339208404329)
                      ·
                        rfl

theorem cell23_4546327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_4546327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4546327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4546327 prefixEnd_4546327 := by exact prefixLift 4546327
  have htrace : WordTrace (prefixWord ++ tailWord_4546327) baseStart_4546327 baseEnd_4546327 := by
    simpa [prefixWord, tailWord_4546327, baseEnd_4546327] using wordTrace_append hprefix tailTrace_4546327
  have hstable : (prefixWord ++ tailWord_4546327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4546327).length < 2 ^ (prefixWord ++ tailWord_4546327).sum := by decide
  have hdescent : baseEnd_4546327 < baseStart_4546327 := by decide
  rcases family_descends (prefixWord ++ tailWord_4546327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4546340 : List Nat := [2, 3, 1, 3, 2, 2, 1, 2, 1, 3, 3]
def baseStart_4546340 : Nat := 118140960795 + 4546340 * 2 ^ 59
def prefixEnd_4546340 : Nat := 4983230072969 + 3 ^ 40 * 4546340 * 2
def baseEnd_4546340 : Nat := 2334457638761847657541769

theorem tailTrace_4546340 : CollatzResearch.WordTrace tailWord_4546340 prefixEnd_4546340 2334457638761847657541769 := by
  unfold tailWord_4546340
  simp only [CollatzResearch.WordTrace]
  refine ⟨82909321174697053950262237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110545761566262738600349649 82909321174697053950262237)
  ·
    refine ⟨31090995440511395231348339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82909321174697053950262237 31090995440511395231348339)
    ·
      refine ⟨46636493160767092847022509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31090995440511395231348339 46636493160767092847022509)
      ·
        refine ⟨17488684935287659817633441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46636493160767092847022509 17488684935287659817633441)
        ·
          refine ⟨13116513701465744863225081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17488684935287659817633441 13116513701465744863225081)
          ·
            refine ⟨9837385276099308647418811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13116513701465744863225081 9837385276099308647418811)
            ·
              refine ⟨14756077914148962971128217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9837385276099308647418811 14756077914148962971128217)
              ·
                refine ⟨11067058435611722228346163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14756077914148962971128217 11067058435611722228346163)
                ·
                  refine ⟨16600587653417583342519245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11067058435611722228346163 16600587653417583342519245)
                  ·
                    refine ⟨6225220370031593753444717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16600587653417583342519245 6225220370031593753444717)
                    ·
                      refine ⟨2334457638761847657541769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6225220370031593753444717 2334457638761847657541769)
                      ·
                        rfl

theorem cell23_4546340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_4546340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4546340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4546340 prefixEnd_4546340 := by exact prefixLift 4546340
  have htrace : WordTrace (prefixWord ++ tailWord_4546340) baseStart_4546340 baseEnd_4546340 := by
    simpa [prefixWord, tailWord_4546340, baseEnd_4546340] using wordTrace_append hprefix tailTrace_4546340
  have hstable : (prefixWord ++ tailWord_4546340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4546340).length < 2 ^ (prefixWord ++ tailWord_4546340).sum := by decide
  have hdescent : baseEnd_4546340 < baseStart_4546340 := by decide
  rcases family_descends (prefixWord ++ tailWord_4546340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4546358 : List Nat := [5, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2]
def baseStart_4546358 : Nat := 118140960795 + 4546358 * 2 ^ 59
def prefixEnd_4546358 : Nat := 4983230072969 + 3 ^ 40 * 4546358 * 2
def baseEnd_4546358 : Nat := 2334466881413628587116687

theorem tailTrace_4546358 : CollatzResearch.WordTrace tailWord_4546358 prefixEnd_4546358 2334466881413628587116687 := by
  unfold tailWord_4546358
  simp only [CollatzResearch.WordTrace]
  refine ⟨10363706178958056060917483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 110546199242219264649786485 10363706178958056060917483)
  ·
    refine ⟨15545559268437084091376225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10363706178958056060917483 15545559268437084091376225)
    ·
      refine ⟨11659169451327813068532169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15545559268437084091376225 11659169451327813068532169)
      ·
        refine ⟨8744377088495859801399127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11659169451327813068532169 8744377088495859801399127)
        ·
          refine ⟨13116565632743789702098691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8744377088495859801399127 13116565632743789702098691)
          ·
            refine ⟨19674848449115684553148037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13116565632743789702098691 19674848449115684553148037)
            ·
              refine ⟨3689034084209190853715257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19674848449115684553148037 3689034084209190853715257)
              ·
                refine ⟨2766775563156893140286443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3689034084209190853715257 2766775563156893140286443)
                ·
                  refine ⟨4150163344735339710429665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2766775563156893140286443 4150163344735339710429665)
                  ·
                    refine ⟨3112622508551504782822249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4150163344735339710429665 3112622508551504782822249)
                    ·
                      refine ⟨2334466881413628587116687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3112622508551504782822249 2334466881413628587116687)
                      ·
                        rfl

theorem cell23_4546358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_4546358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4546358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4546358 prefixEnd_4546358 := by exact prefixLift 4546358
  have htrace : WordTrace (prefixWord ++ tailWord_4546358) baseStart_4546358 baseEnd_4546358 := by
    simpa [prefixWord, tailWord_4546358, baseEnd_4546358] using wordTrace_append hprefix tailTrace_4546358
  have hstable : (prefixWord ++ tailWord_4546358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4546358).length < 2 ^ (prefixWord ++ tailWord_4546358).sum := by decide
  have hdescent : baseEnd_4546358 < baseStart_4546358 := by decide
  rcases family_descends (prefixWord ++ tailWord_4546358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4546374 : List Nat := [6, 1, 1, 2, 1, 2, 2, 1, 1, 3, 3]
def baseStart_4546374 : Nat := 118140960795 + 4546374 * 2 ^ 59
def prefixEnd_4546374 : Nat := 4983230072969 + 3 ^ 40 * 4546374 * 2
def baseEnd_4546374 : Nat := 2334475097104100524516613

theorem tailTrace_4546374 : CollatzResearch.WordTrace tailWord_4546374 prefixEnd_4546374 2334475097104100524516613 := by
  unfold tailWord_4546374
  simp only [CollatzResearch.WordTrace]
  refine ⟨5181871325977216615851943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 110546588287513954471508117 5181871325977216615851943)
  ·
    refine ⟨7772806988965824923777915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5181871325977216615851943 7772806988965824923777915)
    ·
      refine ⟨11659210483448737385666873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7772806988965824923777915 11659210483448737385666873)
      ·
        refine ⟨8744407862586553039250155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11659210483448737385666873 8744407862586553039250155)
        ·
          refine ⟨13116611793879829558875233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8744407862586553039250155 13116611793879829558875233)
          ·
            refine ⟨9837458845409872169156425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13116611793879829558875233 9837458845409872169156425)
            ·
              refine ⟨7378094134057404126867319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9837458845409872169156425 7378094134057404126867319)
              ·
                refine ⟨11067141201086106190300979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7378094134057404126867319 11067141201086106190300979)
                ·
                  refine ⟨16600711801629159285451469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11067141201086106190300979 16600711801629159285451469)
                  ·
                    refine ⟨6225266925610934732044301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16600711801629159285451469 6225266925610934732044301)
                    ·
                      refine ⟨2334475097104100524516613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6225266925610934732044301 2334475097104100524516613)
                      ·
                        rfl

theorem cell23_4546374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_4546374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4546374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4546374 prefixEnd_4546374 := by exact prefixLift 4546374
  have htrace : WordTrace (prefixWord ++ tailWord_4546374) baseStart_4546374 baseEnd_4546374 := by
    simpa [prefixWord, tailWord_4546374, baseEnd_4546374] using wordTrace_append hprefix tailTrace_4546374
  have hstable : (prefixWord ++ tailWord_4546374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4546374).length < 2 ^ (prefixWord ++ tailWord_4546374).sum := by decide
  have hdescent : baseEnd_4546374 < baseStart_4546374 := by decide
  rcases family_descends (prefixWord ++ tailWord_4546374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4546414 : List Nat := [4, 1, 2, 3, 1, 2, 1, 1, 4, 2, 2]
def baseStart_4546414 : Nat := 118140960795 + 4546414 * 2 ^ 59
def prefixEnd_4546414 : Nat := 4983230072969 + 3 ^ 40 * 4546414 * 2
def baseEnd_4546414 : Nat := 2334495636330280368016429

theorem tailTrace_4546414 : CollatzResearch.WordTrace tailWord_4546414 prefixEnd_4546414 2334495636330280368016429 := by
  unfold tailWord_4546414
  simp only [CollatzResearch.WordTrace]
  refine ⟨20727667668890752317339787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110547560900750679025812197 20727667668890752317339787)
  ·
    refine ⟨31091501503336128476009681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20727667668890752317339787 31091501503336128476009681)
    ·
      refine ⟨23318626127502096357007261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31091501503336128476009681 23318626127502096357007261)
      ·
        refine ⟨8744484797813286133877723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23318626127502096357007261 8744484797813286133877723)
        ·
          refine ⟨13116727196719929200816585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8744484797813286133877723 13116727196719929200816585)
          ·
            refine ⟨9837545397539946900612439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13116727196719929200816585 9837545397539946900612439)
            ·
              refine ⟨14756318096309920350918659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9837545397539946900612439 14756318096309920350918659)
              ·
                refine ⟨22134477144464880526377989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14756318096309920350918659 22134477144464880526377989)
                ·
                  refine ⟨4150214464587165098695873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22134477144464880526377989 4150214464587165098695873)
                  ·
                    refine ⟨3112660848440373824021905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4150214464587165098695873 3112660848440373824021905)
                    ·
                      refine ⟨2334495636330280368016429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3112660848440373824021905 2334495636330280368016429)
                      ·
                        rfl

theorem cell23_4546414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_4546414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4546414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4546414 prefixEnd_4546414 := by exact prefixLift 4546414
  have htrace : WordTrace (prefixWord ++ tailWord_4546414) baseStart_4546414 baseEnd_4546414 := by
    simpa [prefixWord, tailWord_4546414, baseEnd_4546414] using wordTrace_append hprefix tailTrace_4546414
  have hstable : (prefixWord ++ tailWord_4546414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4546414).length < 2 ^ (prefixWord ++ tailWord_4546414).sum := by decide
  have hdescent : baseEnd_4546414 < baseStart_4546414 := by decide
  rcases family_descends (prefixWord ++ tailWord_4546414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4546450 : List Nat := [3, 2, 3, 2, 1, 1, 2, 1, 1, 7]
def baseStart_4546450 : Nat := 118140960795 + 4546450 * 2 ^ 59
def prefixEnd_4546450 : Nat := 4983230072969 + 3 ^ 40 * 4546450 * 2
def baseEnd_4546450 : Nat := 778171373877947409055421

theorem tailTrace_4546450 : CollatzResearch.WordTrace tailWord_4546450 prefixEnd_4546450 778171373877947409055421 := by
  unfold tailWord_4546450
  simp only [CollatzResearch.WordTrace]
  refine ⟨41455663594748899171757201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110548436252663731124685869 41455663594748899171757201)
  ·
    refine ⟨31091747696061674378817901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41455663594748899171757201 31091747696061674378817901)
    ·
      refine ⟨11659405386023127892056713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31091747696061674378817901 11659405386023127892056713)
      ·
        refine ⟨8744554039517345919042535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11659405386023127892056713 8744554039517345919042535)
        ·
          refine ⟨13116831059276018878563803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8744554039517345919042535 13116831059276018878563803)
          ·
            refine ⟨19675246588914028317845705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13116831059276018878563803 19675246588914028317845705)
            ·
              refine ⟨14756434941685521238384279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19675246588914028317845705 14756434941685521238384279)
              ·
                refine ⟨22134652412528281857576419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14756434941685521238384279 22134652412528281857576419)
                ·
                  refine ⟨33201978618792422786364629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22134652412528281857576419 33201978618792422786364629)
                  ·
                    refine ⟨778171373877947409055421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33201978618792422786364629 778171373877947409055421)
                    ·
                      rfl

theorem cell23_4546450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_4546450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4546450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4546450 prefixEnd_4546450 := by exact prefixLift 4546450
  have htrace : WordTrace (prefixWord ++ tailWord_4546450) baseStart_4546450 baseEnd_4546450 := by
    simpa [prefixWord, tailWord_4546450, baseEnd_4546450] using wordTrace_append hprefix tailTrace_4546450
  have hstable : (prefixWord ++ tailWord_4546450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4546450).length < 2 ^ (prefixWord ++ tailWord_4546450).sum := by decide
  have hdescent : baseEnd_4546450 < baseStart_4546450 := by decide
  rcases family_descends (prefixWord ++ tailWord_4546450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4546453 : List Nat := [1, 3, 2, 1, 1, 3, 1, 3, 1, 3, 4]
def baseStart_4546453 : Nat := 118140960795 + 4546453 * 2 ^ 59
def prefixEnd_4546453 : Nat := 4983230072969 + 3 ^ 40 * 4546453 * 2
def baseEnd_4546453 : Nat := 2334515662075805715428749

theorem tailTrace_4546453 : CollatzResearch.WordTrace tailWord_4546453 prefixEnd_4546453 2334515662075805715428749 := by
  unfold tailWord_4546453
  simp only [CollatzResearch.WordTrace]
  refine ⟨165822763797984728199388013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110548509198656485466258675 165822763797984728199388013)
  ·
    refine ⟨62183536424244273074770505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165822763797984728199388013 62183536424244273074770505)
    ·
      refine ⟨46637652318183204806077879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62183536424244273074770505 46637652318183204806077879)
      ·
        refine ⟨69956478477274807209116819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46637652318183204806077879 69956478477274807209116819)
        ·
          refine ⟨104934717715912210813675229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69956478477274807209116819 104934717715912210813675229)
          ·
            refine ⟨39350519143467079055128211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 104934717715912210813675229 39350519143467079055128211)
            ·
              refine ⟨59025778715200618582692317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39350519143467079055128211 59025778715200618582692317)
              ·
                refine ⟨22134667018200231968509619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59025778715200618582692317 22134667018200231968509619)
                ·
                  refine ⟨33202000527300347952764429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22134667018200231968509619 33202000527300347952764429)
                  ·
                    refine ⟨12450750197737630482286661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33202000527300347952764429 12450750197737630482286661)
                    ·
                      refine ⟨2334515662075805715428749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12450750197737630482286661 2334515662075805715428749)
                      ·
                        rfl

theorem cell23_4546453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 3, 1, 3, 4].length) (baseStart_4546453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4546453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4546453 prefixEnd_4546453 := by exact prefixLift 4546453
  have htrace : WordTrace (prefixWord ++ tailWord_4546453) baseStart_4546453 baseEnd_4546453 := by
    simpa [prefixWord, tailWord_4546453, baseEnd_4546453] using wordTrace_append hprefix tailTrace_4546453
  have hstable : (prefixWord ++ tailWord_4546453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4546453).length < 2 ^ (prefixWord ++ tailWord_4546453).sum := by decide
  have hdescent : baseEnd_4546453 < baseStart_4546453 := by decide
  rcases family_descends (prefixWord ++ tailWord_4546453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4546473 : List Nat := [1, 2, 1, 1, 1, 1, 4, 2, 3, 4, 3]
def baseStart_4546473 : Nat := 118140960795 + 4546473 * 2 ^ 59
def prefixEnd_4546473 : Nat := 4983230072969 + 3 ^ 40 * 4546473 * 2
def baseEnd_4546473 : Nat := 2334525931688895637178657

theorem tailTrace_4546473 : CollatzResearch.WordTrace tailWord_4546473 prefixEnd_4546473 2334525931688895637178657 := by
  unfold tailWord_4546473
  simp only [CollatzResearch.WordTrace]
  refine ⟨165823493257912271615116073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110548995505274847743410715 165823493257912271615116073)
  ·
    refine ⟨124367619943434203711337055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165823493257912271615116073 124367619943434203711337055)
    ·
      refine ⟨186551429915151305567005583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124367619943434203711337055 186551429915151305567005583)
      ·
        refine ⟨279827144872726958350508375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186551429915151305567005583 279827144872726958350508375)
        ·
          refine ⟨419740717309090437525762563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 279827144872726958350508375 419740717309090437525762563)
          ·
            refine ⟨629611075963635656288643845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 419740717309090437525762563 629611075963635656288643845)
            ·
              refine ⟨118052076743181685554120721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 629611075963635656288643845 118052076743181685554120721)
              ·
                refine ⟨88539057557386264165590541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 118052076743181685554120721 88539057557386264165590541)
                ·
                  refine ⟨33202146584019849062096453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 88539057557386264165590541 33202146584019849062096453)
                  ·
                    refine ⟨6225402484503721699143085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33202146584019849062096453 6225402484503721699143085)
                    ·
                      refine ⟨2334525931688895637178657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6225402484503721699143085 2334525931688895637178657)
                      ·
                        rfl

theorem cell23_4546473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 3, 4, 3].length) (baseStart_4546473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4546473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4546473 prefixEnd_4546473 := by exact prefixLift 4546473
  have htrace : WordTrace (prefixWord ++ tailWord_4546473) baseStart_4546473 baseEnd_4546473 := by
    simpa [prefixWord, tailWord_4546473, baseEnd_4546473] using wordTrace_append hprefix tailTrace_4546473
  have hstable : (prefixWord ++ tailWord_4546473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4546473).length < 2 ^ (prefixWord ++ tailWord_4546473).sum := by decide
  have hdescent : baseEnd_4546473 < baseStart_4546473 := by decide
  rcases family_descends (prefixWord ++ tailWord_4546473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4546531 : List Nat := [1, 1, 1, 6, 1, 4, 2, 2, 1, 4]
def baseStart_4546531 : Nat := 118140960795 + 4546531 * 2 ^ 59
def prefixEnd_4546531 : Nat := 4983230072969 + 3 ^ 40 * 4546531 * 2
def baseEnd_4546531 : Nat := 778185237855618803417797

theorem tailTrace_4546531 : CollatzResearch.WordTrace tailWord_4546531 prefixEnd_4546531 778185237855618803417797 := by
  unfold tailWord_4546531
  simp only [CollatzResearch.WordTrace]
  refine ⟨165825608691702147520727447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110550405794468098347151631 165825608691702147520727447)
  ·
    refine ⟨248738413037553221281091171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165825608691702147520727447 248738413037553221281091171)
    ·
      refine ⟨373107619556329831921636757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248738413037553221281091171 373107619556329831921636757)
      ·
        refine ⟨17489419666702960871326723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 373107619556329831921636757 17489419666702960871326723)
        ·
          refine ⟨26234129500054441306990085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17489419666702960871326723 26234129500054441306990085)
          ·
            refine ⟨4918899281260207745060641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26234129500054441306990085 4918899281260207745060641)
            ·
              refine ⟨3689174460945155808795481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4918899281260207745060641 3689174460945155808795481)
              ·
                refine ⟨2766880845708866856596611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3689174460945155808795481 2766880845708866856596611)
                ·
                  refine ⟨4150321268563300284894917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2766880845708866856596611 4150321268563300284894917)
                  ·
                    refine ⟨778185237855618803417797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4150321268563300284894917 778185237855618803417797)
                    ·
                      rfl

theorem cell23_4546531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 2, 2, 1, 4].length) (baseStart_4546531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4546531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4546531 prefixEnd_4546531 := by exact prefixLift 4546531
  have htrace : WordTrace (prefixWord ++ tailWord_4546531) baseStart_4546531 baseEnd_4546531 := by
    simpa [prefixWord, tailWord_4546531, baseEnd_4546531] using wordTrace_append hprefix tailTrace_4546531
  have hstable : (prefixWord ++ tailWord_4546531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4546531).length < 2 ^ (prefixWord ++ tailWord_4546531).sum := by decide
  have hdescent : baseEnd_4546531 < baseStart_4546531 := by decide
  rcases family_descends (prefixWord ++ tailWord_4546531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4546560 : List Nat := [2, 1, 1, 2, 1, 1, 1, 3, 1, 8, 2]
def baseStart_4546560 : Nat := 118140960795 + 4546560 * 2 ^ 59
def prefixEnd_4546560 : Nat := 4983230072969 + 3 ^ 40 * 4546560 * 2
def baseEnd_4546560 : Nat := 2334570604505836796790757

theorem tailTrace_4546560 : CollatzResearch.WordTrace tailWord_4546560 prefixEnd_4546560 2334570604505836796790757 := by
  unfold tailWord_4546560
  simp only [CollatzResearch.WordTrace]
  refine ⟨82913333204298542736766567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110551110939064723649022089 82913333204298542736766567)
  ·
    refine ⟨124369999806447814105149851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82913333204298542736766567 124369999806447814105149851)
    ·
      refine ⟨186554999709671721157724777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124369999806447814105149851 186554999709671721157724777)
      ·
        refine ⟨139916249782253790868293583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186554999709671721157724777 139916249782253790868293583)
        ·
          refine ⟨209874374673380686302440375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139916249782253790868293583 209874374673380686302440375)
          ·
            refine ⟨314811562010071029453660563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 209874374673380686302440375 314811562010071029453660563)
            ·
              refine ⟨472217343015106544180490845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 314811562010071029453660563 472217343015106544180490845)
              ·
                refine ⟨177081503630664954067684067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 472217343015106544180490845 177081503630664954067684067)
                ·
                  refine ⟨265622255445997431101526101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 177081503630664954067684067 265622255445997431101526101)
                  ·
                    refine ⟨3112760806007782395721009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 265622255445997431101526101 3112760806007782395721009)
                    ·
                      refine ⟨2334570604505836796790757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3112760806007782395721009 2334570604505836796790757)
                      ·
                        rfl

theorem cell23_4546560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 1, 8, 2].length) (baseStart_4546560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4546560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4546560 prefixEnd_4546560 := by exact prefixLift 4546560
  have htrace : WordTrace (prefixWord ++ tailWord_4546560) baseStart_4546560 baseEnd_4546560 := by
    simpa [prefixWord, tailWord_4546560, baseEnd_4546560] using wordTrace_append hprefix tailTrace_4546560
  have hstable : (prefixWord ++ tailWord_4546560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4546560).length < 2 ^ (prefixWord ++ tailWord_4546560).sum := by decide
  have hdescent : baseEnd_4546560 < baseStart_4546560 := by decide
  rcases family_descends (prefixWord ++ tailWord_4546560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4546603 : List Nat := [1, 1, 1, 1, 2, 1, 4, 1, 1, 4, 6]
def baseStart_4546603 : Nat := 118140960795 + 4546603 * 2 ^ 59
def prefixEnd_4546603 : Nat := 4983230072969 + 3 ^ 40 * 4546603 * 2
def baseEnd_4546603 : Nat := 2334592684173980128553059

theorem tailTrace_4546603 : CollatzResearch.WordTrace tailWord_4546603 prefixEnd_4546603 2334592684173980128553059 := by
  unfold tailWord_4546603
  simp only [CollatzResearch.WordTrace]
  refine ⟨165828234747441303817348463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110552156498294202544898975 165828234747441303817348463)
  ·
    refine ⟨248742352121161955726022695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165828234747441303817348463 248742352121161955726022695)
    ·
      refine ⟨373113528181742933589034043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248742352121161955726022695 373113528181742933589034043)
      ·
        refine ⟨559670292272614400383551065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 373113528181742933589034043 559670292272614400383551065)
        ·
          refine ⟨419752719204460800287663299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 559670292272614400383551065 419752719204460800287663299)
          ·
            refine ⟨629629078806691200431494949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 419752719204460800287663299 629629078806691200431494949)
            ·
              refine ⟨118055452276254600080905303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 629629078806691200431494949 118055452276254600080905303)
              ·
                refine ⟨177083178414381900121357955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118055452276254600080905303 177083178414381900121357955)
                ·
                  refine ⟨265624767621572850182036933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 177083178414381900121357955 265624767621572850182036933)
                  ·
                    refine ⟨49804643929044909409131925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 265624767621572850182036933 49804643929044909409131925)
                    ·
                      refine ⟨2334592684173980128553059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49804643929044909409131925 2334592684173980128553059)
                      ·
                        rfl

theorem cell23_4546603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 4, 6].length) (baseStart_4546603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4546603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4546603 prefixEnd_4546603 := by exact prefixLift 4546603
  have htrace : WordTrace (prefixWord ++ tailWord_4546603) baseStart_4546603 baseEnd_4546603 := by
    simpa [prefixWord, tailWord_4546603, baseEnd_4546603] using wordTrace_append hprefix tailTrace_4546603
  have hstable : (prefixWord ++ tailWord_4546603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4546603).length < 2 ^ (prefixWord ++ tailWord_4546603).sum := by decide
  have hdescent : baseEnd_4546603 < baseStart_4546603 := by decide
  rcases family_descends (prefixWord ++ tailWord_4546603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4546644 : List Nat := [2, 4, 1, 1, 1, 1, 1, 6, 2, 1, 3]
def baseStart_4546644 : Nat := 118140960795 + 4546644 * 2 ^ 59
def prefixEnd_4546644 : Nat := 4983230072969 + 3 ^ 40 * 4546644 * 2
def baseEnd_4546644 : Nat := 2334613736880814468140371

theorem tailTrace_4546644 : CollatzResearch.WordTrace tailWord_4546644 prefixEnd_4546644 2334613736880814468140371 := by
  unfold tailWord_4546644
  simp only [CollatzResearch.WordTrace]
  refine ⟨82914865070146383909795493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110553153426861845213060657 82914865070146383909795493)
  ·
    refine ⟨15546537200652446983086655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82914865070146383909795493 15546537200652446983086655)
    ·
      refine ⟨23319805800978670474629983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15546537200652446983086655 23319805800978670474629983)
      ·
        refine ⟨34979708701468005711944975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23319805800978670474629983 34979708701468005711944975)
        ·
          refine ⟨52469563052202008567917463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34979708701468005711944975 52469563052202008567917463)
          ·
            refine ⟨78704344578303012851876195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52469563052202008567917463 78704344578303012851876195)
            ·
              refine ⟨118056516867454519277814293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78704344578303012851876195 118056516867454519277814293)
              ·
                refine ⟨5533899228161930591147545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 118056516867454519277814293 5533899228161930591147545)
                ·
                  refine ⟨4150424421121447943360659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5533899228161930591147545 4150424421121447943360659)
                  ·
                    refine ⟨6225636631682171915040989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4150424421121447943360659 6225636631682171915040989)
                    ·
                      refine ⟨2334613736880814468140371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6225636631682171915040989 2334613736880814468140371)
                      ·
                        rfl

theorem cell23_4546644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 6, 2, 1, 3].length) (baseStart_4546644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4546644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4546644 prefixEnd_4546644 := by exact prefixLift 4546644
  have htrace : WordTrace (prefixWord ++ tailWord_4546644) baseStart_4546644 baseEnd_4546644 := by
    simpa [prefixWord, tailWord_4546644, baseEnd_4546644] using wordTrace_append hprefix tailTrace_4546644
  have hstable : (prefixWord ++ tailWord_4546644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4546644).length < 2 ^ (prefixWord ++ tailWord_4546644).sum := by decide
  have hdescent : baseEnd_4546644 < baseStart_4546644 := by decide
  rcases family_descends (prefixWord ++ tailWord_4546644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4546650 : List Nat := [3, 1, 1, 2, 1, 1, 4, 1, 2, 3, 4]
def baseStart_4546650 : Nat := 118140960795 + 4546650 * 2 ^ 59
def prefixEnd_4546650 : Nat := 4983230072969 + 3 ^ 40 * 4546650 * 2
def baseEnd_4546650 : Nat := 2334616817764741444665343

theorem tailTrace_4546650 : CollatzResearch.WordTrace tailWord_4546650 prefixEnd_4546650 2334616817764741444665343 := by
  unfold tailWord_4546650
  simp only [CollatzResearch.WordTrace]
  refine ⟨41457487244567757711077351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110553299318847353896206269 41457487244567757711077351)
  ·
    refine ⟨62186230866851636566616027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41457487244567757711077351 62186230866851636566616027)
    ·
      refine ⟨93279346300277454849924041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62186230866851636566616027 93279346300277454849924041)
      ·
        refine ⟨69959509725208091137443031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93279346300277454849924041 69959509725208091137443031)
        ·
          refine ⟨104939264587812136706164547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69959509725208091137443031 104939264587812136706164547)
          ·
            refine ⟨157408896881718205059246821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104939264587812136706164547 157408896881718205059246821)
            ·
              refine ⟨29514168165322163448608779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 157408896881718205059246821 29514168165322163448608779)
              ·
                refine ⟨44271252247983245172913169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29514168165322163448608779 44271252247983245172913169)
                ·
                  refine ⟨33203439185987433879684877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44271252247983245172913169 33203439185987433879684877)
                  ·
                    refine ⟨12451289694745287704881829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33203439185987433879684877 12451289694745287704881829)
                    ·
                      refine ⟨2334616817764741444665343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12451289694745287704881829 2334616817764741444665343)
                      ·
                        rfl

theorem cell23_4546650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 2, 3, 4].length) (baseStart_4546650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4546650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4546650 prefixEnd_4546650 := by exact prefixLift 4546650
  have htrace : WordTrace (prefixWord ++ tailWord_4546650) baseStart_4546650 baseEnd_4546650 := by
    simpa [prefixWord, tailWord_4546650, baseEnd_4546650] using wordTrace_append hprefix tailTrace_4546650
  have hstable : (prefixWord ++ tailWord_4546650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4546650).length < 2 ^ (prefixWord ++ tailWord_4546650).sum := by decide
  have hdescent : baseEnd_4546650 < baseStart_4546650 := by decide
  rcases family_descends (prefixWord ++ tailWord_4546650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4546660 : List Nat := [2, 3, 1, 1, 2, 1, 2, 3, 2, 6]
def baseStart_4546660 : Nat := 118140960795 + 4546660 * 2 ^ 59
def prefixEnd_4546660 : Nat := 4983230072969 + 3 ^ 40 * 4546660 * 2
def baseEnd_4546660 : Nat := 778207317523762135180099

theorem tailTrace_4546660 : CollatzResearch.WordTrace tailWord_4546660 prefixEnd_4546660 778207317523762135180099 := by
  unfold tailWord_4546660
  simp only [CollatzResearch.WordTrace]
  refine ⟨82915156854117401276086717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110553542472156535034782289 82915156854117401276086717)
  ·
    refine ⟨31093183820294025478532519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82915156854117401276086717 31093183820294025478532519)
    ·
      refine ⟨46639775730441038217798779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31093183820294025478532519 46639775730441038217798779)
      ·
        refine ⟨69959663595661557326698169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46639775730441038217798779 69959663595661557326698169)
        ·
          refine ⟨52469747696746167995023627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69959663595661557326698169 52469747696746167995023627)
          ·
            refine ⟨78704621545119251992535441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52469747696746167995023627 78704621545119251992535441)
            ·
              refine ⟨59028466158839438994401581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78704621545119251992535441 59028466158839438994401581)
              ·
                refine ⟨22135674809564789622900593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59028466158839438994401581 22135674809564789622900593)
                ·
                  refine ⟨16601756107173592217175445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22135674809564789622900593 16601756107173592217175445)
                  ·
                    refine ⟨778207317523762135180099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16601756107173592217175445 778207317523762135180099)
                    ·
                      rfl

theorem cell23_4546660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 3, 2, 6].length) (baseStart_4546660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4546660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4546660 prefixEnd_4546660 := by exact prefixLift 4546660
  have htrace : WordTrace (prefixWord ++ tailWord_4546660) baseStart_4546660 baseEnd_4546660 := by
    simpa [prefixWord, tailWord_4546660, baseEnd_4546660] using wordTrace_append hprefix tailTrace_4546660
  have hstable : (prefixWord ++ tailWord_4546660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4546660).length < 2 ^ (prefixWord ++ tailWord_4546660).sum := by decide
  have hdescent : baseEnd_4546660 < baseStart_4546660 := by decide
  rcases family_descends (prefixWord ++ tailWord_4546660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4546661 : List Nat := [1, 3, 1, 3, 2, 2, 4, 1, 2, 1, 3]
def baseStart_4546661 : Nat := 118140960795 + 4546661 * 2 ^ 59
def prefixEnd_4546661 : Nat := 4983230072969 + 3 ^ 40 * 4546661 * 2
def baseEnd_4546661 : Nat := 2334622466051940901627793

theorem tailTrace_4546661 : CollatzResearch.WordTrace tailWord_4546661 prefixEnd_4546661 2334622466051940901627793 := by
  unfold tailWord_4546661
  simp only [CollatzResearch.WordTrace]
  refine ⟨165830350181231179722959837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110553566787487453148639891 165830350181231179722959837)
  ·
    refine ⟨62186381317961692396109939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165830350181231179722959837 62186381317961692396109939)
    ·
      refine ⟨93279571976942538594164909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62186381317961692396109939 93279571976942538594164909)
      ·
        refine ⟨34979839491353451972811841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93279571976942538594164909 34979839491353451972811841)
        ·
          refine ⟨26234879618515088979608881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34979839491353451972811841 26234879618515088979608881)
          ·
            refine ⟨19676159713886316734706661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26234879618515088979608881 19676159713886316734706661)
            ·
              refine ⟨3689279946353684387757499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19676159713886316734706661 3689279946353684387757499)
              ·
                refine ⟨5533919919530526581636249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3689279946353684387757499 5533919919530526581636249)
                ·
                  refine ⟨4150439939647894936227187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5533919919530526581636249 4150439939647894936227187)
                  ·
                    refine ⟨6225659909471842404340781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4150439939647894936227187 6225659909471842404340781)
                    ·
                      refine ⟨2334622466051940901627793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6225659909471842404340781 2334622466051940901627793)
                      ·
                        rfl

theorem cell23_4546661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 4, 1, 2, 1, 3].length) (baseStart_4546661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4546661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4546661 prefixEnd_4546661 := by exact prefixLift 4546661
  have htrace : WordTrace (prefixWord ++ tailWord_4546661) baseStart_4546661 baseEnd_4546661 := by
    simpa [prefixWord, tailWord_4546661, baseEnd_4546661] using wordTrace_append hprefix tailTrace_4546661
  have hstable : (prefixWord ++ tailWord_4546661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4546661).length < 2 ^ (prefixWord ++ tailWord_4546661).sum := by decide
  have hdescent : baseEnd_4546661 < baseStart_4546661 := by decide
  rcases family_descends (prefixWord ++ tailWord_4546661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4546671 : List Nat := [1, 1, 2, 1, 3, 6, 1, 2, 1, 3, 2]
def baseStart_4546671 : Nat := 118140960795 + 4546671 * 2 ^ 59
def prefixEnd_4546671 : Nat := 4983230072969 + 3 ^ 40 * 4546671 * 2
def baseEnd_4546671 : Nat := 2334627600858485862502747

theorem tailTrace_4546671 : CollatzResearch.WordTrace tailWord_4546671 prefixEnd_4546671 2334627600858485862502747 := by
  unfold tailWord_4546671
  simp only [CollatzResearch.WordTrace]
  refine ⟨165830714911194951430823867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110553809940796634287215911 165830714911194951430823867)
  ·
    refine ⟨248746072366792427146235801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165830714911194951430823867 248746072366792427146235801)
    ·
      refine ⟨186559554275094320359676851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 248746072366792427146235801 186559554275094320359676851)
      ·
        refine ⟨279839331412641480539515277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186559554275094320359676851 279839331412641480539515277)
        ·
          refine ⟨104939749279740555202318229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 279839331412641480539515277 104939749279740555202318229)
          ·
            refine ⟨4919050747487838525108667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 104939749279740555202318229 4919050747487838525108667)
            ·
              refine ⟨7378576121231757787663001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4919050747487838525108667 7378576121231757787663001)
              ·
                refine ⟨5533932090923818340747251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7378576121231757787663001 5533932090923818340747251)
                ·
                  refine ⟨8300898136385727511120877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5533932090923818340747251 8300898136385727511120877)
                  ·
                    refine ⟨3112836801144647816670329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8300898136385727511120877 3112836801144647816670329)
                    ·
                      refine ⟨2334627600858485862502747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3112836801144647816670329 2334627600858485862502747)
                      ·
                        rfl

theorem cell23_4546671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 2, 1, 3, 2].length) (baseStart_4546671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4546671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4546671 prefixEnd_4546671 := by exact prefixLift 4546671
  have htrace : WordTrace (prefixWord ++ tailWord_4546671) baseStart_4546671 baseEnd_4546671 := by
    simpa [prefixWord, tailWord_4546671, baseEnd_4546671] using wordTrace_append hprefix tailTrace_4546671
  have hstable : (prefixWord ++ tailWord_4546671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4546671).length < 2 ^ (prefixWord ++ tailWord_4546671).sum := by decide
  have hdescent : baseEnd_4546671 < baseStart_4546671 := by decide
  rcases family_descends (prefixWord ++ tailWord_4546671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4546680 : List Nat := [2, 1, 2, 1, 1, 1, 3, 2, 4, 2, 4]
def baseStart_4546680 : Nat := 118140960795 + 4546680 * 2 ^ 59
def prefixEnd_4546680 : Nat := 4983230072969 + 3 ^ 40 * 4546680 * 2
def baseEnd_4546680 : Nat := 2334632222184376327290205

theorem tailTrace_4546680 : CollatzResearch.WordTrace tailWord_4546680 prefixEnd_4546680 2334632222184376327290205 := by
  unfold tailWord_4546680
  simp only [CollatzResearch.WordTrace]
  refine ⟨82915521584081172983950747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110554028778774897311934329 82915521584081172983950747)
  ·
    refine ⟨124373282376121759475926121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82915521584081172983950747 124373282376121759475926121)
    ·
      refine ⟨93279961782091319606944591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124373282376121759475926121 93279961782091319606944591)
      ·
        refine ⟨139919942673136979410416887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93279961782091319606944591 139919942673136979410416887)
        ·
          refine ⟨209879914009705469115625331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139919942673136979410416887 209879914009705469115625331)
          ·
            refine ⟨314819871014558203673437997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 209879914009705469115625331 314819871014558203673437997)
            ·
              refine ⟨118057451630459326377539249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 314819871014558203673437997 118057451630459326377539249)
              ·
                refine ⟨88543088722844494783154437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 118057451630459326377539249 88543088722844494783154437)
                ·
                  refine ⟨16601829135533342771841457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 88543088722844494783154437 16601829135533342771841457)
                  ·
                    refine ⟨12451371851650007078881093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16601829135533342771841457 12451371851650007078881093)
                    ·
                      refine ⟨2334632222184376327290205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12451371851650007078881093 2334632222184376327290205)
                      ·
                        rfl

theorem cell23_4546680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 4, 2, 4].length) (baseStart_4546680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4546680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4546680 prefixEnd_4546680 := by exact prefixLift 4546680
  have htrace : WordTrace (prefixWord ++ tailWord_4546680) baseStart_4546680 baseEnd_4546680 := by
    simpa [prefixWord, tailWord_4546680, baseEnd_4546680] using wordTrace_append hprefix tailTrace_4546680
  have hstable : (prefixWord ++ tailWord_4546680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4546680).length < 2 ^ (prefixWord ++ tailWord_4546680).sum := by decide
  have hdescent : baseEnd_4546680 < baseStart_4546680 := by decide
  rcases family_descends (prefixWord ++ tailWord_4546680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4546684 : List Nat := [2, 2, 2, 1, 1, 5, 1, 2, 1, 4, 2]
def baseStart_4546684 : Nat := 118140960795 + 4546684 * 2 ^ 59
def prefixEnd_4546684 : Nat := 4983230072969 + 3 ^ 40 * 4546684 * 2
def baseEnd_4546684 : Nat := 2334634276106994311640187

theorem tailTrace_4546684 : CollatzResearch.WordTrace tailWord_4546684 prefixEnd_4546684 2334634276106994311640187 := by
  unfold tailWord_4546684
  simp only [CollatzResearch.WordTrace]
  refine ⟨82915594530073927325523553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110554126040098569767364737 82915594530073927325523553)
  ·
    refine ⟨62186695897555445494142665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82915594530073927325523553 62186695897555445494142665)
    ·
      refine ⟨46640021923166584120606999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62186695897555445494142665 46640021923166584120606999)
      ·
        refine ⟨69960032884749876180910499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46640021923166584120606999 69960032884749876180910499)
        ·
          refine ⟨104940049327124814271365749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69960032884749876180910499 104940049327124814271365749)
          ·
            refine ⟨9838129624417951337940539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 104940049327124814271365749 9838129624417951337940539)
            ·
              refine ⟨14757194436626927006910809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9838129624417951337940539 14757194436626927006910809)
              ·
                refine ⟨11067895827470195255183107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14757194436626927006910809 11067895827470195255183107)
                ·
                  refine ⟨16601843741205292882774661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11067895827470195255183107 16601843741205292882774661)
                  ·
                    refine ⟨3112845701475992415520249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16601843741205292882774661 3112845701475992415520249)
                    ·
                      refine ⟨2334634276106994311640187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3112845701475992415520249 2334634276106994311640187)
                      ·
                        rfl

theorem cell23_4546684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 2, 1, 4, 2].length) (baseStart_4546684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4546684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4546684 prefixEnd_4546684 := by exact prefixLift 4546684
  have htrace : WordTrace (prefixWord ++ tailWord_4546684) baseStart_4546684 baseEnd_4546684 := by
    simpa [prefixWord, tailWord_4546684, baseEnd_4546684] using wordTrace_append hprefix tailTrace_4546684
  have hstable : (prefixWord ++ tailWord_4546684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4546684).length < 2 ^ (prefixWord ++ tailWord_4546684).sum := by decide
  have hdescent : baseEnd_4546684 < baseStart_4546684 := by decide
  rcases family_descends (prefixWord ++ tailWord_4546684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4546714 : List Nat := [3, 1, 1, 5, 2, 1, 1, 1, 2, 2, 4]
def baseStart_4546714 : Nat := 118140960795 + 4546714 * 2 ^ 59
def prefixEnd_4546714 : Nat := 4983230072969 + 3 ^ 40 * 4546714 * 2
def baseEnd_4546714 : Nat := 2334649680526629194265049

theorem tailTrace_4546714 : CollatzResearch.WordTrace tailWord_4546714 prefixEnd_4546714 2334649680526629194265049 := by
  unfold tailWord_4546714
  simp only [CollatzResearch.WordTrace]
  refine ⟨41458070812509792443659799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110554855500026113183092797 41458070812509792443659799)
  ·
    refine ⟨62187106218764688665489699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41458070812509792443659799 62187106218764688665489699)
    ·
      refine ⟨93280659328147032998234549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62187106218764688665489699 93280659328147032998234549)
      ·
        refine ⟨8745061812013784343584489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 93280659328147032998234549 8745061812013784343584489)
        ·
          refine ⟨6558796359010338257688367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8745061812013784343584489 6558796359010338257688367)
          ·
            refine ⟨9838194538515507386532551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6558796359010338257688367 9838194538515507386532551)
            ·
              refine ⟨14757291807773261079798827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9838194538515507386532551 14757291807773261079798827)
              ·
                refine ⟨22135937711659891619698241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14757291807773261079798827 22135937711659891619698241)
                ·
                  refine ⟨16601953283744918714773681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22135937711659891619698241 16601953283744918714773681)
                  ·
                    refine ⟨12451464962808689036080261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16601953283744918714773681 12451464962808689036080261)
                    ·
                      refine ⟨2334649680526629194265049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12451464962808689036080261 2334649680526629194265049)
                      ·
                        rfl

theorem cell23_4546714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_4546714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4546714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4546714 prefixEnd_4546714 := by exact prefixLift 4546714
  have htrace : WordTrace (prefixWord ++ tailWord_4546714) baseStart_4546714 baseEnd_4546714 := by
    simpa [prefixWord, tailWord_4546714, baseEnd_4546714] using wordTrace_append hprefix tailTrace_4546714
  have hstable : (prefixWord ++ tailWord_4546714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4546714).length < 2 ^ (prefixWord ++ tailWord_4546714).sum := by decide
  have hdescent : baseEnd_4546714 < baseStart_4546714 := by decide
  rcases family_descends (prefixWord ++ tailWord_4546714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4546717 : List Nat := [1, 4, 2, 1, 1, 3, 1, 1, 1, 5, 3]
def baseStart_4546717 : Nat := 118140960795 + 4546717 * 2 ^ 59
def prefixEnd_4546717 : Nat := 4983230072969 + 3 ^ 40 * 4546717 * 2
def baseEnd_4546717 : Nat := 2334651220968592682527535

theorem tailTrace_4546717 : CollatzResearch.WordTrace tailWord_4546717 prefixEnd_4546717 2334651220968592682527535 := by
  unfold tailWord_4546717
  simp only [CollatzResearch.WordTrace]
  refine ⟨165832392669028301286998405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110554928446018867524665603 165832392669028301286998405)
  ·
    refine ⟨31093573625442806491312201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 165832392669028301286998405 31093573625442806491312201)
    ·
      refine ⟨23320180219082104868484151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31093573625442806491312201 23320180219082104868484151)
      ·
        refine ⟨34980270328623157302726227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23320180219082104868484151 34980270328623157302726227)
        ·
          refine ⟨52470405492934735954089341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34980270328623157302726227 52470405492934735954089341)
          ·
            refine ⟨19676402059850525982783503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52470405492934735954089341 19676402059850525982783503)
            ·
              refine ⟨29514603089775788974175255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19676402059850525982783503 29514603089775788974175255)
              ·
                refine ⟨44271904634663683461262883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29514603089775788974175255 44271904634663683461262883)
                ·
                  refine ⟨66407856951995525191894325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44271904634663683461262883 66407856951995525191894325)
                  ·
                    refine ⟨6225736589249580486740093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 66407856951995525191894325 6225736589249580486740093)
                    ·
                      refine ⟨2334651220968592682527535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6225736589249580486740093 2334651220968592682527535)
                      ·
                        rfl

theorem cell23_4546717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 5, 3].length) (baseStart_4546717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4546717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4546717 prefixEnd_4546717 := by exact prefixLift 4546717
  have htrace : WordTrace (prefixWord ++ tailWord_4546717) baseStart_4546717 baseEnd_4546717 := by
    simpa [prefixWord, tailWord_4546717, baseEnd_4546717] using wordTrace_append hprefix tailTrace_4546717
  have hstable : (prefixWord ++ tailWord_4546717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4546717).length < 2 ^ (prefixWord ++ tailWord_4546717).sum := by decide
  have hdescent : baseEnd_4546717 < baseStart_4546717 := by decide
  rcases family_descends (prefixWord ++ tailWord_4546717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4546718 : List Nat := [4, 3, 1, 1, 3, 1, 2, 1, 1, 4, 2]
def baseStart_4546718 : Nat := 118140960795 + 4546718 * 2 ^ 59
def prefixEnd_4546718 : Nat := 4983230072969 + 3 ^ 40 * 4546718 * 2
def baseEnd_4546718 : Nat := 2334651734449247178615031

theorem tailTrace_4546718 : CollatzResearch.WordTrace tailWord_4546718 prefixEnd_4546718 2334651734449247178615031 := by
  unfold tailWord_4546718
  simp only [CollatzResearch.WordTrace]
  refine ⟨20729053642753084807223101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110554952761349785638523205 20729053642753084807223101)
  ·
    refine ⟨7773395116032406802708663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20729053642753084807223101 7773395116032406802708663)
    ·
      refine ⟨11660092674048610204062995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7773395116032406802708663 11660092674048610204062995)
      ·
        refine ⟨17490139011072915306094493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11660092674048610204062995 17490139011072915306094493)
        ·
          refine ⟨6558802129152343239785435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17490139011072915306094493 6558802129152343239785435)
          ·
            refine ⟨9838203193728514859678153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6558802129152343239785435 9838203193728514859678153)
            ·
              refine ⟨7378652395296386144758615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9838203193728514859678153 7378652395296386144758615)
              ·
                refine ⟨11067978592944579217137923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7378652395296386144758615 11067978592944579217137923)
                ·
                  refine ⟨16601967889416868825706885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11067978592944579217137923 16601967889416868825706885)
                  ·
                    refine ⟨3112868979265662904820041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16601967889416868825706885 3112868979265662904820041)
                    ·
                      refine ⟨2334651734449247178615031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3112868979265662904820041 2334651734449247178615031)
                      ·
                        rfl

theorem cell23_4546718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 1, 1, 4, 2].length) (baseStart_4546718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4546718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4546718 prefixEnd_4546718 := by exact prefixLift 4546718
  have htrace : WordTrace (prefixWord ++ tailWord_4546718) baseStart_4546718 baseEnd_4546718 := by
    simpa [prefixWord, tailWord_4546718, baseEnd_4546718] using wordTrace_append hprefix tailTrace_4546718
  have hstable : (prefixWord ++ tailWord_4546718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4546718).length < 2 ^ (prefixWord ++ tailWord_4546718).sum := by decide
  have hdescent : baseEnd_4546718 < baseStart_4546718 := by decide
  rcases family_descends (prefixWord ++ tailWord_4546718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4546757 : List Nat := [1, 3, 1, 1, 1, 1, 4, 4, 2, 1, 4]
def baseStart_4546757 : Nat := 118140960795 + 4546757 * 2 ^ 59
def prefixEnd_4546757 : Nat := 4983230072969 + 3 ^ 40 * 4546757 * 2
def baseEnd_4546757 : Nat := 2334671760194772526027351

theorem tailTrace_4546757 : CollatzResearch.WordTrace tailWord_4546757 prefixEnd_4546757 2334671760194772526027351 := by
  unfold tailWord_4546757
  simp only [CollatzResearch.WordTrace]
  refine ⟨165833851588883388118454525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110555901059255592078969683 165833851588883388118454525)
  ·
    refine ⟨62187694345831270544420447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165833851588883388118454525 62187694345831270544420447)
    ·
      refine ⟨93281541518746905816630671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62187694345831270544420447 93281541518746905816630671)
      ·
        refine ⟨139922312278120358724946007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93281541518746905816630671 139922312278120358724946007)
        ·
          refine ⟨209883468417180538087419011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139922312278120358724946007 209883468417180538087419011)
          ·
            refine ⟨314825202625770807131128517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 209883468417180538087419011 314825202625770807131128517)
            ·
              refine ⟨59029725492332026337086597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 314825202625770807131128517 59029725492332026337086597)
              ·
                refine ⟨11068073529812254938203737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59029725492332026337086597 11068073529812254938203737)
                ·
                  refine ⟨8301055147359191203652803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11068073529812254938203737 8301055147359191203652803)
                  ·
                    refine ⟨12451582721038786805479205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8301055147359191203652803 12451582721038786805479205)
                    ·
                      refine ⟨2334671760194772526027351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12451582721038786805479205 2334671760194772526027351)
                      ·
                        rfl

theorem cell23_4546757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 4, 2, 1, 4].length) (baseStart_4546757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4546757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4546757 prefixEnd_4546757 := by exact prefixLift 4546757
  have htrace : WordTrace (prefixWord ++ tailWord_4546757) baseStart_4546757 baseEnd_4546757 := by
    simpa [prefixWord, tailWord_4546757, baseEnd_4546757] using wordTrace_append hprefix tailTrace_4546757
  have hstable : (prefixWord ++ tailWord_4546757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4546757).length < 2 ^ (prefixWord ++ tailWord_4546757).sum := by decide
  have hdescent : baseEnd_4546757 < baseStart_4546757 := by decide
  rcases family_descends (prefixWord ++ tailWord_4546757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4546777 : List Nat := [1, 2, 1, 2, 3, 1, 3, 2, 1, 4, 3]
def baseStart_4546777 : Nat := 118140960795 + 4546777 * 2 ^ 59
def prefixEnd_4546777 : Nat := 4983230072969 + 3 ^ 40 * 4546777 * 2
def baseEnd_4546777 : Nat := 2334682029807862447777259

theorem tailTrace_4546777 : CollatzResearch.WordTrace tailWord_4546777 prefixEnd_4546777 2334682029807862447777259 := by
  unfold tailWord_4546777
  simp only [CollatzResearch.WordTrace]
  refine ⟨165834581048810931534182585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110556387365873954356121723 165834581048810931534182585)
  ·
    refine ⟨124375935786608198650636939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165834581048810931534182585 124375935786608198650636939)
    ·
      refine ⟨186563903679912297975955409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124375935786608198650636939 186563903679912297975955409)
      ·
        refine ⟨139922927759934223481966557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186563903679912297975955409 139922927759934223481966557)
        ·
          refine ⟨52471097909975333805737459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 139922927759934223481966557 52471097909975333805737459)
          ·
            refine ⟨78706646864963000708606189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52471097909975333805737459 78706646864963000708606189)
            ·
              refine ⟨29514992574361125265727321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78706646864963000708606189 29514992574361125265727321)
              ·
                refine ⟨22136244430770843949295491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29514992574361125265727321 22136244430770843949295491)
                ·
                  refine ⟨33204366646156265923943237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22136244430770843949295491 33204366646156265923943237)
                  ·
                    refine ⟨6225818746154299860739357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33204366646156265923943237 6225818746154299860739357)
                    ·
                      refine ⟨2334682029807862447777259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6225818746154299860739357 2334682029807862447777259)
                      ·
                        rfl

theorem cell23_4546777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 2, 1, 4, 3].length) (baseStart_4546777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4546777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4546777 prefixEnd_4546777 := by exact prefixLift 4546777
  have htrace : WordTrace (prefixWord ++ tailWord_4546777) baseStart_4546777 baseEnd_4546777 := by
    simpa [prefixWord, tailWord_4546777, baseEnd_4546777] using wordTrace_append hprefix tailTrace_4546777
  have hstable : (prefixWord ++ tailWord_4546777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4546777).length < 2 ^ (prefixWord ++ tailWord_4546777).sum := by decide
  have hdescent : baseEnd_4546777 < baseStart_4546777 := by decide
  rcases family_descends (prefixWord ++ tailWord_4546777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4546794 : List Nat := [3, 1, 3, 1, 1, 2, 2, 3, 2, 2, 3]
def baseStart_4546794 : Nat := 118140960795 + 4546794 * 2 ^ 59
def prefixEnd_4546794 : Nat := 4983230072969 + 3 ^ 40 * 4546794 * 2
def baseEnd_4546794 : Nat := 2334690758978988881264681

theorem tailTrace_4546794 : CollatzResearch.WordTrace tailWord_4546794 prefixEnd_4546794 2334690758978988881264681 := by
  unfold tailWord_4546794
  simp only [CollatzResearch.WordTrace]
  refine ⟨41458800272437335859387859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110556800726499562291700957 41458800272437335859387859)
  ·
    refine ⟨62188200408656003789081789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41458800272437335859387859 62188200408656003789081789)
    ·
      refine ⟨23320575153246001420905671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62188200408656003789081789 23320575153246001420905671)
      ·
        refine ⟨34980862729869002131358507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23320575153246001420905671 34980862729869002131358507)
        ·
          refine ⟨52471294094803503197037761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34980862729869002131358507 52471294094803503197037761)
          ·
            refine ⟨39353470571102627397778321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52471294094803503197037761 39353470571102627397778321)
            ·
              refine ⟨29515102928326970548333741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39353470571102627397778321 29515102928326970548333741)
              ·
                refine ⟨11068163598122613955625153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29515102928326970548333741 11068163598122613955625153)
                ·
                  refine ⟨8301122698591960466718865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11068163598122613955625153 8301122698591960466718865)
                  ·
                    refine ⟨6225842023943970350039149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8301122698591960466718865 6225842023943970350039149)
                    ·
                      refine ⟨2334690758978988881264681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6225842023943970350039149 2334690758978988881264681)
                      ·
                        rfl

theorem cell23_4546794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 3, 2, 2, 3].length) (baseStart_4546794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4546794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4546794 prefixEnd_4546794 := by exact prefixLift 4546794
  have htrace : WordTrace (prefixWord ++ tailWord_4546794) baseStart_4546794 baseEnd_4546794 := by
    simpa [prefixWord, tailWord_4546794, baseEnd_4546794] using wordTrace_append hprefix tailTrace_4546794
  have hstable : (prefixWord ++ tailWord_4546794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4546794).length < 2 ^ (prefixWord ++ tailWord_4546794).sum := by decide
  have hdescent : baseEnd_4546794 < baseStart_4546794 := by decide
  rcases family_descends (prefixWord ++ tailWord_4546794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4546801 : List Nat := [1, 2, 2, 2, 2, 1, 5, 3, 1, 4]
def baseStart_4546801 : Nat := 118140960795 + 4546801 * 2 ^ 59
def prefixEnd_4546801 : Nat := 4983230072969 + 3 ^ 40 * 4546801 * 2
def baseEnd_4546801 : Nat := 778231451114523451292383

theorem tailTrace_4546801 : CollatzResearch.WordTrace tailWord_4546801 prefixEnd_4546801 778231451114523451292383 := by
  unfold tailWord_4546801
  simp only [CollatzResearch.WordTrace]
  refine ⟨165835456400723983633056257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110556970933815989088704171 165835456400723983633056257)
  ·
    refine ⟨124376592300542987724792193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165835456400723983633056257 124376592300542987724792193)
    ·
      refine ⟨93282444225407240793594145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124376592300542987724792193 93282444225407240793594145)
      ·
        refine ⟨69961833169055430595195609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93282444225407240793594145 69961833169055430595195609)
        ·
          refine ⟨52471374876791572946396707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69961833169055430595195609 52471374876791572946396707)
          ·
            refine ⟨78707062315187359419595061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52471374876791572946396707 78707062315187359419595061)
            ·
              refine ⟨7378787092048814945587037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 78707062315187359419595061 7378787092048814945587037)
              ·
                refine ⟨2767045159518305604595139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7378787092048814945587037 2767045159518305604595139)
                ·
                  refine ⟨4150567739277458406892709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2767045159518305604595139 4150567739277458406892709)
                  ·
                    refine ⟨778231451114523451292383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4150567739277458406892709 778231451114523451292383)
                    ·
                      rfl

theorem cell23_4546801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 3, 1, 4].length) (baseStart_4546801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4546801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4546801 prefixEnd_4546801 := by exact prefixLift 4546801
  have htrace : WordTrace (prefixWord ++ tailWord_4546801) baseStart_4546801 baseEnd_4546801 := by
    simpa [prefixWord, tailWord_4546801, baseEnd_4546801] using wordTrace_append hprefix tailTrace_4546801
  have hstable : (prefixWord ++ tailWord_4546801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4546801).length < 2 ^ (prefixWord ++ tailWord_4546801).sum := by decide
  have hdescent : baseEnd_4546801 < baseStart_4546801 := by decide
  rcases family_descends (prefixWord ++ tailWord_4546801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4546814 : List Nat := [4, 2, 2, 1, 1, 1, 2, 4, 6]
def baseStart_4546814 : Nat := 118140960795 + 4546814 * 2 ^ 59
def prefixEnd_4546814 : Nat := 4983230072969 + 3 ^ 40 * 4546814 * 2
def baseEnd_4546814 : Nat := 259411225399119867001621

theorem tailTrace_4546814 : CollatzResearch.WordTrace tailWord_4546814 prefixEnd_4546814 259411225399119867001621 := by
  unfold tailWord_4546814
  simp only [CollatzResearch.WordTrace]
  refine ⟨20729491318709610856659937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110557287033117924568852997 20729491318709610856659937)
  ·
    refine ⟨15547118489032208142494953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20729491318709610856659937 15547118489032208142494953)
    ·
      refine ⟨11660338866774156106871215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15547118489032208142494953 11660338866774156106871215)
      ·
        refine ⟨17490508300161234160306823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11660338866774156106871215 17490508300161234160306823)
        ·
          refine ⟨26235762450241851240460235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17490508300161234160306823 26235762450241851240460235)
          ·
            refine ⟨39353643675362776860690353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26235762450241851240460235 39353643675362776860690353)
            ·
              refine ⟨29515232756522082645517765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39353643675362776860690353 29515232756522082645517765)
              ·
                refine ⟨5534106141847890496034581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29515232756522082645517765 5534106141847890496034581)
                ·
                  refine ⟨259411225399119867001621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5534106141847890496034581 259411225399119867001621)
                  ·
                    rfl

theorem cell23_4546814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 4, 6].length) (baseStart_4546814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4546814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4546814 prefixEnd_4546814 := by exact prefixLift 4546814
  have htrace : WordTrace (prefixWord ++ tailWord_4546814) baseStart_4546814 baseEnd_4546814 := by
    simpa [prefixWord, tailWord_4546814, baseEnd_4546814] using wordTrace_append hprefix tailTrace_4546814
  have hstable : (prefixWord ++ tailWord_4546814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4546814).length < 2 ^ (prefixWord ++ tailWord_4546814).sum := by decide
  have hdescent : baseEnd_4546814 < baseStart_4546814 := by decide
  rcases family_descends (prefixWord ++ tailWord_4546814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4546818 : List Nat := [3, 4, 1, 1, 2, 3, 1, 1, 3, 4]
def baseStart_4546818 : Nat := 118140960795 + 4546818 * 2 ^ 59
def prefixEnd_4546818 : Nat := 4983230072969 + 3 ^ 40 * 4546818 * 2
def baseEnd_4546818 : Nat := 778234360838232262454857

theorem tailTrace_4546818 : CollatzResearch.WordTrace tailWord_4546818 prefixEnd_4546818 778234360838232262454857 := by
  unfold tailWord_4546818
  simp only [CollatzResearch.WordTrace]
  refine ⟨41459019110415598884106277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110557384294441597024283405 41459019110415598884106277)
  ·
    refine ⟨7773566083202924790769927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41459019110415598884106277 7773566083202924790769927)
    ·
      refine ⟨11660349124804387186154891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7773566083202924790769927 11660349124804387186154891)
      ·
        refine ⟨17490523687206580779232337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11660349124804387186154891 17490523687206580779232337)
        ·
          refine ⟨13117892765404935584424253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17490523687206580779232337 13117892765404935584424253)
          ·
            refine ⟨4919209787026850844159095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13117892765404935584424253 4919209787026850844159095)
            ·
              refine ⟨7378814680540276266238643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4919209787026850844159095 7378814680540276266238643)
              ·
                refine ⟨11068222020810414399357965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7378814680540276266238643 11068222020810414399357965)
                ·
                  refine ⟨4150583257803905399759237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11068222020810414399357965 4150583257803905399759237)
                  ·
                    refine ⟨778234360838232262454857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4150583257803905399759237 778234360838232262454857)
                    ·
                      rfl

theorem cell23_4546818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_4546818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4546818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4546818 prefixEnd_4546818 := by exact prefixLift 4546818
  have htrace : WordTrace (prefixWord ++ tailWord_4546818) baseStart_4546818 baseEnd_4546818 := by
    simpa [prefixWord, tailWord_4546818, baseEnd_4546818] using wordTrace_append hprefix tailTrace_4546818
  have hstable : (prefixWord ++ tailWord_4546818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4546818).length < 2 ^ (prefixWord ++ tailWord_4546818).sum := by decide
  have hdescent : baseEnd_4546818 < baseStart_4546818 := by decide
  rcases family_descends (prefixWord ++ tailWord_4546818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4546827 : List Nat := [1, 1, 1, 1, 5, 2, 2, 2, 3, 5]
def baseStart_4546827 : Nat := 118140960795 + 4546827 * 2 ^ 59
def prefixEnd_4546827 : Nat := 4983230072969 + 3 ^ 40 * 4546827 * 2
def baseEnd_4546827 : Nat := 778235901280195750717343

theorem tailTrace_4546827 : CollatzResearch.WordTrace tailWord_4546827 prefixEnd_4546827 778235901280195750717343 := by
  unfold tailWord_4546827
  simp only [CollatzResearch.WordTrace]
  refine ⟨165836404698629790073502735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110557603132419860049001823 165836404698629790073502735)
  ·
    refine ⟨248754607047944685110254103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165836404698629790073502735 248754607047944685110254103)
    ·
      refine ⟨373131910571917027665381155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248754607047944685110254103 373131910571917027665381155)
      ·
        refine ⟨559697865857875541498071733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 373131910571917027665381155 559697865857875541498071733)
        ·
          refine ⟨52471674924175832015444225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 559697865857875541498071733 52471674924175832015444225)
          ·
            refine ⟨39353756193131874011583169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52471674924175832015444225 39353756193131874011583169)
            ·
              refine ⟨29515317144848905508687377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39353756193131874011583169 29515317144848905508687377)
              ·
                refine ⟨22136487858636679131515533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29515317144848905508687377 22136487858636679131515533)
                ·
                  refine ⟨8301182946988754674318325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22136487858636679131515533 8301182946988754674318325)
                  ·
                    refine ⟨778235901280195750717343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8301182946988754674318325 778235901280195750717343)
                    ·
                      rfl

theorem cell23_4546827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 2, 3, 5].length) (baseStart_4546827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4546827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4546827 prefixEnd_4546827 := by exact prefixLift 4546827
  have htrace : WordTrace (prefixWord ++ tailWord_4546827) baseStart_4546827 baseEnd_4546827 := by
    simpa [prefixWord, tailWord_4546827, baseEnd_4546827] using wordTrace_append hprefix tailTrace_4546827
  have hstable : (prefixWord ++ tailWord_4546827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4546827).length < 2 ^ (prefixWord ++ tailWord_4546827).sum := by decide
  have hdescent : baseEnd_4546827 < baseStart_4546827 := by decide
  rcases family_descends (prefixWord ++ tailWord_4546827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4546851 : List Nat := [1, 1, 1, 4, 2, 2, 4, 1, 2, 3, 2]
def baseStart_4546851 : Nat := 118140960795 + 4546851 * 2 ^ 59
def prefixEnd_4546851 : Nat := 4983230072969 + 3 ^ 40 * 4546851 * 2
def baseEnd_4546851 : Nat := 2334720027376295158251919

theorem tailTrace_4546851 : CollatzResearch.WordTrace tailWord_4546851 prefixEnd_4546851 2334720027376295158251919 := by
  unfold tailWord_4546851
  simp only [CollatzResearch.WordTrace]
  refine ⟨165837280050542842172376407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110558186700361894781584271 165837280050542842172376407)
  ·
    refine ⟨248755920075814263258564611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165837280050542842172376407 248755920075814263258564611)
    ·
      refine ⟨373133880113721394887846917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248755920075814263258564611 373133880113721394887846917)
      ·
        refine ⟨69962602521322761541471297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 373133880113721394887846917 69962602521322761541471297)
        ·
          refine ⟨52471951890992071156103473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69962602521322761541471297 52471951890992071156103473)
          ·
            refine ⟨39353963918244053367077605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52471951890992071156103473 39353963918244053367077605)
            ·
              refine ⟨7378868234670760006327051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39353963918244053367077605 7378868234670760006327051)
              ·
                refine ⟨11068302352006140009490577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7378868234670760006327051 11068302352006140009490577)
                ·
                  refine ⟨8301226764004605007117933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11068302352006140009490577 8301226764004605007117933)
                  ·
                    refine ⟨3112960036501726877669225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8301226764004605007117933 3112960036501726877669225)
                    ·
                      refine ⟨2334720027376295158251919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3112960036501726877669225 2334720027376295158251919)
                      ·
                        rfl

theorem cell23_4546851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 1, 2, 3, 2].length) (baseStart_4546851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4546851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4546851 prefixEnd_4546851 := by exact prefixLift 4546851
  have htrace : WordTrace (prefixWord ++ tailWord_4546851) baseStart_4546851 baseEnd_4546851 := by
    simpa [prefixWord, tailWord_4546851, baseEnd_4546851] using wordTrace_append hprefix tailTrace_4546851
  have hstable : (prefixWord ++ tailWord_4546851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4546851).length < 2 ^ (prefixWord ++ tailWord_4546851).sum := by decide
  have hdescent : baseEnd_4546851 < baseStart_4546851 := by decide
  rcases family_descends (prefixWord ++ tailWord_4546851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4546868 : List Nat := [2, 5, 1, 1, 1, 2, 2, 2, 2, 3, 2]
def baseStart_4546868 : Nat := 118140960795 + 4546868 * 2 ^ 59
def prefixEnd_4546868 : Nat := 4983230072969 + 3 ^ 40 * 4546868 * 2
def baseEnd_4546868 : Nat := 2334728756547421591739341

theorem tailTrace_4546868 : CollatzResearch.WordTrace tailWord_4546868 prefixEnd_4546868 2334728756547421591739341 := by
  unfold tailWord_4546868
  simp only [CollatzResearch.WordTrace]
  refine ⟨82918950045740627037872629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110558600060987502717163505 82918950045740627037872629)
  ·
    refine ⟨7773651566788183784800559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 82918950045740627037872629 7773651566788183784800559)
    ·
      refine ⟨11660477350182275677200839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7773651566788183784800559 11660477350182275677200839)
      ·
        refine ⟨17490716025273413515801259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11660477350182275677200839 17490716025273413515801259)
        ·
          refine ⟨26236074037910120273701889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17490716025273413515801259 26236074037910120273701889)
          ·
            refine ⟨19677055528432590205276417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26236074037910120273701889 19677055528432590205276417)
            ·
              refine ⟨14757791646324442653957313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19677055528432590205276417 14757791646324442653957313)
              ·
                refine ⟨11068343734743331990467985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14757791646324442653957313 11068343734743331990467985)
                ·
                  refine ⟨8301257801057498992850989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11068343734743331990467985 8301257801057498992850989)
                  ·
                    refine ⟨3112971675396562122319121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8301257801057498992850989 3112971675396562122319121)
                    ·
                      refine ⟨2334728756547421591739341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3112971675396562122319121 2334728756547421591739341)
                      ·
                        rfl

theorem cell23_4546868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 2, 2, 3, 2].length) (baseStart_4546868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4546868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4546868 prefixEnd_4546868 := by exact prefixLift 4546868
  have htrace : WordTrace (prefixWord ++ tailWord_4546868) baseStart_4546868 baseEnd_4546868 := by
    simpa [prefixWord, tailWord_4546868, baseEnd_4546868] using wordTrace_append hprefix tailTrace_4546868
  have hstable : (prefixWord ++ tailWord_4546868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4546868).length < 2 ^ (prefixWord ++ tailWord_4546868).sum := by decide
  have hdescent : baseEnd_4546868 < baseStart_4546868 := by decide
  rcases family_descends (prefixWord ++ tailWord_4546868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4546915 : List Nat := [1, 1, 1, 5, 2, 1, 4, 3, 1, 2, 2]
def baseStart_4546915 : Nat := 118140960795 + 4546915 * 2 ^ 59
def prefixEnd_4546915 : Nat := 4983230072969 + 3 ^ 40 * 4546915 * 2
def baseEnd_4546915 : Nat := 2334752890138182907851625

theorem tailTrace_4546915 : CollatzResearch.WordTrace tailWord_4546915 prefixEnd_4546915 2334752890138182907851625 := by
  unfold tailWord_4546915
  simp only [CollatzResearch.WordTrace]
  refine ⟨165839614322310981102706199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110559742881540654068470799 165839614322310981102706199)
  ·
    refine ⟨248759421483466471654059299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165839614322310981102706199 248759421483466471654059299)
    ·
      refine ⟨373139132225199707481088949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248759421483466471654059299 373139132225199707481088949)
      ·
        refine ⟨34981793646112472576352089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 373139132225199707481088949 34981793646112472576352089)
        ·
          refine ⟨26236345234584354432264067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34981793646112472576352089 26236345234584354432264067)
          ·
            refine ⟨39354517851876531648396101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26236345234584354432264067 39354517851876531648396101)
            ·
              refine ⟨7378972097226849684074269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39354517851876531648396101 7378972097226849684074269)
              ·
                refine ⟨2767114536460068631527851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7378972097226849684074269 2767114536460068631527851)
                ·
                  refine ⟨4150671804690102947291777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2767114536460068631527851 4150671804690102947291777)
                  ·
                    refine ⟨3113003853517577210468833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4150671804690102947291777 3113003853517577210468833)
                    ·
                      refine ⟨2334752890138182907851625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3113003853517577210468833 2334752890138182907851625)
                      ·
                        rfl

theorem cell23_4546915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 3, 1, 2, 2].length) (baseStart_4546915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4546915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4546915 prefixEnd_4546915 := by exact prefixLift 4546915
  have htrace : WordTrace (prefixWord ++ tailWord_4546915) baseStart_4546915 baseEnd_4546915 := by
    simpa [prefixWord, tailWord_4546915, baseEnd_4546915] using wordTrace_append hprefix tailTrace_4546915
  have hstable : (prefixWord ++ tailWord_4546915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4546915).length < 2 ^ (prefixWord ++ tailWord_4546915).sum := by decide
  have hdescent : baseEnd_4546915 < baseStart_4546915 := by decide
  rcases family_descends (prefixWord ++ tailWord_4546915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4546927 : List Nat := [1, 1, 2, 1, 3, 1, 2, 1, 4, 2, 5]
def baseStart_4546927 : Nat := 118140960795 + 4546927 * 2 ^ 59
def prefixEnd_4546927 : Nat := 4983230072969 + 3 ^ 40 * 4546927 * 2
def baseEnd_4546927 : Nat := 2334759051906036860901569

theorem tailTrace_4546927 : CollatzResearch.WordTrace tailWord_4546927 prefixEnd_4546927 2334759051906036860901569 := by
  unfold tailWord_4546927
  simp only [CollatzResearch.WordTrace]
  refine ⟨165840051998267507152143035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110560034665511671434762023 165840051998267507152143035)
  ·
    refine ⟨248760077997401260728214553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165840051998267507152143035 248760077997401260728214553)
    ·
      refine ⟨186570058498050945546160915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 248760077997401260728214553 186570058498050945546160915)
      ·
        refine ⟨279855087747076418319241373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186570058498050945546160915 279855087747076418319241373)
        ·
          refine ⟨104945657905153656869715515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 279855087747076418319241373 104945657905153656869715515)
          ·
            refine ⟨157418486857730485304573273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104945657905153656869715515 157418486857730485304573273)
            ·
              refine ⟨118063865143297863978429955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 157418486857730485304573273 118063865143297863978429955)
              ·
                refine ⟨177095797714946795967644933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118063865143297863978429955 177095797714946795967644933)
                ·
                  refine ⟨33205462071552524243933425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 177095797714946795967644933 33205462071552524243933425)
                  ·
                    refine ⟨24904096553664393182950069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33205462071552524243933425 24904096553664393182950069)
                    ·
                      refine ⟨2334759051906036860901569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24904096553664393182950069 2334759051906036860901569)
                      ·
                        rfl

theorem cell23_4546927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 4, 2, 5].length) (baseStart_4546927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4546927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4546927 prefixEnd_4546927 := by exact prefixLift 4546927
  have htrace : WordTrace (prefixWord ++ tailWord_4546927) baseStart_4546927 baseEnd_4546927 := by
    simpa [prefixWord, tailWord_4546927, baseEnd_4546927] using wordTrace_append hprefix tailTrace_4546927
  have hstable : (prefixWord ++ tailWord_4546927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4546927).length < 2 ^ (prefixWord ++ tailWord_4546927).sum := by decide
  have hdescent : baseEnd_4546927 < baseStart_4546927 := by decide
  rcases family_descends (prefixWord ++ tailWord_4546927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4546988 : List Nat := [2, 2, 1, 1, 1, 1, 3, 6, 2, 2, 2]
def baseStart_4546988 : Nat := 118140960795 + 4546988 * 2 ^ 59
def prefixEnd_4546988 : Nat := 4983230072969 + 3 ^ 40 * 4546988 * 2
def baseEnd_4546988 : Nat := 2334790374225961122238789

theorem tailTrace_4546988 : CollatzResearch.WordTrace tailWord_4546988 prefixEnd_4546988 2334790374225961122238789 := by
  unfold tailWord_4546988
  simp only [CollatzResearch.WordTrace]
  refine ⟨82921138425523257285056809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110561517900697676380075745 82921138425523257285056809)
  ·
    refine ⟨62190853819142442963792607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82921138425523257285056809 62190853819142442963792607)
    ·
      refine ⟨93286280728713664445688911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62190853819142442963792607 93286280728713664445688911)
      ·
        refine ⟨139929421093070496668533367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93286280728713664445688911 139929421093070496668533367)
        ·
          refine ⟨209894131639605745002800051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139929421093070496668533367 209894131639605745002800051)
          ·
            refine ⟨314841197459408617504200077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 209894131639605745002800051 314841197459408617504200077)
            ·
              refine ⟨118065449047278231564075029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 314841197459408617504200077 118065449047278231564075029)
              ·
                refine ⟨5534317924091167104566017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 118065449047278231564075029 5534317924091167104566017)
                ·
                  refine ⟨4150738443068375328424513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5534317924091167104566017 4150738443068375328424513)
                  ·
                    refine ⟨3113053832301281496318385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4150738443068375328424513 3113053832301281496318385)
                    ·
                      refine ⟨2334790374225961122238789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3113053832301281496318385 2334790374225961122238789)
                      ·
                        rfl

theorem cell23_4546988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 2, 2].length) (baseStart_4546988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4546988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4546988 prefixEnd_4546988 := by exact prefixLift 4546988
  have htrace : WordTrace (prefixWord ++ tailWord_4546988) baseStart_4546988 baseEnd_4546988 := by
    simpa [prefixWord, tailWord_4546988, baseEnd_4546988] using wordTrace_append hprefix tailTrace_4546988
  have hstable : (prefixWord ++ tailWord_4546988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4546988).length < 2 ^ (prefixWord ++ tailWord_4546988).sum := by decide
  have hdescent : baseEnd_4546988 < baseStart_4546988 := by decide
  rcases family_descends (prefixWord ++ tailWord_4546988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4547005 : List Nat := [1, 4, 1, 2, 2, 3, 1, 3, 2, 2, 2]
def baseStart_4547005 : Nat := 118140960795 + 4547005 * 2 ^ 59
def prefixEnd_4547005 : Nat := 4983230072969 + 3 ^ 40 * 4547005 * 2
def baseEnd_4547005 : Nat := 2334799103397087555726211

theorem tailTrace_4547005 : CollatzResearch.WordTrace tailWord_4547005 prefixEnd_4547005 2334799103397087555726211 := by
  unfold tailWord_4547005
  simp only [CollatzResearch.WordTrace]
  refine ⟨165842896891984926473482469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110561931261323284315654979 165842896891984926473482469)
  ·
    refine ⟨31095543167247173713777963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 165842896891984926473482469 31095543167247173713777963)
    ·
      refine ⟨46643314750870760570666945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31095543167247173713777963 46643314750870760570666945)
      ·
        refine ⟨34982486063153070428000209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46643314750870760570666945 34982486063153070428000209)
        ·
          refine ⟨26236864547364802821000157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34982486063153070428000209 26236864547364802821000157)
          ·
            refine ⟨9838824205261801057875059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26236864547364802821000157 9838824205261801057875059)
            ·
              refine ⟨14758236307892701586812589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9838824205261801057875059 14758236307892701586812589)
              ·
                refine ⟨5534338615459763095054721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14758236307892701586812589 5534338615459763095054721)
                ·
                  refine ⟨4150753961594822321291041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5534338615459763095054721 4150753961594822321291041)
                  ·
                    refine ⟨3113065471196116740968281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4150753961594822321291041 3113065471196116740968281)
                    ·
                      refine ⟨2334799103397087555726211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3113065471196116740968281 2334799103397087555726211)
                      ·
                        rfl

theorem cell23_4547005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 3, 2, 2, 2].length) (baseStart_4547005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4547005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4547005 prefixEnd_4547005 := by exact prefixLift 4547005
  have htrace : WordTrace (prefixWord ++ tailWord_4547005) baseStart_4547005 baseEnd_4547005 := by
    simpa [prefixWord, tailWord_4547005, baseEnd_4547005] using wordTrace_append hprefix tailTrace_4547005
  have hstable : (prefixWord ++ tailWord_4547005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4547005).length < 2 ^ (prefixWord ++ tailWord_4547005).sum := by decide
  have hdescent : baseEnd_4547005 < baseStart_4547005 := by decide
  rcases family_descends (prefixWord ++ tailWord_4547005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4547034 : List Nat := [3, 1, 1, 2, 3, 1, 1, 1, 3, 2, 5]
def baseStart_4547034 : Nat := 118140960795 + 4547034 * 2 ^ 59
def prefixEnd_4547034 : Nat := 4983230072969 + 3 ^ 40 * 4547034 * 2
def baseEnd_4547034 : Nat := 2334813994336067942263577

theorem tailTrace_4547034 : CollatzResearch.WordTrace tailWord_4547034 prefixEnd_4547034 2334813994336067942263577 := by
  unfold tailWord_4547034
  simp only [CollatzResearch.WordTrace]
  refine ⟨41460988652219966106572039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110562636405919909617525437 41460988652219966106572039)
  ·
    refine ⟨62191482978329949159858059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41460988652219966106572039 62191482978329949159858059)
    ·
      refine ⟨93287224467494923739787089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62191482978329949159858059 93287224467494923739787089)
      ·
        refine ⟨69965418350621192804840317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93287224467494923739787089 69965418350621192804840317)
        ·
          refine ⟨26237031881482947301815119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69965418350621192804840317 26237031881482947301815119)
          ·
            refine ⟨39355547822224420952722679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26237031881482947301815119 39355547822224420952722679)
            ·
              refine ⟨59033321733336631429084019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39355547822224420952722679 59033321733336631429084019)
              ·
                refine ⟨88549982600004947143626029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59033321733336631429084019 88549982600004947143626029)
                ·
                  refine ⟨33206243475001855178859761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 88549982600004947143626029 33206243475001855178859761)
                  ·
                    refine ⟨24904682606251391384144821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33206243475001855178859761 24904682606251391384144821)
                    ·
                      refine ⟨2334813994336067942263577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24904682606251391384144821 2334813994336067942263577)
                      ·
                        rfl

theorem cell23_4547034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 3, 2, 5].length) (baseStart_4547034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4547034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4547034 prefixEnd_4547034 := by exact prefixLift 4547034
  have htrace : WordTrace (prefixWord ++ tailWord_4547034) baseStart_4547034 baseEnd_4547034 := by
    simpa [prefixWord, tailWord_4547034, baseEnd_4547034] using wordTrace_append hprefix tailTrace_4547034
  have hstable : (prefixWord ++ tailWord_4547034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4547034).length < 2 ^ (prefixWord ++ tailWord_4547034).sum := by decide
  have hdescent : baseEnd_4547034 < baseStart_4547034 := by decide
  rcases family_descends (prefixWord ++ tailWord_4547034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4547044 : List Nat := [2, 3, 1, 1, 1, 1, 1, 1, 5, 3, 4]
def baseStart_4547044 : Nat := 118140960795 + 4547044 * 2 ^ 59
def prefixEnd_4547044 : Nat := 4983230072969 + 3 ^ 40 * 4547044 * 2
def baseEnd_4547044 : Nat := 2334819129142612903138531

theorem tailTrace_4547044 : CollatzResearch.WordTrace tailWord_4547044 prefixEnd_4547044 2334819129142612903138531 := by
  unfold tailWord_4547044
  simp only [CollatzResearch.WordTrace]
  refine ⟨82922159669421818067076093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110562879559229090756101457 82922159669421818067076093)
  ·
    refine ⟨31095809876033181775153535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82922159669421818067076093 31095809876033181775153535)
    ·
      refine ⟨46643714814049772662730303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31095809876033181775153535 46643714814049772662730303)
      ·
        refine ⟨69965572221074658994095455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46643714814049772662730303 69965572221074658994095455)
        ·
          refine ⟨104948358331611988491143183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69965572221074658994095455 104948358331611988491143183)
          ·
            refine ⟨157422537497417982736714775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104948358331611988491143183 157422537497417982736714775)
            ·
              refine ⟨236133806246126974105072163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157422537497417982736714775 236133806246126974105072163)
              ·
                refine ⟨354200709369190461157608245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 236133806246126974105072163 354200709369190461157608245)
                ·
                  refine ⟨33206316503361605733525773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 354200709369190461157608245 33206316503361605733525773)
                  ·
                    refine ⟨12452368688760602150072165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33206316503361605733525773 12452368688760602150072165)
                    ·
                      refine ⟨2334819129142612903138531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12452368688760602150072165 2334819129142612903138531)
                      ·
                        rfl

theorem cell23_4547044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 5, 3, 4].length) (baseStart_4547044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4547044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4547044 prefixEnd_4547044 := by exact prefixLift 4547044
  have htrace : WordTrace (prefixWord ++ tailWord_4547044) baseStart_4547044 baseEnd_4547044 := by
    simpa [prefixWord, tailWord_4547044, baseEnd_4547044] using wordTrace_append hprefix tailTrace_4547044
  have hstable : (prefixWord ++ tailWord_4547044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4547044).length < 2 ^ (prefixWord ++ tailWord_4547044).sum := by decide
  have hdescent : baseEnd_4547044 < baseStart_4547044 := by decide
  rcases family_descends (prefixWord ++ tailWord_4547044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4547071 : List Nat := [1, 1, 2, 2, 1, 2, 5, 2, 3, 4]
def baseStart_4547071 : Nat := 118140960795 + 4547071 * 2 ^ 59
def prefixEnd_4547071 : Nat := 4983230072969 + 3 ^ 40 * 4547071 * 2
def baseEnd_4547071 : Nat := 778277664373428099166969

theorem tailTrace_4547071 : CollatzResearch.WordTrace tailWord_4547071 prefixEnd_4547071 778277664373428099166969 := by
  unfold tailWord_4547071
  simp only [CollatzResearch.WordTrace]
  refine ⟨165845304109745819745385067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110563536073163879830256711 165845304109745819745385067)
  ·
    refine ⟨248767956164618729618077601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165845304109745819745385067 248767956164618729618077601)
    ·
      refine ⟨186575967123464047213558201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 248767956164618729618077601 186575967123464047213558201)
      ·
        refine ⟨139931975342598035410168651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186575967123464047213558201 139931975342598035410168651)
        ·
          refine ⟨209897963013897053115252977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139931975342598035410168651 209897963013897053115252977)
          ·
            refine ⟨157423472260422789836439733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 209897963013897053115252977 157423472260422789836439733)
            ·
              refine ⟨14758450524414636547166225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 157423472260422789836439733 14758450524414636547166225)
              ·
                refine ⟨11068837893310977410374669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14758450524414636547166225 11068837893310977410374669)
                ·
                  refine ⟨4150814209991616528890501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11068837893310977410374669 4150814209991616528890501)
                  ·
                    refine ⟨778277664373428099166969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4150814209991616528890501 778277664373428099166969)
                    ·
                      rfl

theorem cell23_4547071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 2, 3, 4].length) (baseStart_4547071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4547071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4547071 prefixEnd_4547071 := by exact prefixLift 4547071
  have htrace : WordTrace (prefixWord ++ tailWord_4547071) baseStart_4547071 baseEnd_4547071 := by
    simpa [prefixWord, tailWord_4547071, baseEnd_4547071] using wordTrace_append hprefix tailTrace_4547071
  have hstable : (prefixWord ++ tailWord_4547071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4547071).length < 2 ^ (prefixWord ++ tailWord_4547071).sum := by decide
  have hdescent : baseEnd_4547071 < baseStart_4547071 := by decide
  rcases family_descends (prefixWord ++ tailWord_4547071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4547081 : List Nat := [1, 2, 1, 1, 3, 1, 2, 5, 2, 2, 3]
def baseStart_4547081 : Nat := 118140960795 + 4547081 * 2 ^ 59
def prefixEnd_4547081 : Nat := 4983230072969 + 3 ^ 40 * 4547081 * 2
def baseEnd_4547081 : Nat := 2334838127926829258375861

theorem tailTrace_4547081 : CollatzResearch.WordTrace tailWord_4547081 prefixEnd_4547081 2334838127926829258375861 := by
  unfold tailWord_4547081
  simp only [CollatzResearch.WordTrace]
  refine ⟨165845668839709591453249097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110563779226473060968832731 165845668839709591453249097)
  ·
    refine ⟨124384251629782193589936823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165845668839709591453249097 124384251629782193589936823)
    ·
      refine ⟨186576377444673290384905235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124384251629782193589936823 186576377444673290384905235)
      ·
        refine ⟨279864566167009935577357853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186576377444673290384905235 279864566167009935577357853)
        ·
          refine ⟨104949212312628725841509195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 279864566167009935577357853 104949212312628725841509195)
          ·
            refine ⟨157423818468943088762263793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104949212312628725841509195 157423818468943088762263793)
            ·
              refine ⟨118067863851707316571697845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 157423818468943088762263793 118067863851707316571697845)
              ·
                refine ⟨11068862236097560928596673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 118067863851707316571697845 11068862236097560928596673)
                ·
                  refine ⟨8301646677073170696447505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11068862236097560928596673 8301646677073170696447505)
                  ·
                    refine ⟨6226235007804878022335629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8301646677073170696447505 6226235007804878022335629)
                    ·
                      refine ⟨2334838127926829258375861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6226235007804878022335629 2334838127926829258375861)
                      ·
                        rfl

theorem cell23_4547081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 5, 2, 2, 3].length) (baseStart_4547081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4547081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4547081 prefixEnd_4547081 := by exact prefixLift 4547081
  have htrace : WordTrace (prefixWord ++ tailWord_4547081) baseStart_4547081 baseEnd_4547081 := by
    simpa [prefixWord, tailWord_4547081, baseEnd_4547081] using wordTrace_append hprefix tailTrace_4547081
  have hstable : (prefixWord ++ tailWord_4547081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4547081).length < 2 ^ (prefixWord ++ tailWord_4547081).sum := by decide
  have hdescent : baseEnd_4547081 < baseStart_4547081 := by decide
  rcases family_descends (prefixWord ++ tailWord_4547081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4547101 : List Nat := [1, 4, 2, 2, 1, 3, 1, 1, 8]
def baseStart_4547101 : Nat := 118140960795 + 4547101 * 2 ^ 59
def prefixEnd_4547101 : Nat := 4983230072969 + 3 ^ 40 * 4547101 * 2
def baseEnd_4547101 : Nat := 259427599726657686680641

theorem tailTrace_4547101 : CollatzResearch.WordTrace tailWord_4547101 prefixEnd_4547101 259427599726657686680641 := by
  unfold tailWord_4547101
  simp only [CollatzResearch.WordTrace]
  refine ⟨165846398299637134868977157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110564265533091423245984771 165846398299637134868977157)
  ·
    refine ⟨31096199681181962787933217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 165846398299637134868977157 31096199681181962787933217)
    ·
      refine ⟨23322149760886472090949913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31096199681181962787933217 23322149760886472090949913)
      ·
        refine ⟨17491612320664854068212435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23322149760886472090949913 17491612320664854068212435)
        ·
          refine ⟨26237418480997281102318653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17491612320664854068212435 26237418480997281102318653)
          ·
            refine ⟨9839031930373980413369495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26237418480997281102318653 9839031930373980413369495)
            ·
              refine ⟨14758547895560970620054243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9839031930373980413369495 14758547895560970620054243)
              ·
                refine ⟨22137821843341455930081365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14758547895560970620054243 22137821843341455930081365)
                ·
                  refine ⟨259427599726657686680641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22137821843341455930081365 259427599726657686680641)
                  ·
                    rfl

theorem cell23_4547101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 1, 8].length) (baseStart_4547101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4547101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4547101 prefixEnd_4547101 := by exact prefixLift 4547101
  have htrace : WordTrace (prefixWord ++ tailWord_4547101) baseStart_4547101 baseEnd_4547101 := by
    simpa [prefixWord, tailWord_4547101, baseEnd_4547101] using wordTrace_append hprefix tailTrace_4547101
  have hstable : (prefixWord ++ tailWord_4547101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4547101).length < 2 ^ (prefixWord ++ tailWord_4547101).sum := by decide
  have hdescent : baseEnd_4547101 < baseStart_4547101 := by decide
  rcases family_descends (prefixWord ++ tailWord_4547101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4547128 : List Nat := [2, 1, 2, 1, 4, 1, 1, 4, 3, 1, 3]
def baseStart_4547128 : Nat := 118140960795 + 4547128 * 2 ^ 59
def prefixEnd_4547128 : Nat := 4983230072969 + 3 ^ 40 * 4547128 * 2
def baseEnd_4547128 : Nat := 2334862261517590574488145

theorem tailTrace_4547128 : CollatzResearch.WordTrace tailWord_4547128 prefixEnd_4547128 2334862261517590574488145 := by
  unfold tailWord_4547128
  simp only [CollatzResearch.WordTrace]
  refine ⟨82923691535269659240105019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110564922047026212320140025 82923691535269659240105019)
  ·
    refine ⟨124385537302904488860157529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82923691535269659240105019 124385537302904488860157529)
    ·
      refine ⟨93289152977178366645118147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124385537302904488860157529 93289152977178366645118147)
      ·
        refine ⟨139933729465767549967677221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93289152977178366645118147 139933729465767549967677221)
        ·
          refine ⟨26237574274831415618939479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 139933729465767549967677221 26237574274831415618939479)
          ·
            refine ⟨39356361412247123428409219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26237574274831415618939479 39356361412247123428409219)
            ·
              refine ⟨59034542118370685142613829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39356361412247123428409219 59034542118370685142613829)
              ·
                refine ⟨11068976647194503464240093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59034542118370685142613829 11068976647194503464240093)
                ·
                  refine ⟨4150866242697938799090035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11068976647194503464240093 4150866242697938799090035)
                  ·
                    refine ⟨6226299364046908198635053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4150866242697938799090035 6226299364046908198635053)
                    ·
                      refine ⟨2334862261517590574488145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6226299364046908198635053 2334862261517590574488145)
                      ·
                        rfl

theorem cell23_4547128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 4, 3, 1, 3].length) (baseStart_4547128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4547128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4547128 prefixEnd_4547128 := by exact prefixLift 4547128
  have htrace : WordTrace (prefixWord ++ tailWord_4547128) baseStart_4547128 baseEnd_4547128 := by
    simpa [prefixWord, tailWord_4547128, baseEnd_4547128] using wordTrace_append hprefix tailTrace_4547128
  have hstable : (prefixWord ++ tailWord_4547128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4547128).length < 2 ^ (prefixWord ++ tailWord_4547128).sum := by decide
  have hdescent : baseEnd_4547128 < baseStart_4547128 := by decide
  rcases family_descends (prefixWord ++ tailWord_4547128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4547171 : List Nat := [1, 1, 1, 5, 1, 2, 1, 4, 1, 1, 5]
def baseStart_4547171 : Nat := 118140960795 + 4547171 * 2 ^ 59
def prefixEnd_4547171 : Nat := 4983230072969 + 3 ^ 40 * 4547171 * 2
def baseEnd_4547171 : Nat := 2334884341185733906250447

theorem tailTrace_4547171 : CollatzResearch.WordTrace tailWord_4547171 prefixEnd_4547171 2334884341185733906250447 := by
  unfold tailWord_4547171
  simp only [CollatzResearch.WordTrace]
  refine ⟨165848951409383536824025367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110565967606255691216016911 165848951409383536824025367)
  ·
    refine ⟨248773427114075305236038051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165848951409383536824025367 248773427114075305236038051)
    ·
      refine ⟨373160140671112957854057077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248773427114075305236038051 373160140671112957854057077)
      ·
        refine ⟨34983763187916839798817851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 373160140671112957854057077 34983763187916839798817851)
        ·
          refine ⟨52475644781875259698226777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34983763187916839798817851 52475644781875259698226777)
          ·
            refine ⟨39356733586406444773670083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52475644781875259698226777 39356733586406444773670083)
            ·
              refine ⟨59035100379609667160505125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39356733586406444773670083 59035100379609667160505125)
              ·
                refine ⟨11069081321176812592594711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59035100379609667160505125 11069081321176812592594711)
                ·
                  refine ⟨16603621981765218888892067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11069081321176812592594711 16603621981765218888892067)
                  ·
                    refine ⟨24905432972647828333338101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16603621981765218888892067 24905432972647828333338101)
                    ·
                      refine ⟨2334884341185733906250447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24905432972647828333338101 2334884341185733906250447)
                      ·
                        rfl

theorem cell23_4547171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_4547171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4547171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4547171 prefixEnd_4547171 := by exact prefixLift 4547171
  have htrace : WordTrace (prefixWord ++ tailWord_4547171) baseStart_4547171 baseEnd_4547171 := by
    simpa [prefixWord, tailWord_4547171, baseEnd_4547171] using wordTrace_append hprefix tailTrace_4547171
  have hstable : (prefixWord ++ tailWord_4547171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4547171).length < 2 ^ (prefixWord ++ tailWord_4547171).sum := by decide
  have hdescent : baseEnd_4547171 < baseStart_4547171 := by decide
  rcases family_descends (prefixWord ++ tailWord_4547171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4547242 : List Nat := [3, 1, 5, 2, 1, 1, 3, 7]
def baseStart_4547242 : Nat := 118140960795 + 4547242 * 2 ^ 59
def prefixEnd_4547242 : Nat := 4983230072969 + 3 ^ 40 * 4547242 * 2
def baseEnd_4547242 : Nat := 86478548085637152906023

theorem tailTrace_4547242 : CollatzResearch.WordTrace tailWord_4547242 prefixEnd_4547242 86478548085637152906023 := by
  unfold tailWord_4547242
  simp only [CollatzResearch.WordTrace]
  refine ⟨41462885248031578987464995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110567693994750877299906653 41462885248031578987464995)
  ·
    refine ⟨62194327872047368481197493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41462885248031578987464995 62194327872047368481197493)
    ·
      refine ⟨5830718238004440795112265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 62194327872047368481197493 5830718238004440795112265)
      ·
        refine ⟨4373038678503330596334199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5830718238004440795112265 4373038678503330596334199)
        ·
          refine ⟨6559558017754995894501299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4373038678503330596334199 6559558017754995894501299)
          ·
            refine ⟨9839337026632493841751949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6559558017754995894501299 9839337026632493841751949)
            ·
              refine ⟨3689751384987185190656981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9839337026632493841751949 3689751384987185190656981)
              ·
                refine ⟨86478548085637152906023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3689751384987185190656981 86478548085637152906023)
                ·
                  rfl

theorem cell23_4547242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 3, 7].length) (baseStart_4547242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4547242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4547242 prefixEnd_4547242 := by exact prefixLift 4547242
  have htrace : WordTrace (prefixWord ++ tailWord_4547242) baseStart_4547242 baseEnd_4547242 := by
    simpa [prefixWord, tailWord_4547242, baseEnd_4547242] using wordTrace_append hprefix tailTrace_4547242
  have hstable : (prefixWord ++ tailWord_4547242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4547242).length < 2 ^ (prefixWord ++ tailWord_4547242).sum := by decide
  have hdescent : baseEnd_4547242 < baseStart_4547242 := by decide
  rcases family_descends (prefixWord ++ tailWord_4547242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4547262 : List Nat := [4, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2]
def baseStart_4547262 : Nat := 118140960795 + 4547262 * 2 ^ 59
def prefixEnd_4547262 : Nat := 4983230072969 + 3 ^ 40 * 4547262 * 2
def baseEnd_4547262 : Nat := 2334931067925293050212529

theorem tailTrace_4547262 : CollatzResearch.WordTrace tailWord_4547262 prefixEnd_4547262 2334931067925293050212529 := by
  unfold tailWord_4547262
  simp only [CollatzResearch.WordTrace]
  refine ⟨20731533806506732420698505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110568180301369239577058693 20731533806506732420698505)
  ·
    refine ⟨15548650354880049315523879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20731533806506732420698505 15548650354880049315523879)
    ·
      refine ⟨23322975532320073973285819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15548650354880049315523879 23322975532320073973285819)
      ·
        refine ⟨34984463298480110959928729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23322975532320073973285819 34984463298480110959928729)
        ·
          refine ⟨26238347473860083219946547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34984463298480110959928729 26238347473860083219946547)
          ·
            refine ⟨39357521210790124829919821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26238347473860083219946547 39357521210790124829919821)
            ·
              refine ⟨14759070454046296811219933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39357521210790124829919821 14759070454046296811219933)
              ·
                refine ⟨5534651420267361304207475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14759070454046296811219933 5534651420267361304207475)
                ·
                  refine ⟨8301977130401041956311213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5534651420267361304207475 8301977130401041956311213)
                  ·
                    refine ⟨3113241423900390733616705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8301977130401041956311213 3113241423900390733616705)
                    ·
                      refine ⟨2334931067925293050212529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3113241423900390733616705 2334931067925293050212529)
                      ·
                        rfl

theorem cell23_4547262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2].length) (baseStart_4547262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4547262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4547262 prefixEnd_4547262 := by exact prefixLift 4547262
  have htrace : WordTrace (prefixWord ++ tailWord_4547262) baseStart_4547262 baseEnd_4547262 := by
    simpa [prefixWord, tailWord_4547262, baseEnd_4547262] using wordTrace_append hprefix tailTrace_4547262
  have hstable : (prefixWord ++ tailWord_4547262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4547262).length < 2 ^ (prefixWord ++ tailWord_4547262).sum := by decide
  have hdescent : baseEnd_4547262 < baseStart_4547262 := by decide
  rcases family_descends (prefixWord ++ tailWord_4547262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4547268 : List Nat := [2, 3, 3, 1, 1, 2, 1, 2, 2, 6]
def baseStart_4547268 : Nat := 118140960795 + 4547268 * 2 ^ 59
def prefixEnd_4547268 : Nat := 4983230072969 + 3 ^ 40 * 4547268 * 2
def baseEnd_4547268 : Nat := 778311382936406675579167

theorem tailTrace_4547268 : CollatzResearch.WordTrace tailWord_4547268 prefixEnd_4547268 778311382936406675579167 := by
  unfold tailWord_4547268
  simp only [CollatzResearch.WordTrace]
  refine ⟨82926244645016061195153229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110568326193354748260204305 82926244645016061195153229)
  ·
    refine ⟨31097341741881022948182461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82926244645016061195153229 31097341741881022948182461)
    ·
      refine ⟨11661503153205383605568423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31097341741881022948182461 11661503153205383605568423)
      ·
        refine ⟨17492254729808075408352635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11661503153205383605568423 17492254729808075408352635)
        ·
          refine ⟨26238382094712113112528953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17492254729808075408352635 26238382094712113112528953)
          ·
            refine ⟨19678786571034084834396715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26238382094712113112528953 19678786571034084834396715)
            ·
              refine ⟨29518179856551127251595073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19678786571034084834396715 29518179856551127251595073)
              ·
                refine ⟨22138634892413345438696305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29518179856551127251595073 22138634892413345438696305)
                ·
                  refine ⟨16603976169310009079022229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22138634892413345438696305 16603976169310009079022229)
                  ·
                    refine ⟨778311382936406675579167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16603976169310009079022229 778311382936406675579167)
                    ·
                      rfl

theorem cell23_4547268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_4547268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4547268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4547268 prefixEnd_4547268 := by exact prefixLift 4547268
  have htrace : WordTrace (prefixWord ++ tailWord_4547268) baseStart_4547268 baseEnd_4547268 := by
    simpa [prefixWord, tailWord_4547268, baseEnd_4547268] using wordTrace_append hprefix tailTrace_4547268
  have hstable : (prefixWord ++ tailWord_4547268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4547268).length < 2 ^ (prefixWord ++ tailWord_4547268).sum := by decide
  have hdescent : baseEnd_4547268 < baseStart_4547268 := by decide
  rcases family_descends (prefixWord ++ tailWord_4547268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4547288 : List Nat := [2, 1, 2, 2, 3, 2, 2, 1, 2, 2, 4]
def baseStart_4547288 : Nat := 118140960795 + 4547288 * 2 ^ 59
def prefixEnd_4547288 : Nat := 4983230072969 + 3 ^ 40 * 4547288 * 2
def baseEnd_4547288 : Nat := 2334944418422309948487409

theorem tailTrace_4547288 : CollatzResearch.WordTrace tailWord_4547288 prefixEnd_4547288 2334944418422309948487409 := by
  unfold tailWord_4547288
  simp only [CollatzResearch.WordTrace]
  refine ⟨82926609374979832903017259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110568812499973110537356345 82926609374979832903017259)
  ·
    refine ⟨124389914062469749354525889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82926609374979832903017259 124389914062469749354525889)
    ·
      refine ⟨93292435546852312015894417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124389914062469749354525889 93292435546852312015894417)
      ·
        refine ⟨69969326660139234011920813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93292435546852312015894417 69969326660139234011920813)
        ·
          refine ⟨26238497497552212754470305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69969326660139234011920813 26238497497552212754470305)
          ·
            refine ⟨19678873123164159565852729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26238497497552212754470305 19678873123164159565852729)
            ·
              refine ⟨14759154842373119674389547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19678873123164159565852729 14759154842373119674389547)
              ·
                refine ⟨22138732263559679511584321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14759154842373119674389547 22138732263559679511584321)
                ·
                  refine ⟨16604049197669759633688241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22138732263559679511584321 16604049197669759633688241)
                  ·
                    refine ⟨12453036898252319725266181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16604049197669759633688241 12453036898252319725266181)
                    ·
                      refine ⟨2334944418422309948487409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12453036898252319725266181 2334944418422309948487409)
                      ·
                        rfl

theorem cell23_4547288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 1, 2, 2, 4].length) (baseStart_4547288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4547288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4547288 prefixEnd_4547288 := by exact prefixLift 4547288
  have htrace : WordTrace (prefixWord ++ tailWord_4547288) baseStart_4547288 baseEnd_4547288 := by
    simpa [prefixWord, tailWord_4547288, baseEnd_4547288] using wordTrace_append hprefix tailTrace_4547288
  have hstable : (prefixWord ++ tailWord_4547288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4547288).length < 2 ^ (prefixWord ++ tailWord_4547288).sum := by decide
  have hdescent : baseEnd_4547288 < baseStart_4547288 := by decide
  rcases family_descends (prefixWord ++ tailWord_4547288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4547321 : List Nat := [1, 2, 1, 3, 1, 1, 1, 2, 3, 1, 7]
def baseStart_4547321 : Nat := 118140960795 + 4547321 * 2 ^ 59
def prefixEnd_4547321 : Nat := 4983230072969 + 3 ^ 40 * 4547321 * 2
def baseEnd_4547321 : Nat := 2334961363283908319374757

theorem tailTrace_4547321 : CollatzResearch.WordTrace tailWord_4547321 prefixEnd_4547321 2334961363283908319374757 := by
  unfold tailWord_4547321
  simp only [CollatzResearch.WordTrace]
  refine ⟨165854422358840112441985817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110569614905893408294657211 165854422358840112441985817)
  ·
    refine ⟨124390816769130084331489363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165854422358840112441985817 124390816769130084331489363)
    ·
      refine ⟨186586225153695126497234045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124390816769130084331489363 186586225153695126497234045)
      ·
        refine ⟨69969834432635672436462767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 186586225153695126497234045 69969834432635672436462767)
        ·
          refine ⟨104954751648953508654694151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69969834432635672436462767 104954751648953508654694151)
          ·
            refine ⟨157432127473430262982041227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104954751648953508654694151 157432127473430262982041227)
            ·
              refine ⟨236148191210145394473061841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157432127473430262982041227 236148191210145394473061841)
              ·
                refine ⟨177111143407609045854796381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 236148191210145394473061841 177111143407609045854796381)
                ·
                  refine ⟨66416678777853392195548643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 177111143407609045854796381 66416678777853392195548643)
                  ·
                    refine ⟨99625018166780088293322965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 66416678777853392195548643 99625018166780088293322965)
                    ·
                      refine ⟨2334961363283908319374757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 99625018166780088293322965 2334961363283908319374757)
                      ·
                        rfl

theorem cell23_4547321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 1, 7].length) (baseStart_4547321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4547321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4547321 prefixEnd_4547321 := by exact prefixLift 4547321
  have htrace : WordTrace (prefixWord ++ tailWord_4547321) baseStart_4547321 baseEnd_4547321 := by
    simpa [prefixWord, tailWord_4547321, baseEnd_4547321] using wordTrace_append hprefix tailTrace_4547321
  have hstable : (prefixWord ++ tailWord_4547321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4547321).length < 2 ^ (prefixWord ++ tailWord_4547321).sum := by decide
  have hdescent : baseEnd_4547321 < baseStart_4547321 := by decide
  rcases family_descends (prefixWord ++ tailWord_4547321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4547332 : List Nat := [2, 3, 2, 2, 1, 1, 5, 2, 5]
def baseStart_4547332 : Nat := 118140960795 + 4547332 * 2 ^ 59
def prefixEnd_4547332 : Nat := 4983230072969 + 3 ^ 40 * 4547332 * 2
def baseEnd_4547332 : Nat := 259440779063456419593023

theorem tailTrace_4547332 : CollatzResearch.WordTrace tailWord_4547332 prefixEnd_4547332 259440779063456419593023 := by
  unfold tailWord_4547332
  simp only [CollatzResearch.WordTrace]
  refine ⟨82927411780900130660318125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110569882374533507547090833 82927411780900130660318125)
  ·
    refine ⟨31097779417837548997619297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82927411780900130660318125 31097779417837548997619297)
    ·
      refine ⟨23323334563378161748214473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31097779417837548997619297 23323334563378161748214473)
      ·
        refine ⟨17492500922533621311160855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23323334563378161748214473 17492500922533621311160855)
        ·
          refine ⟨26238751383800431966741283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17492500922533621311160855 26238751383800431966741283)
          ·
            refine ⟨39358127075700647950111925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26238751383800431966741283 39358127075700647950111925)
            ·
              refine ⟨3689824413346935745322993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39358127075700647950111925 3689824413346935745322993)
              ·
                refine ⟨2767368310010201808992245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3689824413346935745322993 2767368310010201808992245)
                ·
                  refine ⟨259440779063456419593023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2767368310010201808992245 259440779063456419593023)
                  ·
                    rfl

theorem cell23_4547332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 5, 2, 5].length) (baseStart_4547332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4547332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4547332 prefixEnd_4547332 := by exact prefixLift 4547332
  have htrace : WordTrace (prefixWord ++ tailWord_4547332) baseStart_4547332 baseEnd_4547332 := by
    simpa [prefixWord, tailWord_4547332, baseEnd_4547332] using wordTrace_append hprefix tailTrace_4547332
  have hstable : (prefixWord ++ tailWord_4547332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4547332).length < 2 ^ (prefixWord ++ tailWord_4547332).sum := by decide
  have hdescent : baseEnd_4547332 < baseStart_4547332 := by decide
  rcases family_descends (prefixWord ++ tailWord_4547332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4547338 : List Nat := [3, 1, 2, 2, 1, 2, 3, 1, 1, 2, 5]
def baseStart_4547338 : Nat := 118140960795 + 4547338 * 2 ^ 59
def prefixEnd_4547338 : Nat := 4983230072969 + 3 ^ 40 * 4547338 * 2
def baseEnd_4547338 : Nat := 2334970092455034752862179

theorem tailTrace_4547338 : CollatzResearch.WordTrace tailWord_4547338 prefixEnd_4547338 2334970092455034752862179 := by
  unfold tailWord_4547338
  simp only [CollatzResearch.WordTrace]
  refine ⟨41463760599944631086338667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110570028266519016230236445 41463760599944631086338667)
  ·
    refine ⟨62195640899916946629508001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41463760599944631086338667 62195640899916946629508001)
    ·
      refine ⟨46646730674937709972131001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62195640899916946629508001 46646730674937709972131001)
      ·
        refine ⟨34985048006203282479098251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46646730674937709972131001 34985048006203282479098251)
        ·
          refine ⟨52477572009304923718647377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34985048006203282479098251 52477572009304923718647377)
          ·
            refine ⟨39358179006978692788985533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52477572009304923718647377 39358179006978692788985533)
            ·
              refine ⟨14759317127617009795869575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39358179006978692788985533 14759317127617009795869575)
              ·
                refine ⟨22138975691425514693804363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14759317127617009795869575 22138975691425514693804363)
                ·
                  refine ⟨33208463537138272040706545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22138975691425514693804363 33208463537138272040706545)
                  ·
                    refine ⟨24906347652853704030529909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33208463537138272040706545 24906347652853704030529909)
                    ·
                      refine ⟨2334970092455034752862179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24906347652853704030529909 2334970092455034752862179)
                      ·
                        rfl

theorem cell23_4547338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_4547338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4547338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4547338 prefixEnd_4547338 := by exact prefixLift 4547338
  have htrace : WordTrace (prefixWord ++ tailWord_4547338) baseStart_4547338 baseEnd_4547338 := by
    simpa [prefixWord, tailWord_4547338, baseEnd_4547338] using wordTrace_append hprefix tailTrace_4547338
  have hstable : (prefixWord ++ tailWord_4547338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4547338).length < 2 ^ (prefixWord ++ tailWord_4547338).sum := by decide
  have hdescent : baseEnd_4547338 < baseStart_4547338 := by decide
  rcases family_descends (prefixWord ++ tailWord_4547338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4547365 : List Nat := [1, 3, 1, 2, 3, 1, 4, 1, 2, 1, 4]
def baseStart_4547365 : Nat := 118140960795 + 4547365 * 2 ^ 59
def prefixEnd_4547365 : Nat := 4983230072969 + 3 ^ 40 * 4547365 * 2
def baseEnd_4547365 : Nat := 2334983956432706147224555

theorem tailTrace_4547365 : CollatzResearch.WordTrace tailWord_4547365 prefixEnd_4547365 2334983956432706147224555 := by
  unfold tailWord_4547365
  simp only [CollatzResearch.WordTrace]
  refine ⟨165856027170680707956587549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110570684780453805304391699 165856027170680707956587549)
  ·
    refine ⟨62196010189005265483720331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165856027170680707956587549 62196010189005265483720331)
    ·
      refine ⟨93294015283507898225580497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62196010189005265483720331 93294015283507898225580497)
      ·
        refine ⟨69970511462630923669185373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93294015283507898225580497 69970511462630923669185373)
        ·
          refine ⟨26238941798486596375944515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69970511462630923669185373 26238941798486596375944515)
          ·
            refine ⟨39358412697729894563916773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26238941798486596375944515 39358412697729894563916773)
            ·
              refine ⟨7379702380824355230734395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39358412697729894563916773 7379702380824355230734395)
              ·
                refine ⟨11069553571236532846101593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7379702380824355230734395 11069553571236532846101593)
                ·
                  refine ⟨8302165178427399634576195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11069553571236532846101593 8302165178427399634576195)
                  ·
                    refine ⟨12453247767641099451864293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8302165178427399634576195 12453247767641099451864293)
                    ·
                      refine ⟨2334983956432706147224555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12453247767641099451864293 2334983956432706147224555)
                      ·
                        rfl

theorem cell23_4547365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 1, 2, 1, 4].length) (baseStart_4547365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4547365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4547365 prefixEnd_4547365 := by exact prefixLift 4547365
  have htrace : WordTrace (prefixWord ++ tailWord_4547365) baseStart_4547365 baseEnd_4547365 := by
    simpa [prefixWord, tailWord_4547365, baseEnd_4547365] using wordTrace_append hprefix tailTrace_4547365
  have hstable : (prefixWord ++ tailWord_4547365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4547365).length < 2 ^ (prefixWord ++ tailWord_4547365).sum := by decide
  have hdescent : baseEnd_4547365 < baseStart_4547365 := by decide
  rcases family_descends (prefixWord ++ tailWord_4547365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4547378 : List Nat := [3, 2, 1, 1, 3, 1, 2, 1, 2, 1, 6]
def baseStart_4547378 : Nat := 118140960795 + 4547378 * 2 ^ 59
def prefixEnd_4547378 : Nat := 4983230072969 + 3 ^ 40 * 4547378 * 2
def baseEnd_4547378 : Nat := 2334990631681214596361995

theorem tailTrace_4547378 : CollatzResearch.WordTrace tailWord_4547378 prefixEnd_4547378 2334990631681214596361995 := by
  unfold tailWord_4547378
  simp only [CollatzResearch.WordTrace]
  refine ⟨41464125329908402794202697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110571000879755740784540525 41464125329908402794202697)
  ·
    refine ⟨31098093997431302095652023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41464125329908402794202697 31098093997431302095652023)
    ·
      refine ⟨46647140996146953143478035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31098093997431302095652023 46647140996146953143478035)
      ·
        refine ⟨69970711494220429715217053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46647140996146953143478035 69970711494220429715217053)
        ·
          refine ⟨26239016810332661143206395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69970711494220429715217053 26239016810332661143206395)
          ·
            refine ⟨39358525215498991714809593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26239016810332661143206395 39358525215498991714809593)
            ·
              refine ⟨29518893911624243786107195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39358525215498991714809593 29518893911624243786107195)
              ·
                refine ⟨44278340867436365679160793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29518893911624243786107195 44278340867436365679160793)
                ·
                  refine ⟨33208755650577274259370595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44278340867436365679160793 33208755650577274259370595)
                  ·
                    refine ⟨49813133475865911389055893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33208755650577274259370595 49813133475865911389055893)
                    ·
                      refine ⟨2334990631681214596361995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49813133475865911389055893 2334990631681214596361995)
                      ·
                        rfl

theorem cell23_4547378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 2, 1, 6].length) (baseStart_4547378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4547378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4547378 prefixEnd_4547378 := by exact prefixLift 4547378
  have htrace : WordTrace (prefixWord ++ tailWord_4547378) baseStart_4547378 baseEnd_4547378 := by
    simpa [prefixWord, tailWord_4547378, baseEnd_4547378] using wordTrace_append hprefix tailTrace_4547378
  have hstable : (prefixWord ++ tailWord_4547378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4547378).length < 2 ^ (prefixWord ++ tailWord_4547378).sum := by decide
  have hdescent : baseEnd_4547378 < baseStart_4547378 := by decide
  rcases family_descends (prefixWord ++ tailWord_4547378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4547426 : List Nat := [3, 3, 2, 1, 3, 1, 2, 3, 1, 4]
def baseStart_4547426 : Nat := 118140960795 + 4547426 * 2 ^ 59
def prefixEnd_4547426 : Nat := 4983230072969 + 3 ^ 40 * 4547426 * 2
def baseEnd_4547426 : Nat := 778338426250876802853925

theorem tailTrace_4547426 : CollatzResearch.WordTrace tailWord_4547426 prefixEnd_4547426 778338426250876802853925 := by
  unfold tailWord_4547426
  simp only [CollatzResearch.WordTrace]
  refine ⟨41464563005864928843639533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110572168015639810249705421 41464563005864928843639533)
  ·
    refine ⟨15549211127199348316364825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41464563005864928843639533 15549211127199348316364825)
    ·
      refine ⟨11661908345399511237273619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15549211127199348316364825 11661908345399511237273619)
      ·
        refine ⟨17492862518099266855910429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11661908345399511237273619 17492862518099266855910429)
        ·
          refine ⟨6559823444287225070966411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17492862518099266855910429 6559823444287225070966411)
          ·
            refine ⟨9839735166430837606449617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6559823444287225070966411 9839735166430837606449617)
            ·
              refine ⟨7379801374823128204837213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9839735166430837606449617 7379801374823128204837213)
              ·
                refine ⟨2767425515558673076813955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7379801374823128204837213 2767425515558673076813955)
                ·
                  refine ⟨4151138273338009615220933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2767425515558673076813955 4151138273338009615220933)
                  ·
                    refine ⟨778338426250876802853925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4151138273338009615220933 778338426250876802853925)
                    ·
                      rfl

theorem cell23_4547426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_4547426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4547426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4547426 prefixEnd_4547426 := by exact prefixLift 4547426
  have htrace : WordTrace (prefixWord ++ tailWord_4547426) baseStart_4547426 baseEnd_4547426 := by
    simpa [prefixWord, tailWord_4547426, baseEnd_4547426] using wordTrace_append hprefix tailTrace_4547426
  have hstable : (prefixWord ++ tailWord_4547426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4547426).length < 2 ^ (prefixWord ++ tailWord_4547426).sum := by decide
  have hdescent : baseEnd_4547426 < baseStart_4547426 := by decide
  rcases family_descends (prefixWord ++ tailWord_4547426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4547442 : List Nat := [3, 2, 1, 2, 1, 1, 2, 4, 2, 3, 2]
def baseStart_4547442 : Nat := 118140960795 + 4547442 * 2 ^ 59
def prefixEnd_4547442 : Nat := 4983230072969 + 3 ^ 40 * 4547442 * 2
def baseEnd_4547442 : Nat := 2335023494443102345961701

theorem tailTrace_4547442 : CollatzResearch.WordTrace tailWord_4547442 prefixEnd_4547442 2335023494443102345961701 := by
  unfold tailWord_4547442
  simp only [CollatzResearch.WordTrace]
  refine ⟨41464708897850437526785145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110572557060934500071427053 41464708897850437526785145)
  ·
    refine ⟨31098531673387828145088859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41464708897850437526785145 31098531673387828145088859)
    ·
      refine ⟨46647797510081742217633289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31098531673387828145088859 46647797510081742217633289)
      ·
        refine ⟨34985848132561306663224967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46647797510081742217633289 34985848132561306663224967)
        ·
          refine ⟨52478772198841959994837451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34985848132561306663224967 52478772198841959994837451)
          ·
            refine ⟨78718158298262939992256177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52478772198841959994837451 78718158298262939992256177)
            ·
              refine ⟨59038618723697204994192133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78718158298262939992256177 59038618723697204994192133)
              ·
                refine ⟨11069741010693225936411025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59038618723697204994192133 11069741010693225936411025)
                ·
                  refine ⟨8302305758019919452308269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11069741010693225936411025 8302305758019919452308269)
                  ·
                    refine ⟨3113364659257469794615601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8302305758019919452308269 3113364659257469794615601)
                    ·
                      refine ⟨2335023494443102345961701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3113364659257469794615601 2335023494443102345961701)
                      ·
                        rfl

theorem cell23_4547442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 4, 2, 3, 2].length) (baseStart_4547442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4547442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4547442 prefixEnd_4547442 := by exact prefixLift 4547442
  have htrace : WordTrace (prefixWord ++ tailWord_4547442) baseStart_4547442 baseEnd_4547442 := by
    simpa [prefixWord, tailWord_4547442, baseEnd_4547442] using wordTrace_append hprefix tailTrace_4547442
  have hstable : (prefixWord ++ tailWord_4547442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4547442).length < 2 ^ (prefixWord ++ tailWord_4547442).sum := by decide
  have hdescent : baseEnd_4547442 < baseStart_4547442 := by decide
  rcases family_descends (prefixWord ++ tailWord_4547442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4547449 : List Nat := [1, 2, 1, 3, 2, 3, 2, 4, 1, 1, 3]
def baseStart_4547449 : Nat := 118140960795 + 4547449 * 2 ^ 59
def prefixEnd_4547449 : Nat := 4983230072969 + 3 ^ 40 * 4547449 * 2
def baseEnd_4547449 : Nat := 2335027088807683818574169

theorem tailTrace_4547449 : CollatzResearch.WordTrace tailWord_4547449 prefixEnd_4547449 2335027088807683818574169 := by
  unfold tailWord_4547449
  simp only [CollatzResearch.WordTrace]
  refine ⟨165859090902376390302645401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110572727268250926868430267 165859090902376390302645401)
  ·
    refine ⟨124394318176782292726984051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165859090902376390302645401 124394318176782292726984051)
    ·
      refine ⟨186591477265173439090476077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124394318176782292726984051 186591477265173439090476077)
      ·
        refine ⟨69971803974440039658928529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 186591477265173439090476077 69971803974440039658928529)
        ·
          refine ⟨52478852980830029744196397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69971803974440039658928529 52478852980830029744196397)
          ·
            refine ⟨19679569867811261154073649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52478852980830029744196397 19679569867811261154073649)
            ·
              refine ⟨14759677400858445865555237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19679569867811261154073649 14759677400858445865555237)
              ·
                refine ⟨2767439512660958599791607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14759677400858445865555237 2767439512660958599791607)
                ·
                  refine ⟨4151159268991437899687411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2767439512660958599791607 4151159268991437899687411)
                  ·
                    refine ⟨6226738903487156849531117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4151159268991437899687411 6226738903487156849531117)
                    ·
                      refine ⟨2335027088807683818574169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6226738903487156849531117 2335027088807683818574169)
                      ·
                        rfl

theorem cell23_4547449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 4, 1, 1, 3].length) (baseStart_4547449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4547449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4547449 prefixEnd_4547449 := by exact prefixLift 4547449
  have htrace : WordTrace (prefixWord ++ tailWord_4547449) baseStart_4547449 baseEnd_4547449 := by
    simpa [prefixWord, tailWord_4547449, baseEnd_4547449] using wordTrace_append hprefix tailTrace_4547449
  have hstable : (prefixWord ++ tailWord_4547449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4547449).length < 2 ^ (prefixWord ++ tailWord_4547449).sum := by decide
  have hdescent : baseEnd_4547449 < baseStart_4547449 := by decide
  rcases family_descends (prefixWord ++ tailWord_4547449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4547465 : List Nat := [1, 2, 1, 1, 5, 2, 3, 1, 1, 6]
def baseStart_4547465 : Nat := 118140960795 + 4547465 * 2 ^ 59
def prefixEnd_4547465 : Nat := 4983230072969 + 3 ^ 40 * 4547465 * 2
def baseEnd_4547465 : Nat := 778345101499385251991365

theorem tailTrace_4547465 : CollatzResearch.WordTrace tailWord_4547465 prefixEnd_4547465 778345101499385251991365 := by
  unfold tailWord_4547465
  simp only [CollatzResearch.WordTrace]
  refine ⟨165859674470318425035227849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110573116313545616690151899 165859674470318425035227849)
  ·
    refine ⟨124394755852738818776420887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165859674470318425035227849 124394755852738818776420887)
    ·
      refine ⟨186592133779108228164631331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124394755852738818776420887 186592133779108228164631331)
      ·
        refine ⟨279888200668662342246946997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186592133779108228164631331 279888200668662342246946997)
        ·
          refine ⟨26239518812687094585651281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 279888200668662342246946997 26239518812687094585651281)
          ·
            refine ⟨19679639109515320939238461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26239518812687094585651281 19679639109515320939238461)
            ·
              refine ⟨7379864666068245352214423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19679639109515320939238461 7379864666068245352214423)
              ·
                refine ⟨11069796999102368028321635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7379864666068245352214423 11069796999102368028321635)
                ·
                  refine ⟨16604695498653552042482453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11069796999102368028321635 16604695498653552042482453)
                  ·
                    refine ⟨778345101499385251991365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16604695498653552042482453 778345101499385251991365)
                    ·
                      rfl

theorem cell23_4547465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 1, 1, 6].length) (baseStart_4547465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4547465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4547465 prefixEnd_4547465 := by exact prefixLift 4547465
  have htrace : WordTrace (prefixWord ++ tailWord_4547465) baseStart_4547465 baseEnd_4547465 := by
    simpa [prefixWord, tailWord_4547465, baseEnd_4547465] using wordTrace_append hprefix tailTrace_4547465
  have hstable : (prefixWord ++ tailWord_4547465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4547465).length < 2 ^ (prefixWord ++ tailWord_4547465).sum := by decide
  have hdescent : baseEnd_4547465 < baseStart_4547465 := by decide
  rcases family_descends (prefixWord ++ tailWord_4547465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4547485 : List Nat := [1, 4, 2, 1, 2, 1, 2, 1, 3, 2, 4]
def baseStart_4547485 : Nat := 118140960795 + 4547485 * 2 ^ 59
def prefixEnd_4547485 : Nat := 4983230072969 + 3 ^ 40 * 4547485 * 2
def baseEnd_4547485 : Nat := 2335045574111245677724003

theorem tailTrace_4547485 : CollatzResearch.WordTrace tailWord_4547485 prefixEnd_4547485 2335045574111245677724003 := by
  unfold tailWord_4547485
  simp only [CollatzResearch.WordTrace]
  refine ⟨165860403930245968450955909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110573602620163978967303939 165860403930245968450955909)
  ·
    refine ⟨31098825736921119084554233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 165860403930245968450955909 31098825736921119084554233)
    ·
      refine ⟨23324119302690839313415675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31098825736921119084554233 23324119302690839313415675)
      ·
        refine ⟨34986178954036258970123513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23324119302690839313415675 34986178954036258970123513)
        ·
          refine ⟨26239634215527194227592635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34986178954036258970123513 26239634215527194227592635)
          ·
            refine ⟨39359451323290791341388953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26239634215527194227592635 39359451323290791341388953)
            ·
              refine ⟨29519588492468093506041715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39359451323290791341388953 29519588492468093506041715)
              ·
                refine ⟨44279382738702140259062573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29519588492468093506041715 44279382738702140259062573)
                ·
                  refine ⟨16604768527013302597148465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44279382738702140259062573 16604768527013302597148465)
                  ·
                    refine ⟨12453576395259976947861349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16604768527013302597148465 12453576395259976947861349)
                    ·
                      refine ⟨2335045574111245677724003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12453576395259976947861349 2335045574111245677724003)
                      ·
                        rfl

theorem cell23_4547485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_4547485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4547485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4547485 prefixEnd_4547485 := by exact prefixLift 4547485
  have htrace : WordTrace (prefixWord ++ tailWord_4547485) baseStart_4547485 baseEnd_4547485 := by
    simpa [prefixWord, tailWord_4547485, baseEnd_4547485] using wordTrace_append hprefix tailTrace_4547485
  have hstable : (prefixWord ++ tailWord_4547485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4547485).length < 2 ^ (prefixWord ++ tailWord_4547485).sum := by decide
  have hdescent : baseEnd_4547485 < baseStart_4547485 := by decide
  rcases family_descends (prefixWord ++ tailWord_4547485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4547492 : List Nat := [2, 3, 1, 2, 1, 2, 1, 5, 1, 2, 3]
def baseStart_4547492 : Nat := 118140960795 + 4547492 * 2 ^ 59
def prefixEnd_4547492 : Nat := 4983230072969 + 3 ^ 40 * 4547492 * 2
def baseEnd_4547492 : Nat := 2335049168475827150336471

theorem tailTrace_4547492 : CollatzResearch.WordTrace tailWord_4547492 prefixEnd_4547492 2335049168475827150336471 := by
  unfold tailWord_4547492
  simp only [CollatzResearch.WordTrace]
  refine ⟨82930329620610304323230365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110573772827480405764307153 82930329620610304323230365)
  ·
    refine ⟨31098873607728864121211387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82930329620610304323230365 31098873607728864121211387)
    ·
      refine ⟨46648310411593296181817081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31098873607728864121211387 46648310411593296181817081)
      ·
        refine ⟨34986232808694972136362811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46648310411593296181817081 34986232808694972136362811)
        ·
          refine ⟨52479349213042458204544217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34986232808694972136362811 52479349213042458204544217)
          ·
            refine ⟨39359511909781843653408163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52479349213042458204544217 39359511909781843653408163)
            ·
              refine ⟨59039267864672765480112245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39359511909781843653408163 59039267864672765480112245)
              ·
                refine ⟨5534931362313071763760523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 59039267864672765480112245 5534931362313071763760523)
                ·
                  refine ⟨8302397043469607645640785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5534931362313071763760523 8302397043469607645640785)
                  ·
                    refine ⟨6226797782602205734230589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8302397043469607645640785 6226797782602205734230589)
                    ·
                      refine ⟨2335049168475827150336471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6226797782602205734230589 2335049168475827150336471)
                      ·
                        rfl

theorem cell23_4547492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 5, 1, 2, 3].length) (baseStart_4547492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4547492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4547492 prefixEnd_4547492 := by exact prefixLift 4547492
  have htrace : WordTrace (prefixWord ++ tailWord_4547492) baseStart_4547492 baseEnd_4547492 := by
    simpa [prefixWord, tailWord_4547492, baseEnd_4547492] using wordTrace_append hprefix tailTrace_4547492
  have hstable : (prefixWord ++ tailWord_4547492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4547492).length < 2 ^ (prefixWord ++ tailWord_4547492).sum := by decide
  have hdescent : baseEnd_4547492 < baseStart_4547492 := by decide
  rcases family_descends (prefixWord ++ tailWord_4547492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4547555 : List Nat := [1, 1, 1, 6, 1, 1, 2, 2, 2, 6]
def baseStart_4547555 : Nat := 118140960795 + 4547555 * 2 ^ 59
def prefixEnd_4547555 : Nat := 4983230072969 + 3 ^ 40 * 4547555 * 2
def baseEnd_4547555 : Nat := 778360505919020134616227

theorem tailTrace_4547555 : CollatzResearch.WordTrace tailWord_4547555 prefixEnd_4547555 778360505919020134616227 := by
  unfold tailWord_4547555
  simp only [CollatzResearch.WordTrace]
  refine ⟨165862957039992370406004119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110575304693328246937336079 165862957039992370406004119)
  ·
    refine ⟨248794435559988555609006179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165862957039992370406004119 248794435559988555609006179)
    ·
      refine ⟨373191653339982833413509269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248794435559988555609006179 373191653339982833413509269)
      ·
        refine ⟨17493358750311695316258247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 373191653339982833413509269 17493358750311695316258247)
        ·
          refine ⟨26240038125467542974387371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17493358750311695316258247 26240038125467542974387371)
          ·
            refine ⟨39360057188201314461581057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26240038125467542974387371 39360057188201314461581057)
            ·
              refine ⟨29520042891150985846185793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39360057188201314461581057 29520042891150985846185793)
              ·
                refine ⟨22140032168363239384639345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29520042891150985846185793 22140032168363239384639345)
                ·
                  refine ⟨16605024126272429538479509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22140032168363239384639345 16605024126272429538479509)
                  ·
                    refine ⟨778360505919020134616227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16605024126272429538479509 778360505919020134616227)
                    ·
                      rfl

theorem cell23_4547555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 2, 2, 6].length) (baseStart_4547555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4547555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4547555 prefixEnd_4547555 := by exact prefixLift 4547555
  have htrace : WordTrace (prefixWord ++ tailWord_4547555) baseStart_4547555 baseEnd_4547555 := by
    simpa [prefixWord, tailWord_4547555, baseEnd_4547555] using wordTrace_append hprefix tailTrace_4547555
  have hstable : (prefixWord ++ tailWord_4547555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4547555).length < 2 ^ (prefixWord ++ tailWord_4547555).sum := by decide
  have hdescent : baseEnd_4547555 < baseStart_4547555 := by decide
  rcases family_descends (prefixWord ++ tailWord_4547555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4547557 : List Nat := [1, 3, 1, 6, 1, 2, 2, 2, 1, 2, 2]
def baseStart_4547557 : Nat := 118140960795 + 4547557 * 2 ^ 59
def prefixEnd_4547557 : Nat := 4983230072969 + 3 ^ 40 * 4547557 * 2
def baseEnd_4547557 : Nat := 2335082544718369396023673

theorem tailTrace_4547557 : CollatzResearch.WordTrace tailWord_4547557 prefixEnd_4547557 2335082544718369396023673 := by
  unfold tailWord_4547557
  simp only [CollatzResearch.WordTrace]
  refine ⟨165863029985985124747576925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110575353323990083165051283 165863029985985124747576925)
  ·
    refine ⟨62198636244744421780341347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165863029985985124747576925 62198636244744421780341347)
    ·
      refine ⟨93297954367116632670512021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62198636244744421780341347 93297954367116632670512021)
      ·
        refine ⟨4373341610958592156430251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 93297954367116632670512021 4373341610958592156430251)
        ·
          refine ⟨6560012416437888234645377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4373341610958592156430251 6560012416437888234645377)
          ·
            refine ⟨4920009312328416175984033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6560012416437888234645377 4920009312328416175984033)
            ·
              refine ⟨3690006984246312131988025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4920009312328416175984033 3690006984246312131988025)
              ·
                refine ⟨2767505238184734098991019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3690006984246312131988025 2767505238184734098991019)
                ·
                  refine ⟨4151257857277101148486529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2767505238184734098991019 4151257857277101148486529)
                  ·
                    refine ⟨3113443392957825861364897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4151257857277101148486529 3113443392957825861364897)
                    ·
                      refine ⟨2335082544718369396023673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3113443392957825861364897 2335082544718369396023673)
                      ·
                        rfl

theorem cell23_4547557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_4547557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4547557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4547557 prefixEnd_4547557 := by exact prefixLift 4547557
  have htrace : WordTrace (prefixWord ++ tailWord_4547557) baseStart_4547557 baseEnd_4547557 := by
    simpa [prefixWord, tailWord_4547557, baseEnd_4547557] using wordTrace_append hprefix tailTrace_4547557
  have hstable : (prefixWord ++ tailWord_4547557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4547557).length < 2 ^ (prefixWord ++ tailWord_4547557).sum := by decide
  have hdescent : baseEnd_4547557 < baseStart_4547557 := by decide
  rcases family_descends (prefixWord ++ tailWord_4547557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4547585 : List Nat := [1, 2, 4, 1, 2, 2, 1, 1, 9]
def baseStart_4547585 : Nat := 118140960795 + 4547585 * 2 ^ 59
def prefixEnd_4547585 : Nat := 4983230072969 + 3 ^ 40 * 4547585 * 2
def baseEnd_4547585 : Nat := 259455213575188365163727

theorem tailTrace_4547585 : CollatzResearch.WordTrace tailWord_4547585 prefixEnd_4547585 259455213575188365163727 := by
  unfold tailWord_4547585
  simp only [CollatzResearch.WordTrace]
  refine ⟨165864051229883685529596209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110576034153255790353064139 165864051229883685529596209)
  ·
    refine ⟨124398038422412764147197157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165864051229883685529596209 124398038422412764147197157)
    ·
      refine ⟨23324632204202393277599467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 124398038422412764147197157 23324632204202393277599467)
      ·
        refine ⟨34986948306303589916399201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23324632204202393277599467 34986948306303589916399201)
        ·
          refine ⟨26240211229727692437299401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34986948306303589916399201 26240211229727692437299401)
          ·
            refine ⟨19680158422295769327974551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26240211229727692437299401 19680158422295769327974551)
            ·
              refine ⟨29520237633443653991961827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19680158422295769327974551 29520237633443653991961827)
              ·
                refine ⟨44280356450165480987942741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29520237633443653991961827 44280356450165480987942741)
                ·
                  refine ⟨259455213575188365163727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 44280356450165480987942741 259455213575188365163727)
                  ·
                    rfl

theorem cell23_4547585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 9].length) (baseStart_4547585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4547585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4547585 prefixEnd_4547585 := by exact prefixLift 4547585
  have htrace : WordTrace (prefixWord ++ tailWord_4547585) baseStart_4547585 baseEnd_4547585 := by
    simpa [prefixWord, tailWord_4547585, baseEnd_4547585] using wordTrace_append hprefix tailTrace_4547585
  have hstable : (prefixWord ++ tailWord_4547585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4547585).length < 2 ^ (prefixWord ++ tailWord_4547585).sum := by decide
  have hdescent : baseEnd_4547585 < baseStart_4547585 := by decide
  rcases family_descends (prefixWord ++ tailWord_4547585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4547665 : List Nat := [1, 2, 2, 1, 3, 1, 2, 1, 1, 3, 6]
def baseStart_4547665 : Nat := 118140960795 + 4547665 * 2 ^ 59
def prefixEnd_4547665 : Nat := 4983230072969 + 3 ^ 40 * 4547665 * 2
def baseEnd_4547665 : Nat := 2335138000629054973473175

theorem tailTrace_4547665 : CollatzResearch.WordTrace tailWord_4547665 prefixEnd_4547665 2335138000629054973473175 := by
  unfold tailWord_4547665
  simp only [CollatzResearch.WordTrace]
  refine ⟨165866969069593859192508449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110577979379729239461672299 165866969069593859192508449)
  ·
    refine ⟨124400226802195394394381337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165866969069593859192508449 124400226802195394394381337)
    ·
      refine ⟨93300170101646545795786003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124400226802195394394381337 93300170101646545795786003)
      ·
        refine ⟨139950255152469818693679005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93300170101646545795786003 139950255152469818693679005)
        ·
          refine ⟨52481345682176182010129627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 139950255152469818693679005 52481345682176182010129627)
          ·
            refine ⟨78722018523264273015194441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52481345682176182010129627 78722018523264273015194441)
            ·
              refine ⟨59041513892448204761395831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78722018523264273015194441 59041513892448204761395831)
              ·
                refine ⟨88562270838672307142093747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59041513892448204761395831 88562270838672307142093747)
                ·
                  refine ⟨132843406258008460713140621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 88562270838672307142093747 132843406258008460713140621)
                  ·
                    refine ⟨49816277346753172767427733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 132843406258008460713140621 49816277346753172767427733)
                    ·
                      refine ⟨2335138000629054973473175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49816277346753172767427733 2335138000629054973473175)
                      ·
                        rfl

theorem cell23_4547665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 3, 6].length) (baseStart_4547665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4547665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4547665 prefixEnd_4547665 := by exact prefixLift 4547665
  have htrace : WordTrace (prefixWord ++ tailWord_4547665) baseStart_4547665 baseEnd_4547665 := by
    simpa [prefixWord, tailWord_4547665, baseEnd_4547665] using wordTrace_append hprefix tailTrace_4547665
  have hstable : (prefixWord ++ tailWord_4547665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4547665).length < 2 ^ (prefixWord ++ tailWord_4547665).sum := by decide
  have hdescent : baseEnd_4547665 < baseStart_4547665 := by decide
  rcases family_descends (prefixWord ++ tailWord_4547665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4547670 : List Nat := [5, 2, 2, 1, 2, 1, 3, 2, 5]
def baseStart_4547670 : Nat := 118140960795 + 4547670 * 2 ^ 59
def prefixEnd_4547670 : Nat := 4983230072969 + 3 ^ 40 * 4547670 * 2
def baseEnd_4547670 : Nat := 259460063114703050434517

theorem tailTrace_4547670 : CollatzResearch.WordTrace tailWord_4547670 prefixEnd_4547670 259460063114703050434517 := by
  unfold tailWord_4547670
  simp only [CollatzResearch.WordTrace]
  refine ⟨10366696964660984065402529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 110578100956383830030960309 10366696964660984065402529)
  ·
    refine ⟨7775022723495738049051897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10366696964660984065402529 7775022723495738049051897)
    ·
      refine ⟨5831267042621803536788923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7775022723495738049051897 5831267042621803536788923)
      ·
        refine ⟨8746900563932705305183385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5831267042621803536788923 8746900563932705305183385)
        ·
          refine ⟨6560175422949528978887539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8746900563932705305183385 6560175422949528978887539)
          ·
            refine ⟨9840263134424293468331309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6560175422949528978887539 9840263134424293468331309)
            ·
              refine ⟨3690098675409110050624241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9840263134424293468331309 3690098675409110050624241)
              ·
                refine ⟨2767574006556832537968181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3690098675409110050624241 2767574006556832537968181)
                ·
                  refine ⟨259460063114703050434517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2767574006556832537968181 259460063114703050434517)
                  ·
                    rfl

theorem cell23_4547670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 3, 2, 5].length) (baseStart_4547670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4547670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4547670 prefixEnd_4547670 := by exact prefixLift 4547670
  have htrace : WordTrace (prefixWord ++ tailWord_4547670) baseStart_4547670 baseEnd_4547670 := by
    simpa [prefixWord, tailWord_4547670, baseEnd_4547670] using wordTrace_append hprefix tailTrace_4547670
  have hstable : (prefixWord ++ tailWord_4547670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4547670).length < 2 ^ (prefixWord ++ tailWord_4547670).sum := by decide
  have hdescent : baseEnd_4547670 < baseStart_4547670 := by decide
  rcases family_descends (prefixWord ++ tailWord_4547670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4547692 : List Nat := [2, 2, 1, 1, 3, 2, 3, 3, 6]
def baseStart_4547692 : Nat := 118140960795 + 4547692 * 2 ^ 59
def prefixEnd_4547692 : Nat := 4983230072969 + 3 ^ 40 * 4547692 * 2
def baseEnd_4547692 : Nat := 259461318289636263092839

theorem tailTrace_4547692 : CollatzResearch.WordTrace tailWord_4547692 prefixEnd_4547692 259461318289636263092839 := by
  unfold tailWord_4547692
  simp only [CollatzResearch.WordTrace]
  refine ⟨82933976920248021401870665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110578635893664028535827553 82933976920248021401870665)
  ·
    refine ⟨62200482690186016051402999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82933976920248021401870665 62200482690186016051402999)
    ·
      refine ⟨93300724035279024077104499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62200482690186016051402999 93300724035279024077104499)
      ·
        refine ⟨139951086052918536115656749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93300724035279024077104499 139951086052918536115656749)
        ·
          refine ⟨52481657269844451043371281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 139951086052918536115656749 52481657269844451043371281)
          ·
            refine ⟨39361242952383338282528461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52481657269844451043371281 39361242952383338282528461)
            ·
              refine ⟨14760466107143751855948173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39361242952383338282528461 14760466107143751855948173)
              ·
                refine ⟨5535174790178906945980565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14760466107143751855948173 5535174790178906945980565)
                ·
                  refine ⟨259461318289636263092839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5535174790178906945980565 259461318289636263092839)
                  ·
                    rfl

theorem cell23_4547692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 6].length) (baseStart_4547692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4547692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4547692 prefixEnd_4547692 := by exact prefixLift 4547692
  have htrace : WordTrace (prefixWord ++ tailWord_4547692) baseStart_4547692 baseEnd_4547692 := by
    simpa [prefixWord, tailWord_4547692, baseEnd_4547692] using wordTrace_append hprefix tailTrace_4547692
  have hstable : (prefixWord ++ tailWord_4547692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4547692).length < 2 ^ (prefixWord ++ tailWord_4547692).sum := by decide
  have hdescent : baseEnd_4547692 < baseStart_4547692 := by decide
  rcases family_descends (prefixWord ++ tailWord_4547692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4547730 : List Nat := [3, 2, 3, 1, 1, 4, 2, 2, 1, 4]
def baseStart_4547730 : Nat := 118140960795 + 4547730 * 2 ^ 59
def prefixEnd_4547730 : Nat := 4983230072969 + 3 ^ 40 * 4547730 * 2
def baseEnd_4547730 : Nat := 778390458957199073053459

theorem tailTrace_4547730 : CollatzResearch.WordTrace tailWord_4547730 prefixEnd_4547730 778390458957199073053459 := by
  unfold tailWord_4547730
  simp only [CollatzResearch.WordTrace]
  refine ⟨41467334953589593823406161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110579559876238916862416429 41467334953589593823406161)
  ·
    refine ⟨31100501215192195367554621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41467334953589593823406161 31100501215192195367554621)
    ·
      refine ⟨11662687955697073262832983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31100501215192195367554621 11662687955697073262832983)
      ·
        refine ⟨17494031933545609894249475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11662687955697073262832983 17494031933545609894249475)
        ·
          refine ⟨26241047900318414841374213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17494031933545609894249475 26241047900318414841374213)
          ·
            refine ⟨4920196481309702782757665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26241047900318414841374213 4920196481309702782757665)
            ·
              refine ⟨3690147360982277087068249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4920196481309702782757665 3690147360982277087068249)
              ·
                refine ⟨2767610520736707815301187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3690147360982277087068249 2767610520736707815301187)
                ·
                  refine ⟨4151415781105061722951781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2767610520736707815301187 4151415781105061722951781)
                  ·
                    refine ⟨778390458957199073053459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4151415781105061722951781 778390458957199073053459)
                    ·
                      rfl

theorem cell23_4547730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_4547730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4547730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4547730 prefixEnd_4547730 := by exact prefixLift 4547730
  have htrace : WordTrace (prefixWord ++ tailWord_4547730) baseStart_4547730 baseEnd_4547730 := by
    simpa [prefixWord, tailWord_4547730, baseEnd_4547730] using wordTrace_append hprefix tailTrace_4547730
  have hstable : (prefixWord ++ tailWord_4547730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4547730).length < 2 ^ (prefixWord ++ tailWord_4547730).sum := by decide
  have hdescent : baseEnd_4547730 < baseStart_4547730 := by decide
  rcases family_descends (prefixWord ++ tailWord_4547730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
