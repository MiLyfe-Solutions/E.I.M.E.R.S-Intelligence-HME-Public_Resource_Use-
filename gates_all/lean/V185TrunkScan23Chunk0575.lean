import V185TrunkScan23Chunk0574

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3399692 : List Nat := [2, 2, 1, 2, 3, 1, 4, 1, 2, 5]
def baseStart_3399692 : Nat := 118140960795 + 3399692 * 2 ^ 59
def prefixEnd_3399692 : Nat := 4983230072969 + 3 ^ 40 * 3399692 * 2
def baseEnd_3399692 : Nat := 581892024415072641038369

theorem tailTrace_3399692 : CollatzResearch.WordTrace tailWord_3399692 prefixEnd_3399692 581892024415072641038369 := by
  unfold tailWord_3399692
  simp only [CollatzResearch.WordTrace]
  refine ⟨61998476999751990006548665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82664635999669320008731553 61998476999751990006548665)
  ·
    refine ⟨46498857749813992504911499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61998476999751990006548665 46498857749813992504911499)
    ·
      refine ⟨69748286624720988757367249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46498857749813992504911499 69748286624720988757367249)
      ·
        refine ⟨52311214968540741568025437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69748286624720988757367249 52311214968540741568025437)
        ·
          refine ⟨19616705613202778088009539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52311214968540741568025437 19616705613202778088009539)
          ·
            refine ⟨29425058419804167132014309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19616705613202778088009539 29425058419804167132014309)
            ·
              refine ⟨5517198453713281337252683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29425058419804167132014309 5517198453713281337252683)
              ·
                refine ⟨8275797680569922005879025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5517198453713281337252683 8275797680569922005879025)
                ·
                  refine ⟨6206848260427441504409269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8275797680569922005879025 6206848260427441504409269)
                  ·
                    refine ⟨581892024415072641038369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6206848260427441504409269 581892024415072641038369)
                    ·
                      rfl

theorem cell23_3399692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 1, 2, 5].length) (baseStart_3399692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3399692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3399692 prefixEnd_3399692 := by exact prefixLift 3399692
  have htrace : WordTrace (prefixWord ++ tailWord_3399692) baseStart_3399692 baseEnd_3399692 := by
    simpa [prefixWord, tailWord_3399692, baseEnd_3399692] using wordTrace_append hprefix tailTrace_3399692
  have hstable : (prefixWord ++ tailWord_3399692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399692).length < 2 ^ (prefixWord ++ tailWord_3399692).sum := by decide
  have hdescent : baseEnd_3399692 < baseStart_3399692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399713 : List Nat := [1, 2, 3, 2, 5, 1, 2, 2, 5]
def baseStart_3399713 : Nat := 118140960795 + 3399713 * 2 ^ 59
def prefixEnd_3399713 : Nat := 4983230072969 + 3 ^ 40 * 3399713 * 2
def baseEnd_3399713 : Nat := 193965206259884704550279

theorem tailTrace_3399713 : CollatzResearch.WordTrace tailWord_3399713 prefixEnd_3399713 193965206259884704550279 := by
  unfold tailWord_3399713
  simp only [CollatzResearch.WordTrace]
  refine ⟨123997719932427900599611793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82665146621618600399741195 123997719932427900599611793)
  ·
    refine ⟨92998289949320925449708845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123997719932427900599611793 92998289949320925449708845)
    ·
      refine ⟨34874358730995347043640817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92998289949320925449708845 34874358730995347043640817)
      ·
        refine ⟨26155769048246510282730613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34874358730995347043640817 26155769048246510282730613)
        ·
          refine ⟨2452103348273110339005995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26155769048246510282730613 2452103348273110339005995)
          ·
            refine ⟨3678155022409665508508993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2452103348273110339005995 3678155022409665508508993)
            ·
              refine ⟨2758616266807249131381745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3678155022409665508508993 2758616266807249131381745)
              ·
                refine ⟨2068962200105436848536309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2758616266807249131381745 2068962200105436848536309)
                ·
                  refine ⟨193965206259884704550279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2068962200105436848536309 193965206259884704550279)
                  ·
                    rfl

theorem cell23_3399713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 2, 2, 5].length) (baseStart_3399713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3399713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3399713 prefixEnd_3399713 := by exact prefixLift 3399713
  have htrace : WordTrace (prefixWord ++ tailWord_3399713) baseStart_3399713 baseEnd_3399713 := by
    simpa [prefixWord, tailWord_3399713, baseEnd_3399713] using wordTrace_append hprefix tailTrace_3399713
  have hstable : (prefixWord ++ tailWord_3399713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399713).length < 2 ^ (prefixWord ++ tailWord_3399713).sum := by decide
  have hdescent : baseEnd_3399713 < baseStart_3399713 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399715 : List Nat := [1, 1, 1, 4, 3, 1, 1, 1, 2, 3, 5]
def baseStart_3399715 : Nat := 118140960795 + 3399715 * 2 ^ 59
def prefixEnd_3399715 : Nat := 4983230072969 + 3 ^ 40 * 3399715 * 2
def baseEnd_3399715 : Nat := 1745687883300271333127501

theorem tailTrace_3399715 : CollatzResearch.WordTrace tailWord_3399715 prefixEnd_3399715 1745687883300271333127501 := by
  unfold tailWord_3399715
  simp only [CollatzResearch.WordTrace]
  refine ⟨123997792878420654941184599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82665195252280436627456399 123997792878420654941184599)
  ·
    refine ⟨185996689317630982411776899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123997792878420654941184599 185996689317630982411776899)
    ·
      refine ⟨278995033976446473617665349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185996689317630982411776899 278995033976446473617665349)
      ·
        refine ⟨52311568870583713803312253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 278995033976446473617665349 52311568870583713803312253)
        ·
          refine ⟨19616838326468892676242095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52311568870583713803312253 19616838326468892676242095)
          ·
            refine ⟨29425257489703339014363143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19616838326468892676242095 29425257489703339014363143)
            ·
              refine ⟨44137886234555008521544715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29425257489703339014363143 44137886234555008521544715)
              ·
                refine ⟨66206829351832512782317073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44137886234555008521544715 66206829351832512782317073)
                ·
                  refine ⟨49655122013874384586737805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66206829351832512782317073 49655122013874384586737805)
                  ·
                    refine ⟨18620670755202894220026677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49655122013874384586737805 18620670755202894220026677)
                    ·
                      refine ⟨1745687883300271333127501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18620670755202894220026677 1745687883300271333127501)
                      ·
                        rfl

theorem cell23_3399715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 3, 5].length) (baseStart_3399715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3399715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3399715 prefixEnd_3399715 := by exact prefixLift 3399715
  have htrace : WordTrace (prefixWord ++ tailWord_3399715) baseStart_3399715 baseEnd_3399715 := by
    simpa [prefixWord, tailWord_3399715, baseEnd_3399715] using wordTrace_append hprefix tailTrace_3399715
  have hstable : (prefixWord ++ tailWord_3399715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399715).length < 2 ^ (prefixWord ++ tailWord_3399715).sum := by decide
  have hdescent : baseEnd_3399715 < baseStart_3399715 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399729 : List Nat := [1, 2, 2, 3, 1, 4, 1, 1, 2, 4, 2]
def baseStart_3399729 : Nat := 118140960795 + 3399729 * 2 ^ 59
def prefixEnd_3399729 : Nat := 4983230072969 + 3 ^ 40 * 3399729 * 2
def baseEnd_3399729 : Nat := 1745695072029434278352437

theorem tailTrace_3399729 : CollatzResearch.WordTrace tailWord_3399729 prefixEnd_3399729 1745695072029434278352437 := by
  unfold tailWord_3399729
  simp only [CollatzResearch.WordTrace]
  refine ⟨123998303500369935332194241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82665535666913290221462827 123998303500369935332194241)
  ·
    refine ⟨92998727625277451499145681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123998303500369935332194241 92998727625277451499145681)
    ·
      refine ⟨69749045718958088624359261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92998727625277451499145681 69749045718958088624359261)
      ·
        refine ⟨26155892144609283234134723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69749045718958088624359261 26155892144609283234134723)
        ·
          refine ⟨39233838216913924851202085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26155892144609283234134723 39233838216913924851202085)
          ·
            refine ⟨7356344665671360909600391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39233838216913924851202085 7356344665671360909600391)
            ·
              refine ⟨11034516998507041364400587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7356344665671360909600391 11034516998507041364400587)
              ·
                refine ⟨16551775497760562046600881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11034516998507041364400587 16551775497760562046600881)
                ·
                  refine ⟨12413831623320421534950661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16551775497760562046600881 12413831623320421534950661)
                  ·
                    refine ⟨2327593429372579037803249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12413831623320421534950661 2327593429372579037803249)
                    ·
                      refine ⟨1745695072029434278352437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2327593429372579037803249 1745695072029434278352437)
                      ·
                        rfl

theorem cell23_3399729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 1, 2, 4, 2].length) (baseStart_3399729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3399729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3399729 prefixEnd_3399729 := by exact prefixLift 3399729
  have htrace : WordTrace (prefixWord ++ tailWord_3399729) baseStart_3399729 baseEnd_3399729 := by
    simpa [prefixWord, tailWord_3399729, baseEnd_3399729] using wordTrace_append hprefix tailTrace_3399729
  have hstable : (prefixWord ++ tailWord_3399729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399729).length < 2 ^ (prefixWord ++ tailWord_3399729).sum := by decide
  have hdescent : baseEnd_3399729 < baseStart_3399729 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399772 : List Nat := [2, 2, 4, 1, 1, 2, 1, 1, 1, 2, 6]
def baseStart_3399772 : Nat := 118140960795 + 3399772 * 2 ^ 59
def prefixEnd_3399772 : Nat := 4983230072969 + 3 ^ 40 * 3399772 * 2
def baseEnd_3399772 : Nat := 1745717151697577610114739

theorem tailTrace_3399772 : CollatzResearch.WordTrace tailWord_3399772 prefixEnd_3399772 1745717151697577610114739 := by
  unfold tailWord_3399772
  simp only [CollatzResearch.WordTrace]
  refine ⟨61999935919607076838004785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82666581226142769117339713 61999935919607076838004785)
  ·
    refine ⟨46499951939705307628503589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61999935919607076838004785 46499951939705307628503589)
    ·
      refine ⟨8718740988694745180344423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46499951939705307628503589 8718740988694745180344423)
      ·
        refine ⟨13078111483042117770516635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8718740988694745180344423 13078111483042117770516635)
        ·
          refine ⟨19617167224563176655774953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13078111483042117770516635 19617167224563176655774953)
          ·
            refine ⟨14712875418422382491831215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19617167224563176655774953 14712875418422382491831215)
            ·
              refine ⟨22069313127633573737746823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14712875418422382491831215 22069313127633573737746823)
              ·
                refine ⟨33103969691450360606620235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22069313127633573737746823 33103969691450360606620235)
                ·
                  refine ⟨49655954537175540909930353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33103969691450360606620235 49655954537175540909930353)
                  ·
                    refine ⟨37241965902881655682447765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49655954537175540909930353 37241965902881655682447765)
                    ·
                      refine ⟨1745717151697577610114739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37241965902881655682447765 1745717151697577610114739)
                      ·
                        rfl

theorem cell23_3399772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_3399772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3399772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3399772 prefixEnd_3399772 := by exact prefixLift 3399772
  have htrace : WordTrace (prefixWord ++ tailWord_3399772) baseStart_3399772 baseEnd_3399772 := by
    simpa [prefixWord, tailWord_3399772, baseEnd_3399772] using wordTrace_append hprefix tailTrace_3399772
  have hstable : (prefixWord ++ tailWord_3399772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399772).length < 2 ^ (prefixWord ++ tailWord_3399772).sum := by decide
  have hdescent : baseEnd_3399772 < baseStart_3399772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399773 : List Nat := [1, 4, 4, 1, 1, 1, 2, 4, 1, 4]
def baseStart_3399773 : Nat := 118140960795 + 3399773 * 2 ^ 59
def prefixEnd_3399773 : Nat := 4983230072969 + 3 ^ 40 * 3399773 * 2
def baseEnd_3399773 : Nat := 581905888392744035400745

theorem tailTrace_3399773 : CollatzResearch.WordTrace tailWord_3399773 prefixEnd_3399773 581905888392744035400745 := by
  unfold tailWord_3399773
  simp only [CollatzResearch.WordTrace]
  refine ⟨123999908312210530846795973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82666605541473687231197315 123999908312210530846795973)
  ·
    refine ⟨23249982808539474533774245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123999908312210530846795973 23249982808539474533774245)
    ·
      refine ⟨4359371776601151475082671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23249982808539474533774245 4359371776601151475082671)
      ·
        refine ⟨6539057664901727212624007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4359371776601151475082671 6539057664901727212624007)
        ·
          refine ⟨9808586497352590818936011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6539057664901727212624007 9808586497352590818936011)
          ·
            refine ⟨14712879746028886228404017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9808586497352590818936011 14712879746028886228404017)
            ·
              refine ⟨11034659809521664671303013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14712879746028886228404017 11034659809521664671303013)
              ·
                refine ⟨2068998714285312125869315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11034659809521664671303013 2068998714285312125869315)
                ·
                  refine ⟨3103498071427968188803973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2068998714285312125869315 3103498071427968188803973)
                  ·
                    refine ⟨581905888392744035400745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3103498071427968188803973 581905888392744035400745)
                    ·
                      rfl

theorem cell23_3399773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_3399773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3399773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3399773 prefixEnd_3399773 := by exact prefixLift 3399773
  have htrace : WordTrace (prefixWord ++ tailWord_3399773) baseStart_3399773 baseEnd_3399773 := by
    simpa [prefixWord, tailWord_3399773, baseEnd_3399773] using wordTrace_append hprefix tailTrace_3399773
  have hstable : (prefixWord ++ tailWord_3399773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399773).length < 2 ^ (prefixWord ++ tailWord_3399773).sum := by decide
  have hdescent : baseEnd_3399773 < baseStart_3399773 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399775 : List Nat := [1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 7]
def baseStart_3399775 : Nat := 118140960795 + 3399775 * 2 ^ 59
def prefixEnd_3399775 : Nat := 4983230072969 + 3 ^ 40 * 3399775 * 2
def baseEnd_3399775 : Nat := 1745718692139541098377225

theorem tailTrace_3399775 : CollatzResearch.WordTrace tailWord_3399775 prefixEnd_3399775 1745718692139541098377225 := by
  unfold tailWord_3399775
  simp only [CollatzResearch.WordTrace]
  refine ⟨123999981258203285188368779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82666654172135523458912519 123999981258203285188368779)
  ·
    refine ⟨185999971887304927782553169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123999981258203285188368779 185999971887304927782553169)
    ·
      refine ⟨139499978915478695836914877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185999971887304927782553169 139499978915478695836914877)
      ·
        refine ⟨52312492093304510938843079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139499978915478695836914877 52312492093304510938843079)
        ·
          refine ⟨78468738139956766408264619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52312492093304510938843079 78468738139956766408264619)
          ·
            refine ⟨117703107209935149612396929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78468738139956766408264619 117703107209935149612396929)
            ·
              refine ⟨88277330407451362209297697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117703107209935149612396929 88277330407451362209297697)
              ·
                refine ⟨66207997805588521656973273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88277330407451362209297697 66207997805588521656973273)
                ·
                  refine ⟨49655998354191391242729955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66207997805588521656973273 49655998354191391242729955)
                  ·
                    refine ⟨74483997531287086864094933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49655998354191391242729955 74483997531287086864094933)
                    ·
                      refine ⟨1745718692139541098377225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 74483997531287086864094933 1745718692139541098377225)
                      ·
                        rfl

theorem cell23_3399775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 7].length) (baseStart_3399775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3399775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3399775 prefixEnd_3399775 := by exact prefixLift 3399775
  have htrace : WordTrace (prefixWord ++ tailWord_3399775) baseStart_3399775 baseEnd_3399775 := by
    simpa [prefixWord, tailWord_3399775, baseEnd_3399775] using wordTrace_append hprefix tailTrace_3399775
  have hstable : (prefixWord ++ tailWord_3399775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399775).length < 2 ^ (prefixWord ++ tailWord_3399775).sum := by decide
  have hdescent : baseEnd_3399775 < baseStart_3399775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399779 : List Nat := [1, 1, 1, 5, 1, 1, 3, 3, 3, 1, 3]
def baseStart_3399779 : Nat := 118140960795 + 3399779 * 2 ^ 59
def prefixEnd_3399779 : Nat := 4983230072969 + 3 ^ 40 * 3399779 * 2
def baseEnd_3399779 : Nat := 1745720746062159082727207

theorem tailTrace_3399779 : CollatzResearch.WordTrace tailWord_3399779 prefixEnd_3399779 1745720746062159082727207 := by
  unfold tailWord_3399779
  simp only [CollatzResearch.WordTrace]
  refine ⟨124000127150188793871514391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82666751433459195914342927 124000127150188793871514391)
  ·
    refine ⟨186000190725283190807271587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124000127150188793871514391 186000190725283190807271587)
    ·
      refine ⟨279000286087924786210907381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186000190725283190807271587 279000286087924786210907381)
      ·
        refine ⟨26156276820742948707272567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 279000286087924786210907381 26156276820742948707272567)
        ·
          refine ⟨39234415231114423060908851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26156276820742948707272567 39234415231114423060908851)
          ·
            refine ⟨58851622846671634591363277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39234415231114423060908851 58851622846671634591363277)
            ·
              refine ⟨22069358567501862971761229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58851622846671634591363277 22069358567501862971761229)
              ·
                refine ⟨8276009462813198614410461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22069358567501862971761229 8276009462813198614410461)
                ·
                  refine ⟨3103503548554949480403923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8276009462813198614410461 3103503548554949480403923)
                  ·
                    refine ⟨4655255322832424220605885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3103503548554949480403923 4655255322832424220605885)
                    ·
                      refine ⟨1745720746062159082727207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4655255322832424220605885 1745720746062159082727207)
                      ·
                        rfl

theorem cell23_3399779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 3, 3, 1, 3].length) (baseStart_3399779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3399779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3399779 prefixEnd_3399779 := by exact prefixLift 3399779
  have htrace : WordTrace (prefixWord ++ tailWord_3399779) baseStart_3399779 baseEnd_3399779 := by
    simpa [prefixWord, tailWord_3399779, baseEnd_3399779] using wordTrace_append hprefix tailTrace_3399779
  have hstable : (prefixWord ++ tailWord_3399779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399779).length < 2 ^ (prefixWord ++ tailWord_3399779).sum := by decide
  have hdescent : baseEnd_3399779 < baseStart_3399779 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399786 : List Nat := [3, 1, 3, 2, 3, 1, 3, 1, 6]
def baseStart_3399786 : Nat := 118140960795 + 3399786 * 2 ^ 59
def prefixEnd_3399786 : Nat := 4983230072969 + 3 ^ 40 * 3399786 * 2
def baseEnd_3399786 : Nat := 193969371158526728371075

theorem tailTrace_3399786 : CollatzResearch.WordTrace tailWord_3399786 prefixEnd_3399786 193969371158526728371075 := by
  unfold tailWord_3399786
  simp only [CollatzResearch.WordTrace]
  refine ⟨31000095615290858516754803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82666921640775622711346141 31000095615290858516754803)
  ·
    refine ⟨46500143422936287775132205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31000095615290858516754803 46500143422936287775132205)
    ·
      refine ⟨17437553783601107915674577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46500143422936287775132205 17437553783601107915674577)
      ·
        refine ⟨13078165337700830936755933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17437553783601107915674577 13078165337700830936755933)
        ·
          refine ⟨4904312001637811601283475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13078165337700830936755933 4904312001637811601283475)
          ·
            refine ⟨7356468002456717401925213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4904312001637811601283475 7356468002456717401925213)
            ·
              refine ⟨2758675500921269025721955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7356468002456717401925213 2758675500921269025721955)
              ·
                refine ⟨4138013251381903538582933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2758675500921269025721955 4138013251381903538582933)
                ·
                  refine ⟨193969371158526728371075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4138013251381903538582933 193969371158526728371075)
                  ·
                    rfl

theorem cell23_3399786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 3, 1, 6].length) (baseStart_3399786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3399786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3399786 prefixEnd_3399786 := by exact prefixLift 3399786
  have htrace : WordTrace (prefixWord ++ tailWord_3399786) baseStart_3399786 baseEnd_3399786 := by
    simpa [prefixWord, tailWord_3399786, baseEnd_3399786] using wordTrace_append hprefix tailTrace_3399786
  have hstable : (prefixWord ++ tailWord_3399786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399786).length < 2 ^ (prefixWord ++ tailWord_3399786).sum := by decide
  have hdescent : baseEnd_3399786 < baseStart_3399786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399789 : List Nat := [1, 5, 1, 1, 2, 1, 1, 1, 3, 5, 2]
def baseStart_3399789 : Nat := 118140960795 + 3399789 * 2 ^ 59
def prefixEnd_3399789 : Nat := 4983230072969 + 3 ^ 40 * 3399789 * 2
def baseEnd_3399789 : Nat := 1745725880868704043602161

theorem tailTrace_3399789 : CollatzResearch.WordTrace tailWord_3399789 prefixEnd_3399789 1745725880868704043602161 := by
  unfold tailWord_3399789
  simp only [CollatzResearch.WordTrace]
  refine ⟨124000491880152565579378421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82666994586768377052918947 124000491880152565579378421)
  ·
    refine ⟨11625046113764303023066727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 124000491880152565579378421 11625046113764303023066727)
    ·
      refine ⟨17437569170646454534600091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11625046113764303023066727 17437569170646454534600091)
      ·
        refine ⟨26156353755969681801900137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17437569170646454534600091 26156353755969681801900137)
        ·
          refine ⟨19617265316977261351425103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26156353755969681801900137 19617265316977261351425103)
          ·
            refine ⟨29425897975465892027137655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19617265316977261351425103 29425897975465892027137655)
            ·
              refine ⟨44138846963198838040706483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29425897975465892027137655 44138846963198838040706483)
              ·
                refine ⟨66208270444798257061059725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44138846963198838040706483 66208270444798257061059725)
                ·
                  refine ⟨24828101416799346397897397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66208270444798257061059725 24828101416799346397897397)
                  ·
                    refine ⟨2327634507824938724802881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24828101416799346397897397 2327634507824938724802881)
                    ·
                      refine ⟨1745725880868704043602161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2327634507824938724802881 1745725880868704043602161)
                      ·
                        rfl

theorem cell23_3399789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 3, 5, 2].length) (baseStart_3399789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3399789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3399789 prefixEnd_3399789 := by exact prefixLift 3399789
  have htrace : WordTrace (prefixWord ++ tailWord_3399789) baseStart_3399789 baseEnd_3399789 := by
    simpa [prefixWord, tailWord_3399789, baseEnd_3399789] using wordTrace_append hprefix tailTrace_3399789
  have hstable : (prefixWord ++ tailWord_3399789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399789).length < 2 ^ (prefixWord ++ tailWord_3399789).sum := by decide
  have hdescent : baseEnd_3399789 < baseStart_3399789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399799 : List Nat := [1, 1, 3, 1, 1, 6, 2, 2, 1, 5]
def baseStart_3399799 : Nat := 118140960795 + 3399799 * 2 ^ 59
def prefixEnd_3399799 : Nat := 4983230072969 + 3 ^ 40 * 3399799 * 2
def baseEnd_3399799 : Nat := 581910338558416334825705

theorem tailTrace_3399799 : CollatzResearch.WordTrace tailWord_3399799 prefixEnd_3399799 581910338558416334825705 := by
  unfold tailWord_3399799
  simp only [CollatzResearch.WordTrace]
  refine ⟨124000856610116337287242451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82667237740077558191494967 124000856610116337287242451)
  ·
    refine ⟨186001284915174505930863677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124000856610116337287242451 186001284915174505930863677)
    ·
      refine ⟨69750481843190439724073879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186001284915174505930863677 69750481843190439724073879)
      ·
        refine ⟨104625722764785659586110819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69750481843190439724073879 104625722764785659586110819)
        ·
          refine ⟨156938584147178489379166229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104625722764785659586110819 156938584147178489379166229)
          ·
            refine ⟨7356496131898991689648417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 156938584147178489379166229 7356496131898991689648417)
            ·
              refine ⟨5517372098924243767236313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7356496131898991689648417 5517372098924243767236313)
              ·
                refine ⟨4138029074193182825427235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5517372098924243767236313 4138029074193182825427235)
                ·
                  refine ⟨6207043611289774238140853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4138029074193182825427235 6207043611289774238140853)
                  ·
                    refine ⟨581910338558416334825705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6207043611289774238140853 581910338558416334825705)
                    ·
                      rfl

theorem cell23_3399799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 2, 1, 5].length) (baseStart_3399799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3399799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3399799 prefixEnd_3399799 := by exact prefixLift 3399799
  have htrace : WordTrace (prefixWord ++ tailWord_3399799) baseStart_3399799 baseEnd_3399799 := by
    simpa [prefixWord, tailWord_3399799, baseEnd_3399799] using wordTrace_append hprefix tailTrace_3399799
  have hstable : (prefixWord ++ tailWord_3399799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399799).length < 2 ^ (prefixWord ++ tailWord_3399799).sum := by decide
  have hdescent : baseEnd_3399799 < baseStart_3399799 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399812 : List Nat := [2, 3, 2, 1, 2, 1, 2, 1, 3, 6]
def baseStart_3399812 : Nat := 118140960795 + 3399812 * 2 ^ 59
def prefixEnd_3399812 : Nat := 4983230072969 + 3 ^ 40 * 3399812 * 2
def baseEnd_3399812 : Nat := 581912563641252484538185

theorem tailTrace_3399812 : CollatzResearch.WordTrace tailWord_3399812 prefixEnd_3399812 581912563641252484538185 := by
  unfold tailWord_3399812
  simp only [CollatzResearch.WordTrace]
  refine ⟨62000665379534620253732845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82667553839379493671643793 62000665379534620253732845)
  ·
    refine ⟨23250249517325482595149817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62000665379534620253732845 23250249517325482595149817)
    ·
      refine ⟨17437687137994111946362363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23250249517325482595149817 17437687137994111946362363)
      ·
        refine ⟨26156530706991167919543545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17437687137994111946362363 26156530706991167919543545)
        ·
          refine ⟨19617398030243375939657659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26156530706991167919543545 19617398030243375939657659)
          ·
            refine ⟨29426097045365063909486489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19617398030243375939657659 29426097045365063909486489)
            ·
              refine ⟨22069572784023797932114867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29426097045365063909486489 22069572784023797932114867)
              ·
                refine ⟨33104359176035696898172301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22069572784023797932114867 33104359176035696898172301)
                ·
                  refine ⟨12414134691013386336814613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33104359176035696898172301 12414134691013386336814613)
                  ·
                    refine ⟨581912563641252484538185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12414134691013386336814613 581912563641252484538185)
                    ·
                      rfl

theorem cell23_3399812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 3, 6].length) (baseStart_3399812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3399812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3399812 prefixEnd_3399812 := by exact prefixLift 3399812
  have htrace : WordTrace (prefixWord ++ tailWord_3399812) baseStart_3399812 baseEnd_3399812 := by
    simpa [prefixWord, tailWord_3399812, baseEnd_3399812] using wordTrace_append hprefix tailTrace_3399812
  have hstable : (prefixWord ++ tailWord_3399812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399812).length < 2 ^ (prefixWord ++ tailWord_3399812).sum := by decide
  have hdescent : baseEnd_3399812 < baseStart_3399812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399813 : List Nat := [1, 3, 1, 1, 5, 1, 3, 3, 1, 1, 3]
def baseStart_3399813 : Nat := 118140960795 + 3399813 * 2 ^ 59
def prefixEnd_3399813 : Nat := 4983230072969 + 3 ^ 40 * 3399813 * 2
def baseEnd_3399813 : Nat := 1745738204404411949702051

theorem tailTrace_3399813 : CollatzResearch.WordTrace tailWord_3399813 prefixEnd_3399813 1745738204404411949702051 := by
  unfold tailWord_3399813
  simp only [CollatzResearch.WordTrace]
  refine ⟨124001367232065617678252093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82667578154710411785501395 124001367232065617678252093)
  ·
    refine ⟨46500512712024606629344535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124001367232065617678252093 46500512712024606629344535)
    ·
      refine ⟨69750769068036909944016803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46500512712024606629344535 69750769068036909944016803)
      ·
        refine ⟨104626153602055364916025205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69750769068036909944016803 104626153602055364916025205)
        ·
          refine ⟨9808701900192690460877363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 104626153602055364916025205 9808701900192690460877363)
          ·
            refine ⟨14713052850289035691316045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9808701900192690460877363 14713052850289035691316045)
            ·
              refine ⟨5517394818858388384243517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14713052850289035691316045 5517394818858388384243517)
              ·
                refine ⟨2069023057071895644091319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5517394818858388384243517 2069023057071895644091319)
                ·
                  refine ⟨3103534585607843466136979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2069023057071895644091319 3103534585607843466136979)
                  ·
                    refine ⟨4655301878411765199205469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3103534585607843466136979 4655301878411765199205469)
                    ·
                      refine ⟨1745738204404411949702051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4655301878411765199205469 1745738204404411949702051)
                      ·
                        rfl

theorem cell23_3399813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 3, 1, 1, 3].length) (baseStart_3399813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3399813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3399813 prefixEnd_3399813 := by exact prefixLift 3399813
  have htrace : WordTrace (prefixWord ++ tailWord_3399813) baseStart_3399813 baseEnd_3399813 := by
    simpa [prefixWord, tailWord_3399813, baseEnd_3399813] using wordTrace_append hprefix tailTrace_3399813
  have hstable : (prefixWord ++ tailWord_3399813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399813).length < 2 ^ (prefixWord ++ tailWord_3399813).sum := by decide
  have hdescent : baseEnd_3399813 < baseStart_3399813 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399829 : List Nat := [1, 3, 2, 1, 1, 1, 4, 4, 2, 4]
def baseStart_3399829 : Nat := 118140960795 + 3399829 * 2 ^ 59
def prefixEnd_3399829 : Nat := 4983230072969 + 3 ^ 40 * 3399829 * 2
def baseEnd_3399829 : Nat := 581915473364961295700659

theorem tailTrace_3399829 : CollatzResearch.WordTrace tailWord_3399829 prefixEnd_3399829 581915473364961295700659 := by
  unfold tailWord_3399829
  simp only [CollatzResearch.WordTrace]
  refine ⟨124001950800007652410834541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82667967200005101607223027 124001950800007652410834541)
  ·
    refine ⟨46500731550002869654062953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124001950800007652410834541 46500731550002869654062953)
    ·
      refine ⟨34875548662502152240547215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46500731550002869654062953 34875548662502152240547215)
      ·
        refine ⟨52313322993753228360820823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34875548662502152240547215 52313322993753228360820823)
        ·
          refine ⟨78469984490629842541231235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52313322993753228360820823 78469984490629842541231235)
          ·
            refine ⟨117704976735944763811846853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78469984490629842541231235 117704976735944763811846853)
            ·
              refine ⟨22069683137989643214721285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 117704976735944763811846853 22069683137989643214721285)
              ·
                refine ⟨4138065588373058102760241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22069683137989643214721285 4138065588373058102760241)
                ·
                  refine ⟨3103549191279793577070181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4138065588373058102760241 3103549191279793577070181)
                  ·
                    refine ⟨581915473364961295700659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3103549191279793577070181 581915473364961295700659)
                    ·
                      rfl

theorem cell23_3399829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 4, 2, 4].length) (baseStart_3399829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3399829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3399829 prefixEnd_3399829 := by exact prefixLift 3399829
  have htrace : WordTrace (prefixWord ++ tailWord_3399829) baseStart_3399829 baseEnd_3399829 := by
    simpa [prefixWord, tailWord_3399829, baseEnd_3399829] using wordTrace_append hprefix tailTrace_3399829
  have hstable : (prefixWord ++ tailWord_3399829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399829).length < 2 ^ (prefixWord ++ tailWord_3399829).sum := by decide
  have hdescent : baseEnd_3399829 < baseStart_3399829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399839 : List Nat := [1, 1, 2, 6, 1, 1, 2, 2, 1, 1, 5]
def baseStart_3399839 : Nat := 118140960795 + 3399839 * 2 ^ 59
def prefixEnd_3399839 : Nat := 4983230072969 + 3 ^ 40 * 3399839 * 2
def baseEnd_3399839 : Nat := 1745751554901428847976931

theorem tailTrace_3399839 : CollatzResearch.WordTrace tailWord_3399839 prefixEnd_3399839 1745751554901428847976931 := by
  unfold tailWord_3399839
  simp only [CollatzResearch.WordTrace]
  refine ⟨124002315529971424118698571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82668210353314282745799047 124002315529971424118698571)
  ·
    refine ⟨186003473294957136178047857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124002315529971424118698571 186003473294957136178047857)
    ·
      refine ⟨139502604971217852133535893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186003473294957136178047857 139502604971217852133535893)
      ·
        refine ⟨6539184608025836818759495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 139502604971217852133535893 6539184608025836818759495)
        ·
          refine ⟨9808776912038755228139243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6539184608025836818759495 9808776912038755228139243)
          ·
            refine ⟨14713165368058132842208865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9808776912038755228139243 14713165368058132842208865)
            ·
              refine ⟨11034874026043599631656649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14713165368058132842208865 11034874026043599631656649)
              ·
                refine ⟨8276155519532699723742487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11034874026043599631656649 8276155519532699723742487)
                ·
                  refine ⟨12414233279299049585613731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8276155519532699723742487 12414233279299049585613731)
                  ·
                    refine ⟨18621349918948574378420597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12414233279299049585613731 18621349918948574378420597)
                    ·
                      refine ⟨1745751554901428847976931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18621349918948574378420597 1745751554901428847976931)
                      ·
                        rfl

theorem cell23_3399839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_3399839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3399839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3399839 prefixEnd_3399839 := by exact prefixLift 3399839
  have htrace : WordTrace (prefixWord ++ tailWord_3399839) baseStart_3399839 baseEnd_3399839 := by
    simpa [prefixWord, tailWord_3399839, baseEnd_3399839] using wordTrace_append hprefix tailTrace_3399839
  have hstable : (prefixWord ++ tailWord_3399839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399839).length < 2 ^ (prefixWord ++ tailWord_3399839).sum := by decide
  have hdescent : baseEnd_3399839 < baseStart_3399839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399850 : List Nat := [3, 1, 5, 1, 3, 1, 1, 2, 1, 5]
def baseStart_3399850 : Nat := 118140960795 + 3399850 * 2 ^ 59
def prefixEnd_3399850 : Nat := 4983230072969 + 3 ^ 40 * 3399850 * 2
def baseEnd_3399850 : Nat := 581919067729542768313127

theorem tailTrace_3399850 : CollatzResearch.WordTrace tailWord_3399850 prefixEnd_3399850 581919067729542768313127 := by
  unfold tailWord_3399850
  simp only [CollatzResearch.WordTrace]
  refine ⟨31000679183232893249337251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82668477821954381998232669 31000679183232893249337251)
  ·
    refine ⟨46501018774849339874005877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31000679183232893249337251 46501018774849339874005877)
    ·
      refine ⟨4359470510142125613188051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46501018774849339874005877 4359470510142125613188051)
      ·
        refine ⟨6539205765213188419782077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4359470510142125613188051 6539205765213188419782077)
        ·
          refine ⟨2452202161954945657418279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6539205765213188419782077 2452202161954945657418279)
          ·
            refine ⟨3678303242932418486127419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2452202161954945657418279 3678303242932418486127419)
            ·
              refine ⟨5517454864398627729191129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3678303242932418486127419 5517454864398627729191129)
              ·
                refine ⟨4138091148298970796893347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5517454864398627729191129 4138091148298970796893347)
                ·
                  refine ⟨6207136722448456195340021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4138091148298970796893347 6207136722448456195340021)
                  ·
                    refine ⟨581919067729542768313127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6207136722448456195340021 581919067729542768313127)
                    ·
                      rfl

theorem cell23_3399850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_3399850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3399850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3399850 prefixEnd_3399850 := by exact prefixLift 3399850
  have htrace : WordTrace (prefixWord ++ tailWord_3399850) baseStart_3399850 baseEnd_3399850 := by
    simpa [prefixWord, tailWord_3399850, baseEnd_3399850] using wordTrace_append hprefix tailTrace_3399850
  have hstable : (prefixWord ++ tailWord_3399850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399850).length < 2 ^ (prefixWord ++ tailWord_3399850).sum := by decide
  have hdescent : baseEnd_3399850 < baseStart_3399850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399853 : List Nat := [1, 5, 2, 1, 2, 3, 1, 2, 1, 1, 4]
def baseStart_3399853 : Nat := 118140960795 + 3399853 * 2 ^ 59
def prefixEnd_3399853 : Nat := 4983230072969 + 3 ^ 40 * 3399853 * 2
def baseEnd_3399853 : Nat := 1745758743630591793201867

theorem tailTrace_3399853 : CollatzResearch.WordTrace tailWord_3399853 prefixEnd_3399853 1745758743630591793201867 := by
  unfold tailWord_3399853
  simp only [CollatzResearch.WordTrace]
  refine ⟨124002826151920704509708213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82668550767947136339805475 124002826151920704509708213)
  ·
    refine ⟨11625264951742566047785145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 124002826151920704509708213 11625264951742566047785145)
    ·
      refine ⟨8718948713806924535838859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11625264951742566047785145 8718948713806924535838859)
      ·
        refine ⟨13078423070710386803758289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8718948713806924535838859 13078423070710386803758289)
        ·
          refine ⟨9808817303032790102818717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13078423070710386803758289 9808817303032790102818717)
          ·
            refine ⟨3678306488637296288557019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9808817303032790102818717 3678306488637296288557019)
            ·
              refine ⟨5517459732955944432835529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3678306488637296288557019 5517459732955944432835529)
              ·
                refine ⟨4138094799716958324626647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5517459732955944432835529 4138094799716958324626647)
                ·
                  refine ⟨6207142199575437486939971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4138094799716958324626647 6207142199575437486939971)
                  ·
                    refine ⟨9310713299363156230409957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6207142199575437486939971 9310713299363156230409957)
                    ·
                      refine ⟨1745758743630591793201867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9310713299363156230409957 1745758743630591793201867)
                      ·
                        rfl

theorem cell23_3399853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_3399853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3399853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3399853 prefixEnd_3399853 := by exact prefixLift 3399853
  have htrace : WordTrace (prefixWord ++ tailWord_3399853) baseStart_3399853 baseEnd_3399853 := by
    simpa [prefixWord, tailWord_3399853, baseEnd_3399853] using wordTrace_append hprefix tailTrace_3399853
  have hstable : (prefixWord ++ tailWord_3399853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399853).length < 2 ^ (prefixWord ++ tailWord_3399853).sum := by decide
  have hdescent : baseEnd_3399853 < baseStart_3399853 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399873 : List Nat := [1, 2, 6, 1, 2, 2, 1, 1, 1, 1, 5]
def baseStart_3399873 : Nat := 118140960795 + 3399873 * 2 ^ 59
def prefixEnd_3399873 : Nat := 4983230072969 + 3 ^ 40 * 3399873 * 2
def baseEnd_3399873 : Nat := 1745769013243681714951775

theorem tailTrace_3399873 : CollatzResearch.WordTrace tailWord_3399873 prefixEnd_3399873 1745769013243681714951775 := by
  unfold tailWord_3399873
  simp only [CollatzResearch.WordTrace]
  refine ⟨124003555611848247925436273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82669037074565498616957515 124003555611848247925436273)
  ·
    refine ⟨93002666708886185944077205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124003555611848247925436273 93002666708886185944077205)
    ·
      refine ⟨4359500001979039966128619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 93002666708886185944077205 4359500001979039966128619)
      ·
        refine ⟨6539250002968559949192929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4359500001979039966128619 6539250002968559949192929)
        ·
          refine ⟨4904437502226419961894697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6539250002968559949192929 4904437502226419961894697)
          ·
            refine ⟨3678328126669814971421023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4904437502226419961894697 3678328126669814971421023)
            ·
              refine ⟨5517492190004722457131535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3678328126669814971421023 5517492190004722457131535)
              ·
                refine ⟨8276238285007083685697303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5517492190004722457131535 8276238285007083685697303)
                ·
                  refine ⟨12414357427510625528545955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8276238285007083685697303 12414357427510625528545955)
                  ·
                    refine ⟨18621536141265938292818933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12414357427510625528545955 18621536141265938292818933)
                    ·
                      refine ⟨1745769013243681714951775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18621536141265938292818933 1745769013243681714951775)
                      ·
                        rfl

theorem cell23_3399873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_3399873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3399873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3399873 prefixEnd_3399873 := by exact prefixLift 3399873
  have htrace : WordTrace (prefixWord ++ tailWord_3399873) baseStart_3399873 baseEnd_3399873 := by
    simpa [prefixWord, tailWord_3399873, baseEnd_3399873] using wordTrace_append hprefix tailTrace_3399873
  have hstable : (prefixWord ++ tailWord_3399873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399873).length < 2 ^ (prefixWord ++ tailWord_3399873).sum := by decide
  have hdescent : baseEnd_3399873 < baseStart_3399873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399896 : List Nat := [2, 1, 2, 2, 4, 1, 1, 2, 3, 3, 2]
def baseStart_3399896 : Nat := 118140960795 + 3399896 * 2 ^ 59
def prefixEnd_3399896 : Nat := 4983230072969 + 3 ^ 40 * 3399896 * 2
def baseEnd_3399896 : Nat := 1745780823298735124964169

theorem tailTrace_3399896 : CollatzResearch.WordTrace tailWord_3399896 prefixEnd_3399896 1745780823298735124964169 := by
  unfold tailWord_3399896
  simp only [CollatzResearch.WordTrace]
  refine ⟨62002197245382461426761771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82669596327176615235682361 62002197245382461426761771)
  ·
    refine ⟨93003295868073692140142657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62002197245382461426761771 93003295868073692140142657)
    ·
      refine ⟨69752471901055269105106993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93003295868073692140142657 69752471901055269105106993)
      ·
        refine ⟨52314353925791451828830245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69752471901055269105106993 52314353925791451828830245)
        ·
          refine ⟨9808941361085897217905671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52314353925791451828830245 9808941361085897217905671)
          ·
            refine ⟨14713412041628845826858507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9808941361085897217905671 14713412041628845826858507)
            ·
              refine ⟨22070118062443268740287761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14713412041628845826858507 22070118062443268740287761)
              ·
                refine ⟨16552588546832451555215821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22070118062443268740287761 16552588546832451555215821)
                ·
                  refine ⟨6207220705062169333205933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16552588546832451555215821 6207220705062169333205933)
                  ·
                    refine ⟨2327707764398313499952225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6207220705062169333205933 2327707764398313499952225)
                    ·
                      refine ⟨1745780823298735124964169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2327707764398313499952225 1745780823298735124964169)
                      ·
                        rfl

theorem cell23_3399896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 2, 3, 3, 2].length) (baseStart_3399896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3399896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3399896 prefixEnd_3399896 := by exact prefixLift 3399896
  have htrace : WordTrace (prefixWord ++ tailWord_3399896) baseStart_3399896 baseEnd_3399896 := by
    simpa [prefixWord, tailWord_3399896, baseEnd_3399896] using wordTrace_append hprefix tailTrace_3399896
  have hstable : (prefixWord ++ tailWord_3399896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399896).length < 2 ^ (prefixWord ++ tailWord_3399896).sum := by decide
  have hdescent : baseEnd_3399896 < baseStart_3399896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399930 : List Nat := [3, 1, 1, 1, 1, 7, 2, 1, 1, 3, 2]
def baseStart_3399930 : Nat := 118140960795 + 3399930 * 2 ^ 59
def prefixEnd_3399930 : Nat := 4983230072969 + 3 ^ 40 * 3399930 * 2
def baseEnd_3399930 : Nat := 1745798281640987991939013

theorem tailTrace_3399930 : CollatzResearch.WordTrace tailWord_3399930 prefixEnd_3399930 1745798281640987991939013 := by
  unfold tailWord_3399930
  simp only [CollatzResearch.WordTrace]
  refine ⟨31001408643160436665065311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82670423048427831106840829 31001408643160436665065311)
  ·
    refine ⟨46502112964740654997597967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31001408643160436665065311 46502112964740654997597967)
    ·
      refine ⟨69753169447110982496396951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46502112964740654997597967 69753169447110982496396951)
      ·
        refine ⟨104629754170666473744595427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69753169447110982496396951 104629754170666473744595427)
        ·
          refine ⟨156944631255999710616893141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104629754170666473744595427 156944631255999710616893141)
          ·
            refine ⟨3678389795062493217583433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 156944631255999710616893141 3678389795062493217583433)
            ·
              refine ⟨2758792346296869913187575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3678389795062493217583433 2758792346296869913187575)
              ·
                refine ⟨4138188519445304869781363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2758792346296869913187575 4138188519445304869781363)
                ·
                  refine ⟨6207282779167957304672045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4138188519445304869781363 6207282779167957304672045)
                  ·
                    refine ⟨2327731042187983989252017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6207282779167957304672045 2327731042187983989252017)
                    ·
                      refine ⟨1745798281640987991939013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2327731042187983989252017 1745798281640987991939013)
                      ·
                        rfl

theorem cell23_3399930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 2, 1, 1, 3, 2].length) (baseStart_3399930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3399930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3399930 prefixEnd_3399930 := by exact prefixLift 3399930
  have htrace : WordTrace (prefixWord ++ tailWord_3399930) baseStart_3399930 baseEnd_3399930 := by
    simpa [prefixWord, tailWord_3399930, baseEnd_3399930] using wordTrace_append hprefix tailTrace_3399930
  have hstable : (prefixWord ++ tailWord_3399930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399930).length < 2 ^ (prefixWord ++ tailWord_3399930).sum := by decide
  have hdescent : baseEnd_3399930 < baseStart_3399930 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399960 : List Nat := [2, 1, 2, 3, 1, 2, 5, 1, 2, 2, 2]
def baseStart_3399960 : Nat := 118140960795 + 3399960 * 2 ^ 59
def prefixEnd_3399960 : Nat := 4983230072969 + 3 ^ 40 * 3399960 * 2
def baseEnd_3399960 : Nat := 1745813686060622874563875

theorem tailTrace_3399960 : CollatzResearch.WordTrace tailWord_3399960 prefixEnd_3399960 1745813686060622874563875 := by
  unfold tailWord_3399960
  simp only [CollatzResearch.WordTrace]
  refine ⟨62003364381266530891926667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82671152508355374522568889 62003364381266530891926667)
  ·
    refine ⟨93005046571899796337890001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62003364381266530891926667 93005046571899796337890001)
    ·
      refine ⟨69753784928924847253417501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93005046571899796337890001 69753784928924847253417501)
      ·
        refine ⟨26157669348346817720031563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69753784928924847253417501 26157669348346817720031563)
        ·
          refine ⟨39236504022520226580047345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26157669348346817720031563 39236504022520226580047345)
          ·
            refine ⟨29427378016890169935035509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39236504022520226580047345 29427378016890169935035509)
            ·
              refine ⟨2758816689083453431409579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29427378016890169935035509 2758816689083453431409579)
              ·
                refine ⟨4138225033625180147114369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2758816689083453431409579 4138225033625180147114369)
                ·
                  refine ⟨3103668775218885110335777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4138225033625180147114369 3103668775218885110335777)
                  ·
                    refine ⟨2327751581414163832751833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3103668775218885110335777 2327751581414163832751833)
                    ·
                      refine ⟨1745813686060622874563875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2327751581414163832751833 1745813686060622874563875)
                      ·
                        rfl

theorem cell23_3399960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 5, 1, 2, 2, 2].length) (baseStart_3399960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3399960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3399960 prefixEnd_3399960 := by exact prefixLift 3399960
  have htrace : WordTrace (prefixWord ++ tailWord_3399960) baseStart_3399960 baseEnd_3399960 := by
    simpa [prefixWord, tailWord_3399960, baseEnd_3399960] using wordTrace_append hprefix tailTrace_3399960
  have hstable : (prefixWord ++ tailWord_3399960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399960).length < 2 ^ (prefixWord ++ tailWord_3399960).sum := by decide
  have hdescent : baseEnd_3399960 < baseStart_3399960 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3399989 : List Nat := [1, 3, 3, 1, 2, 1, 2, 2, 1, 2, 5]
def baseStart_3399989 : Nat := 118140960795 + 3399989 * 2 ^ 59
def prefixEnd_3399989 : Nat := 4983230072969 + 3 ^ 40 * 3399989 * 2
def baseEnd_3399989 : Nat := 1745828576999603261101241

theorem tailTrace_3399989 : CollatzResearch.WordTrace tailWord_3399989 prefixEnd_3399989 1745828576999603261101241 := by
  unfold tailWord_3399989
  simp only [CollatzResearch.WordTrace]
  refine ⟨124007786479427999736659021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82671857652951999824439347 124007786479427999736659021)
  ·
    refine ⟨46502919929785499901247133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124007786479427999736659021 46502919929785499901247133)
    ·
      refine ⟨17438594973669562462967675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46502919929785499901247133 17438594973669562462967675)
      ·
        refine ⟨26157892460504343694451513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17438594973669562462967675 26157892460504343694451513)
        ·
          refine ⟨19618419345378257770838635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26157892460504343694451513 19618419345378257770838635)
          ·
            refine ⟨29427629018067386656257953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19618419345378257770838635 29427629018067386656257953)
            ·
              refine ⟨22070721763550539992193465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29427629018067386656257953 22070721763550539992193465)
              ·
                refine ⟨16553041322662904994145099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22070721763550539992193465 16553041322662904994145099)
                ·
                  refine ⟨24829561983994357491217649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16553041322662904994145099 24829561983994357491217649)
                  ·
                    refine ⟨18622171487995768118413237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24829561983994357491217649 18622171487995768118413237)
                    ·
                      refine ⟨1745828576999603261101241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18622171487995768118413237 1745828576999603261101241)
                      ·
                        rfl

theorem cell23_3399989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_3399989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3399989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3399989 prefixEnd_3399989 := by exact prefixLift 3399989
  have htrace : WordTrace (prefixWord ++ tailWord_3399989) baseStart_3399989 baseEnd_3399989 := by
    simpa [prefixWord, tailWord_3399989, baseEnd_3399989] using wordTrace_append hprefix tailTrace_3399989
  have hstable : (prefixWord ++ tailWord_3399989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3399989).length < 2 ^ (prefixWord ++ tailWord_3399989).sum := by decide
  have hdescent : baseEnd_3399989 < baseStart_3399989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3399989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3400019 : List Nat := [1, 1, 1, 2, 1, 1, 4, 4, 1, 4, 3]
def baseStart_3400019 : Nat := 118140960795 + 3400019 * 2 ^ 59
def prefixEnd_3400019 : Nat := 4983230072969 + 3 ^ 40 * 3400019 * 2
def baseEnd_3400019 : Nat := 1745843981419238143726103

theorem tailTrace_3400019 : CollatzResearch.WordTrace tailWord_3400019 prefixEnd_3400019 1745843981419238143726103 := by
  unfold tailWord_3400019
  simp only [CollatzResearch.WordTrace]
  refine ⟨124008880669319314860251111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82672587112879543240167407 124008880669319314860251111)
  ·
    refine ⟨186013321003978972290376667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124008880669319314860251111 186013321003978972290376667)
    ·
      refine ⟨279019981505968458435565001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186013321003978972290376667 279019981505968458435565001)
      ·
        refine ⟨209264986129476343826673751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279019981505968458435565001 209264986129476343826673751)
        ·
          refine ⟨313897479194214515740010627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209264986129476343826673751 313897479194214515740010627)
          ·
            refine ⟨470846218791321773610015941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313897479194214515740010627 470846218791321773610015941)
            ·
              refine ⟨88283666023372832551877989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 470846218791321773610015941 88283666023372832551877989)
              ·
                refine ⟨16553187379382406103477123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88283666023372832551877989 16553187379382406103477123)
                ·
                  refine ⟨24829781069073609155215685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16553187379382406103477123 24829781069073609155215685)
                  ·
                    refine ⟨4655583950451301716602941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24829781069073609155215685 4655583950451301716602941)
                    ·
                      refine ⟨1745843981419238143726103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4655583950451301716602941 1745843981419238143726103)
                      ·
                        rfl

theorem cell23_3400019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 4, 1, 4, 3].length) (baseStart_3400019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3400019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3400019 prefixEnd_3400019 := by exact prefixLift 3400019
  have htrace : WordTrace (prefixWord ++ tailWord_3400019) baseStart_3400019 baseEnd_3400019 := by
    simpa [prefixWord, tailWord_3400019, baseEnd_3400019] using wordTrace_append hprefix tailTrace_3400019
  have hstable : (prefixWord ++ tailWord_3400019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3400019).length < 2 ^ (prefixWord ++ tailWord_3400019).sum := by decide
  have hdescent : baseEnd_3400019 < baseStart_3400019 := by decide
  rcases family_descends (prefixWord ++ tailWord_3400019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3400053 : List Nat := [1, 3, 4, 1, 2, 1, 2, 2, 2, 2, 3]
def baseStart_3400053 : Nat := 118140960795 + 3400053 * 2 ^ 59
def prefixEnd_3400053 : Nat := 4983230072969 + 3 ^ 40 * 3400053 * 2
def baseEnd_3400053 : Nat := 1745861439761491010700947

theorem tailTrace_3400053 : CollatzResearch.WordTrace tailWord_3400053 prefixEnd_3400053 1745861439761491010700947 := by
  unfold tailWord_3400053
  simp only [CollatzResearch.WordTrace]
  refine ⟨124010120751196138666988813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82673413834130759111325875 124010120751196138666988813)
  ·
    refine ⟨46503795281698552000120805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124010120751196138666988813 46503795281698552000120805)
    ·
      refine ⟨8719461615318478500022651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46503795281698552000120805 8719461615318478500022651)
      ·
        refine ⟨13079192422977717750033977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8719461615318478500022651 13079192422977717750033977)
        ·
          refine ⟨9809394317233288312525483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13079192422977717750033977 9809394317233288312525483)
          ·
            refine ⟨14714091475849932468788225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9809394317233288312525483 14714091475849932468788225)
            ·
              refine ⟨11035568606887449351591169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14714091475849932468788225 11035568606887449351591169)
              ·
                refine ⟨8276676455165587013693377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11035568606887449351591169 8276676455165587013693377)
                ·
                  refine ⟨6207507341374190260270033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8276676455165587013693377 6207507341374190260270033)
                  ·
                    refine ⟨4655630506030642695202525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6207507341374190260270033 4655630506030642695202525)
                    ·
                      refine ⟨1745861439761491010700947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4655630506030642695202525 1745861439761491010700947)
                      ·
                        rfl

theorem cell23_3400053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_3400053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3400053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3400053 prefixEnd_3400053 := by exact prefixLift 3400053
  have htrace : WordTrace (prefixWord ++ tailWord_3400053) baseStart_3400053 baseEnd_3400053 := by
    simpa [prefixWord, tailWord_3400053, baseEnd_3400053] using wordTrace_append hprefix tailTrace_3400053
  have hstable : (prefixWord ++ tailWord_3400053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3400053).length < 2 ^ (prefixWord ++ tailWord_3400053).sum := by decide
  have hdescent : baseEnd_3400053 < baseStart_3400053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3400053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3400100 : List Nat := [2, 3, 1, 2, 1, 1, 3, 5, 1, 1, 3]
def baseStart_3400100 : Nat := 118140960795 + 3400100 * 2 ^ 59
def prefixEnd_3400100 : Nat := 4983230072969 + 3 ^ 40 * 3400100 * 2
def baseEnd_3400100 : Nat := 1745885573352252326813231

theorem tailTrace_3400100 : CollatzResearch.WordTrace tailWord_3400100 prefixEnd_3400100 1745885573352252326813231 := by
  unfold tailWord_3400100
  simp only [CollatzResearch.WordTrace]
  refine ⟨62005917491012932846974877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82674556654683910462633169 62005917491012932846974877)
  ·
    refine ⟨23252219059129849817615579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62005917491012932846974877 23252219059129849817615579)
    ·
      refine ⟨34878328588694774726423369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23252219059129849817615579 34878328588694774726423369)
      ·
        refine ⟨26158746441521081044817527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34878328588694774726423369 26158746441521081044817527)
        ·
          refine ⟨39238119662281621567226291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26158746441521081044817527 39238119662281621567226291)
          ·
            refine ⟨58857179493422432350839437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39238119662281621567226291 58857179493422432350839437)
            ·
              refine ⟨22071442310033412131564789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58857179493422432350839437 22071442310033412131564789)
              ·
                refine ⟨2069197716565632387334199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22071442310033412131564789 2069197716565632387334199)
                ·
                  refine ⟨3103796574848448581001299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2069197716565632387334199 3103796574848448581001299)
                  ·
                    refine ⟨4655694862272672871501949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3103796574848448581001299 4655694862272672871501949)
                    ·
                      refine ⟨1745885573352252326813231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4655694862272672871501949 1745885573352252326813231)
                      ·
                        rfl

theorem cell23_3400100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 5, 1, 1, 3].length) (baseStart_3400100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3400100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3400100 prefixEnd_3400100 := by exact prefixLift 3400100
  have htrace : WordTrace (prefixWord ++ tailWord_3400100) baseStart_3400100 baseEnd_3400100 := by
    simpa [prefixWord, tailWord_3400100, baseEnd_3400100] using wordTrace_append hprefix tailTrace_3400100
  have hstable : (prefixWord ++ tailWord_3400100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3400100).length < 2 ^ (prefixWord ++ tailWord_3400100).sum := by decide
  have hdescent : baseEnd_3400100 < baseStart_3400100 := by decide
  rcases family_descends (prefixWord ++ tailWord_3400100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3400103 : List Nat := [1, 1, 6, 1, 1, 3, 1, 3, 1, 5]
def baseStart_3400103 : Nat := 118140960795 + 3400103 * 2 ^ 59
def prefixEnd_3400103 : Nat := 4983230072969 + 3 ^ 40 * 3400103 * 2
def baseEnd_3400103 : Nat := 581962371264738605025239

theorem tailTrace_3400103 : CollatzResearch.WordTrace tailWord_3400103 prefixEnd_3400103 581962371264738605025239 := by
  unfold tailWord_3400103
  simp only [CollatzResearch.WordTrace]
  refine ⟨124011944401014997206308963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82674629600676664804205975 124011944401014997206308963)
  ·
    refine ⟨186017916601522495809463445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124011944401014997206308963 186017916601522495809463445)
    ·
      refine ⟨8719589840696366991068599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 186017916601522495809463445 8719589840696366991068599)
      ·
        refine ⟨13079384761044550486602899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8719589840696366991068599 13079384761044550486602899)
        ·
          refine ⟨19619077141566825729904349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13079384761044550486602899 19619077141566825729904349)
          ·
            refine ⟨7357153928087559648714131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19619077141566825729904349 7357153928087559648714131)
            ·
              refine ⟨11035730892131339473071197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7357153928087559648714131 11035730892131339473071197)
              ·
                refine ⟨4138399084549252302401699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11035730892131339473071197 4138399084549252302401699)
                ·
                  refine ⟨6207598626823878453602549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4138399084549252302401699 6207598626823878453602549)
                  ·
                    refine ⟨581962371264738605025239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6207598626823878453602549 581962371264738605025239)
                    ·
                      rfl

theorem cell23_3400103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_3400103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3400103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3400103 prefixEnd_3400103 := by exact prefixLift 3400103
  have htrace : WordTrace (prefixWord ++ tailWord_3400103) baseStart_3400103 baseEnd_3400103 := by
    simpa [prefixWord, tailWord_3400103, baseEnd_3400103] using wordTrace_append hprefix tailTrace_3400103
  have hstable : (prefixWord ++ tailWord_3400103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3400103).length < 2 ^ (prefixWord ++ tailWord_3400103).sum := by decide
  have hdescent : baseEnd_3400103 < baseStart_3400103 := by decide
  rcases family_descends (prefixWord ++ tailWord_3400103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3400126 : List Nat := [4, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5]
def baseStart_3400126 : Nat := 118140960795 + 3400126 * 2 ^ 59
def prefixEnd_3400126 : Nat := 4983230072969 + 3 ^ 40 * 3400126 * 2
def baseEnd_3400126 : Nat := 1745898923849269225088111

theorem tailTrace_3400126 : CollatzResearch.WordTrace tailWord_3400126 prefixEnd_3400126 1745898923849269225088111 := by
  unfold tailWord_3400126
  simp only [CollatzResearch.WordTrace]
  refine ⟨15501597909991459016799529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82675188853287781422930821 15501597909991459016799529)
  ·
    refine ⟨11626198432493594262599647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15501597909991459016799529 11626198432493594262599647)
    ·
      refine ⟨17439297648740391393899471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11626198432493594262599647 17439297648740391393899471)
      ·
        refine ⟨26158946473110587090849207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17439297648740391393899471 26158946473110587090849207)
        ·
          refine ⟨39238419709665880636273811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26158946473110587090849207 39238419709665880636273811)
          ·
            refine ⟨58857629564498820954410717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39238419709665880636273811 58857629564498820954410717)
            ·
              refine ⟨22071611086687057857904019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58857629564498820954410717 22071611086687057857904019)
              ·
                refine ⟨33107416630030586786856029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22071611086687057857904019 33107416630030586786856029)
                ·
                  refine ⟨12415281236261470045071011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33107416630030586786856029 12415281236261470045071011)
                  ·
                    refine ⟨18622921854392205067606517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12415281236261470045071011 18622921854392205067606517)
                    ·
                      refine ⟨1745898923849269225088111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18622921854392205067606517 1745898923849269225088111)
                      ·
                        rfl

theorem cell23_3400126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_3400126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3400126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3400126 prefixEnd_3400126 := by exact prefixLift 3400126
  have htrace : WordTrace (prefixWord ++ tailWord_3400126) baseStart_3400126 baseEnd_3400126 := by
    simpa [prefixWord, tailWord_3400126, baseEnd_3400126] using wordTrace_append hprefix tailTrace_3400126
  have hstable : (prefixWord ++ tailWord_3400126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3400126).length < 2 ^ (prefixWord ++ tailWord_3400126).sum := by decide
  have hdescent : baseEnd_3400126 < baseStart_3400126 := by decide
  rcases family_descends (prefixWord ++ tailWord_3400126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3400136 : List Nat := [2, 1, 3, 1, 3, 3, 1, 1, 1, 1, 6]
def baseStart_3400136 : Nat := 118140960795 + 3400136 * 2 ^ 59
def prefixEnd_3400136 : Nat := 4983230072969 + 3 ^ 40 * 3400136 * 2
def baseEnd_3400136 : Nat := 1745904058655814185963065

theorem tailTrace_3400136 : CollatzResearch.WordTrace tailWord_3400136 prefixEnd_3400136 1745904058655814185963065 := by
  unfold tailWord_3400136
  simp only [CollatzResearch.WordTrace]
  refine ⟨62006574004947721921130131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82675432006596962561506841 62006574004947721921130131)
  ·
    refine ⟨93009861007421582881695197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62006574004947721921130131 93009861007421582881695197)
    ·
      refine ⟨34878697877783093580635699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93009861007421582881695197 34878697877783093580635699)
      ·
        refine ⟨52318046816674640370953549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34878697877783093580635699 52318046816674640370953549)
        ·
          refine ⟨19619267556252990139107581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52318046816674640370953549 19619267556252990139107581)
          ·
            refine ⟨7357225333594871302165343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19619267556252990139107581 7357225333594871302165343)
            ·
              refine ⟨11035838000392306953248015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7357225333594871302165343 11035838000392306953248015)
              ·
                refine ⟨16553757000588460429872023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11035838000392306953248015 16553757000588460429872023)
                ·
                  refine ⟨24830635500882690644808035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16553757000588460429872023 24830635500882690644808035)
                  ·
                    refine ⟨37245953251324035967212053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24830635500882690644808035 37245953251324035967212053)
                    ·
                      refine ⟨1745904058655814185963065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37245953251324035967212053 1745904058655814185963065)
                      ·
                        rfl

theorem cell23_3400136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 1, 1, 1, 6].length) (baseStart_3400136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3400136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3400136 prefixEnd_3400136 := by exact prefixLift 3400136
  have htrace : WordTrace (prefixWord ++ tailWord_3400136) baseStart_3400136 baseEnd_3400136 := by
    simpa [prefixWord, tailWord_3400136, baseEnd_3400136] using wordTrace_append hprefix tailTrace_3400136
  have hstable : (prefixWord ++ tailWord_3400136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3400136).length < 2 ^ (prefixWord ++ tailWord_3400136).sum := by decide
  have hdescent : baseEnd_3400136 < baseStart_3400136 := by decide
  rcases family_descends (prefixWord ++ tailWord_3400136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3400140 : List Nat := [2, 2, 1, 4, 3, 1, 2, 2, 1, 1, 4]
def baseStart_3400140 : Nat := 118140960795 + 3400140 * 2 ^ 59
def prefixEnd_3400140 : Nat := 4983230072969 + 3 ^ 40 * 3400140 * 2
def baseEnd_3400140 : Nat := 1745906112578432170313047

theorem tailTrace_3400140 : CollatzResearch.WordTrace tailWord_3400140 prefixEnd_3400140 1745906112578432170313047 := by
  unfold tailWord_3400140
  simp only [CollatzResearch.WordTrace]
  refine ⟨62006646950940476262702937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82675529267920635016937249 62006646950940476262702937)
  ·
    refine ⟨46504985213205357197027203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62006646950940476262702937 46504985213205357197027203)
    ·
      refine ⟨69757477819808035795540805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46504985213205357197027203 69757477819808035795540805)
      ·
        refine ⟨13079527091214006711663901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69757477819808035795540805 13079527091214006711663901)
        ·
          refine ⟨4904822659205252516873963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13079527091214006711663901 4904822659205252516873963)
          ·
            refine ⟨7357233988807878775310945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4904822659205252516873963 7357233988807878775310945)
            ·
              refine ⟨5517925491605909081483209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7357233988807878775310945 5517925491605909081483209)
              ·
                refine ⟨4138444118704431811112407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5517925491605909081483209 4138444118704431811112407)
                ·
                  refine ⟨6207666178056647716668611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4138444118704431811112407 6207666178056647716668611)
                  ·
                    refine ⟨9311499267084971575002917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6207666178056647716668611 9311499267084971575002917)
                    ·
                      refine ⟨1745906112578432170313047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9311499267084971575002917 1745906112578432170313047)
                      ·
                        rfl

theorem cell23_3400140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_3400140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3400140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3400140 prefixEnd_3400140 := by exact prefixLift 3400140
  have htrace : WordTrace (prefixWord ++ tailWord_3400140) baseStart_3400140 baseEnd_3400140 := by
    simpa [prefixWord, tailWord_3400140, baseEnd_3400140] using wordTrace_append hprefix tailTrace_3400140
  have hstable : (prefixWord ++ tailWord_3400140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3400140).length < 2 ^ (prefixWord ++ tailWord_3400140).sum := by decide
  have hdescent : baseEnd_3400140 < baseStart_3400140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3400140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3400163 : List Nat := [1, 1, 1, 6, 4, 1, 9]
def baseStart_3400163 : Nat := 118140960795 + 3400163 * 2 ^ 59
def prefixEnd_3400163 : Nat := 4983230072969 + 3 ^ 40 * 3400163 * 2
def baseEnd_3400163 : Nat := 21554542254734389880561

theorem tailTrace_3400163 : CollatzResearch.WordTrace tailWord_3400163 prefixEnd_3400163 21554542254734389880561 := by
  unfold tailWord_3400163
  simp only [CollatzResearch.WordTrace]
  refine ⟨124014132780797627453493143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82676088520531751635662095 124014132780797627453493143)
  ·
    refine ⟨186021199171196441180239715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124014132780797627453493143 186021199171196441180239715)
    ·
      refine ⟨279031798756794661770359573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186021199171196441180239715 279031798756794661770359573)
      ·
        refine ⟨13079615566724749770485605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 279031798756794661770359573 13079615566724749770485605)
        ·
          refine ⟨2452427918760890581966051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13079615566724749770485605 2452427918760890581966051)
          ·
            refine ⟨3678641878141335872949077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2452427918760890581966051 3678641878141335872949077)
            ·
              refine ⟨21554542254734389880561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3678641878141335872949077 21554542254734389880561)
              ·
                rfl

theorem cell23_3400163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 9].length) (baseStart_3400163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3400163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3400163 prefixEnd_3400163 := by exact prefixLift 3400163
  have htrace : WordTrace (prefixWord ++ tailWord_3400163) baseStart_3400163 baseEnd_3400163 := by
    simpa [prefixWord, tailWord_3400163, baseEnd_3400163] using wordTrace_append hprefix tailTrace_3400163
  have hstable : (prefixWord ++ tailWord_3400163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3400163).length < 2 ^ (prefixWord ++ tailWord_3400163).sum := by decide
  have hdescent : baseEnd_3400163 < baseStart_3400163 := by decide
  rcases family_descends (prefixWord ++ tailWord_3400163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3400194 : List Nat := [3, 4, 1, 2, 2, 2, 1, 2, 1, 2, 3]
def baseStart_3400194 : Nat := 118140960795 + 3400194 * 2 ^ 59
def prefixEnd_3400194 : Nat := 4983230072969 + 3 ^ 40 * 3400194 * 2
def baseEnd_3400194 : Nat := 1745933840533774959037799

theorem tailTrace_3400194 : CollatzResearch.WordTrace tailWord_3400194 prefixEnd_3400194 1745933840533774959037799 := by
  unfold tailWord_3400194
  simp only [CollatzResearch.WordTrace]
  refine ⟨31003815860921329936967909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82676842295790213165247757 31003815860921329936967909)
  ·
    refine ⟨5813215473922749363181483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31003815860921329936967909 5813215473922749363181483)
    ·
      refine ⟨8719823210884124044772225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5813215473922749363181483 8719823210884124044772225)
      ·
        refine ⟨6539867408163093033579169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8719823210884124044772225 6539867408163093033579169)
        ·
          refine ⟨4904900556122319775184377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6539867408163093033579169 4904900556122319775184377)
          ·
            refine ⟨3678675417091739831388283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4904900556122319775184377 3678675417091739831388283)
            ·
              refine ⟨5518013125637609747082425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3678675417091739831388283 5518013125637609747082425)
              ·
                refine ⟨4138509844228207310311819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5518013125637609747082425 4138509844228207310311819)
                ·
                  refine ⟨6207764766342310965467729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4138509844228207310311819 6207764766342310965467729)
                  ·
                    refine ⟨4655823574756733224100797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6207764766342310965467729 4655823574756733224100797)
                    ·
                      refine ⟨1745933840533774959037799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4655823574756733224100797 1745933840533774959037799)
                      ·
                        rfl

theorem cell23_3400194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_3400194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3400194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3400194 prefixEnd_3400194 := by exact prefixLift 3400194
  have htrace : WordTrace (prefixWord ++ tailWord_3400194) baseStart_3400194 baseEnd_3400194 := by
    simpa [prefixWord, tailWord_3400194, baseEnd_3400194] using wordTrace_append hprefix tailTrace_3400194
  have hstable : (prefixWord ++ tailWord_3400194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3400194).length < 2 ^ (prefixWord ++ tailWord_3400194).sum := by decide
  have hdescent : baseEnd_3400194 < baseStart_3400194 := by decide
  rcases family_descends (prefixWord ++ tailWord_3400194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3400226 : List Nat := [3, 3, 1, 1, 1, 1, 1, 1, 2, 3, 6]
def baseStart_3400226 : Nat := 118140960795 + 3400226 * 2 ^ 59
def prefixEnd_3400226 : Nat := 4983230072969 + 3 ^ 40 * 3400226 * 2
def baseEnd_3400226 : Nat := 1745950271914718833837651

theorem tailTrace_3400226 : CollatzResearch.WordTrace tailWord_3400226 prefixEnd_3400226 1745950271914718833837651 := by
  unfold tailWord_3400226
  simp only [CollatzResearch.WordTrace]
  refine ⟨31004107644892347303259133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82677620386379592808691021 31004107644892347303259133)
  ·
    refine ⟨11626540366834630238722175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31004107644892347303259133 11626540366834630238722175)
    ·
      refine ⟨17439810550251945358083263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11626540366834630238722175 17439810550251945358083263)
      ·
        refine ⟨26159715825377918037124895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17439810550251945358083263 26159715825377918037124895)
        ·
          refine ⟨39239573738066877055687343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26159715825377918037124895 39239573738066877055687343)
          ·
            refine ⟨58859360607100315583531015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39239573738066877055687343 58859360607100315583531015)
            ·
              refine ⟨88289040910650473375296523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58859360607100315583531015 88289040910650473375296523)
              ·
                refine ⟨132433561365975710062944785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88289040910650473375296523 132433561365975710062944785)
                ·
                  refine ⟨99325171024481782547208589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 132433561365975710062944785 99325171024481782547208589)
                  ·
                    refine ⟨37246939134180668455203221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 99325171024481782547208589 37246939134180668455203221)
                    ·
                      refine ⟨1745950271914718833837651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37246939134180668455203221 1745950271914718833837651)
                      ·
                        rfl

theorem cell23_3400226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_3400226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3400226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3400226 prefixEnd_3400226 := by exact prefixLift 3400226
  have htrace : WordTrace (prefixWord ++ tailWord_3400226) baseStart_3400226 baseEnd_3400226 := by
    simpa [prefixWord, tailWord_3400226, baseEnd_3400226] using wordTrace_append hprefix tailTrace_3400226
  have hstable : (prefixWord ++ tailWord_3400226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3400226).length < 2 ^ (prefixWord ++ tailWord_3400226).sum := by decide
  have hdescent : baseEnd_3400226 < baseStart_3400226 := by decide
  rcases family_descends (prefixWord ++ tailWord_3400226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3400253 : List Nat := [1, 4, 1, 3, 2, 2, 1, 2, 7]
def baseStart_3400253 : Nat := 118140960795 + 3400253 * 2 ^ 59
def prefixEnd_3400253 : Nat := 4983230072969 + 3 ^ 40 * 3400253 * 2
def baseEnd_3400253 : Nat := 193996015099154469800003

theorem tailTrace_3400253 : CollatzResearch.WordTrace tailWord_3400253 prefixEnd_3400253 193996015099154469800003 := by
  unfold tailWord_3400253
  simp only [CollatzResearch.WordTrace]
  refine ⟨124017415350471572824269413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82678276900314381882846275 124017415350471572824269413)
  ·
    refine ⟨23253265378213419904550515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124017415350471572824269413 23253265378213419904550515)
    ·
      refine ⟨34879898067320129856825773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23253265378213419904550515 34879898067320129856825773)
      ·
        refine ⟨13079961775245048696309665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34879898067320129856825773 13079961775245048696309665)
        ·
          refine ⟨9809971331433786522232249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13079961775245048696309665 9809971331433786522232249)
          ·
            refine ⟨7357478498575339891674187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9809971331433786522232249 7357478498575339891674187)
            ·
              refine ⟨11036217747863009837511281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7357478498575339891674187 11036217747863009837511281)
              ·
                refine ⟨8277163310897257378133461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11036217747863009837511281 8277163310897257378133461)
                ·
                  refine ⟨193996015099154469800003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8277163310897257378133461 193996015099154469800003)
                  ·
                    rfl

theorem cell23_3400253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 2, 7].length) (baseStart_3400253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3400253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3400253 prefixEnd_3400253 := by exact prefixLift 3400253
  have htrace : WordTrace (prefixWord ++ tailWord_3400253) baseStart_3400253 baseEnd_3400253 := by
    simpa [prefixWord, tailWord_3400253, baseEnd_3400253] using wordTrace_append hprefix tailTrace_3400253
  have hstable : (prefixWord ++ tailWord_3400253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3400253).length < 2 ^ (prefixWord ++ tailWord_3400253).sum := by decide
  have hdescent : baseEnd_3400253 < baseStart_3400253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3400253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3400323 : List Nat := [1, 1, 1, 3, 3, 1, 4, 1, 1, 4, 3]
def baseStart_3400323 : Nat := 118140960795 + 3400323 * 2 ^ 59
def prefixEnd_3400323 : Nat := 4983230072969 + 3 ^ 40 * 3400323 * 2
def baseEnd_3400323 : Nat := 1746000079538204954324705

theorem tailTrace_3400323 : CollatzResearch.WordTrace tailWord_3400323 prefixEnd_3400323 1746000079538204954324705 := by
  unfold tailWord_3400323
  simp only [CollatzResearch.WordTrace]
  refine ⟨124019968460217974779317623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82679978973478649852878415 124019968460217974779317623)
  ·
    refine ⟨186029952690326962168976435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124019968460217974779317623 186029952690326962168976435)
    ·
      refine ⟨279044929035490443253464653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186029952690326962168976435 279044929035490443253464653)
      ·
        refine ⟨104641848388308916220049245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 279044929035490443253464653 104641848388308916220049245)
        ·
          refine ⟨39240693145615843582518467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104641848388308916220049245 39240693145615843582518467)
          ·
            refine ⟨58861039718423765373777701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39240693145615843582518467 58861039718423765373777701)
            ·
              refine ⟨11036444947204456007583319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58861039718423765373777701 11036444947204456007583319)
              ·
                refine ⟨16554667420806684011374979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11036444947204456007583319 16554667420806684011374979)
                ·
                  refine ⟨24832001131210026017062469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16554667420806684011374979 24832001131210026017062469)
                  ·
                    refine ⟨4656000212101879878199213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24832001131210026017062469 4656000212101879878199213)
                    ·
                      refine ⟨1746000079538204954324705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4656000212101879878199213 1746000079538204954324705)
                      ·
                        rfl

theorem cell23_3400323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 1, 1, 4, 3].length) (baseStart_3400323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3400323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3400323 prefixEnd_3400323 := by exact prefixLift 3400323
  have htrace : WordTrace (prefixWord ++ tailWord_3400323) baseStart_3400323 baseEnd_3400323 := by
    simpa [prefixWord, tailWord_3400323, baseEnd_3400323] using wordTrace_append hprefix tailTrace_3400323
  have hstable : (prefixWord ++ tailWord_3400323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3400323).length < 2 ^ (prefixWord ++ tailWord_3400323).sum := by decide
  have hdescent : baseEnd_3400323 < baseStart_3400323 := by decide
  rcases family_descends (prefixWord ++ tailWord_3400323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3400343 : List Nat := [1, 1, 3, 3, 2, 1, 2, 4, 6]
def baseStart_3400343 : Nat := 118140960795 + 3400343 * 2 ^ 59
def prefixEnd_3400343 : Nat := 4983230072969 + 3 ^ 40 * 3400343 * 2
def baseEnd_3400343 : Nat := 194001149905699430674957

theorem tailTrace_3400343 : CollatzResearch.WordTrace tailWord_3400343 prefixEnd_3400343 194001149905699430674957 := by
  unfold tailWord_3400343
  simp only [CollatzResearch.WordTrace]
  refine ⟨124020697920145518195045683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82680465280097012130030455 124020697920145518195045683)
  ·
    refine ⟨186031046880218277292568525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124020697920145518195045683 186031046880218277292568525)
    ·
      refine ⟨69761642580081853984713197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186031046880218277292568525 69761642580081853984713197)
      ·
        refine ⟨26160615967530695244267449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69761642580081853984713197 26160615967530695244267449)
        ·
          refine ⟨19620461975648021433200587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26160615967530695244267449 19620461975648021433200587)
          ·
            refine ⟨29430692963472032149800881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19620461975648021433200587 29430692963472032149800881)
            ·
              refine ⟨22073019722604024112350661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29430692963472032149800881 22073019722604024112350661)
              ·
                refine ⟨4138691197988254521065749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22073019722604024112350661 4138691197988254521065749)
                ·
                  refine ⟨194001149905699430674957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4138691197988254521065749 194001149905699430674957)
                  ·
                    rfl

theorem cell23_3400343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 4, 6].length) (baseStart_3400343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3400343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3400343 prefixEnd_3400343 := by exact prefixLift 3400343
  have htrace : WordTrace (prefixWord ++ tailWord_3400343) baseStart_3400343 baseEnd_3400343 := by
    simpa [prefixWord, tailWord_3400343, baseEnd_3400343] using wordTrace_append hprefix tailTrace_3400343
  have hstable : (prefixWord ++ tailWord_3400343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3400343).length < 2 ^ (prefixWord ++ tailWord_3400343).sum := by decide
  have hdescent : baseEnd_3400343 < baseStart_3400343 := by decide
  rcases family_descends (prefixWord ++ tailWord_3400343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3400370 : List Nat := [3, 2, 1, 1, 1, 2, 1, 3, 5, 1, 3]
def baseStart_3400370 : Nat := 118140960795 + 3400370 * 2 ^ 59
def prefixEnd_3400370 : Nat := 4983230072969 + 3 ^ 40 * 3400370 * 2
def baseEnd_3400370 : Nat := 1746024213128966270436989

theorem tailTrace_3400370 : CollatzResearch.WordTrace tailWord_3400370 prefixEnd_3400370 1746024213128966270436989 := by
  unfold tailWord_3400370
  simp only [CollatzResearch.WordTrace]
  refine ⟨31005420672761925451569641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82681121794031801204185709 31005420672761925451569641)
  ·
    refine ⟨23254065504571444088677231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31005420672761925451569641 23254065504571444088677231)
    ·
      refine ⟨34881098256857166133015847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23254065504571444088677231 34881098256857166133015847)
      ·
        refine ⟨52321647385285749199523771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34881098256857166133015847 52321647385285749199523771)
        ·
          refine ⟨78482471077928623799285657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52321647385285749199523771 78482471077928623799285657)
          ·
            refine ⟨58861853308446467849464243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78482471077928623799285657 58861853308446467849464243)
            ·
              refine ⟨88292779962669701774196365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58861853308446467849464243 88292779962669701774196365)
              ·
                refine ⟨33109792486001138165323637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88292779962669701774196365 33109792486001138165323637)
                ·
                  refine ⟨3104043045562606702999091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33109792486001138165323637 3104043045562606702999091)
                  ·
                    refine ⟨4656064568343910054498637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3104043045562606702999091 4656064568343910054498637)
                    ·
                      refine ⟨1746024213128966270436989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4656064568343910054498637 1746024213128966270436989)
                      ·
                        rfl

theorem cell23_3400370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 5, 1, 3].length) (baseStart_3400370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3400370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3400370 prefixEnd_3400370 := by exact prefixLift 3400370
  have htrace : WordTrace (prefixWord ++ tailWord_3400370) baseStart_3400370 baseEnd_3400370 := by
    simpa [prefixWord, tailWord_3400370, baseEnd_3400370] using wordTrace_append hprefix tailTrace_3400370
  have hstable : (prefixWord ++ tailWord_3400370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3400370).length < 2 ^ (prefixWord ++ tailWord_3400370).sum := by decide
  have hdescent : baseEnd_3400370 < baseStart_3400370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3400370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3400420 : List Nat := [2, 3, 1, 1, 1, 5, 2, 1, 1, 6]
def baseStart_3400420 : Nat := 118140960795 + 3400420 * 2 ^ 59
def prefixEnd_3400420 : Nat := 4983230072969 + 3 ^ 40 * 3400420 * 2
def baseEnd_3400420 : Nat := 582016629053897024937253

theorem tailTrace_3400420 : CollatzResearch.WordTrace tailWord_3400420 prefixEnd_3400420 582016629053897024937253 := by
  unfold tailWord_3400420
  simp only [CollatzResearch.WordTrace]
  refine ⟨62011753170433280172799357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82682337560577706897065809 62011753170433280172799357)
  ·
    refine ⟨23254407438912480064799759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62011753170433280172799357 23254407438912480064799759)
    ·
      refine ⟨34881611158368720097199639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23254407438912480064799759 34881611158368720097199639)
      ·
        refine ⟨52322416737553080145799459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34881611158368720097199639 52322416737553080145799459)
        ·
          refine ⟨78483625106329620218699189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52322416737553080145799459 78483625106329620218699189)
          ·
            refine ⟨7357839853718401895503049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 78483625106329620218699189 7357839853718401895503049)
            ·
              refine ⟨5518379890288801421627287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7357839853718401895503049 5518379890288801421627287)
              ·
                refine ⟨8277569835433202132440931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5518379890288801421627287 8277569835433202132440931)
                ·
                  refine ⟨12416354753149803198661397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8277569835433202132440931 12416354753149803198661397)
                  ·
                    refine ⟨582016629053897024937253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12416354753149803198661397 582016629053897024937253)
                    ·
                      rfl

theorem cell23_3400420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 1, 1, 6].length) (baseStart_3400420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3400420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3400420 prefixEnd_3400420 := by exact prefixLift 3400420
  have htrace : WordTrace (prefixWord ++ tailWord_3400420) baseStart_3400420 baseEnd_3400420 := by
    simpa [prefixWord, tailWord_3400420, baseEnd_3400420] using wordTrace_append hprefix tailTrace_3400420
  have hstable : (prefixWord ++ tailWord_3400420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3400420).length < 2 ^ (prefixWord ++ tailWord_3400420).sum := by decide
  have hdescent : baseEnd_3400420 < baseStart_3400420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3400420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3400443 : List Nat := [1, 1, 1, 1, 1, 3, 1, 2, 2, 7, 3]
def baseStart_3400443 : Nat := 118140960795 + 3400443 * 2 ^ 59
def prefixEnd_3400443 : Nat := 4983230072969 + 3 ^ 40 * 3400443 * 2
def baseEnd_3400443 : Nat := 1746061697216744484824153

theorem tailTrace_3400443 : CollatzResearch.WordTrace tailWord_3400443 prefixEnd_3400443 1746061697216744484824153 := by
  unfold tailWord_3400443
  simp only [CollatzResearch.WordTrace]
  refine ⟨124024345219783235273685983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82682896813188823515790655 124024345219783235273685983)
  ·
    refine ⟨186036517829674852910528975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124024345219783235273685983 186036517829674852910528975)
    ·
      refine ⟨279054776744512279365793463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186036517829674852910528975 279054776744512279365793463)
      ·
        refine ⟨418582165116768419048690195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279054776744512279365793463 418582165116768419048690195)
        ·
          refine ⟨627873247675152628573035293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 418582165116768419048690195 627873247675152628573035293)
          ·
            refine ⟨235452467878182235714888235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 627873247675152628573035293 235452467878182235714888235)
            ·
              refine ⟨353178701817273353572332353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235452467878182235714888235 353178701817273353572332353)
              ·
                refine ⟨264884026362955015179249265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 353178701817273353572332353 264884026362955015179249265)
                ·
                  refine ⟨198663019772216261384436949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 264884026362955015179249265 198663019772216261384436949)
                  ·
                    refine ⟨4656164525911318626197741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 198663019772216261384436949 4656164525911318626197741)
                    ·
                      refine ⟨1746061697216744484824153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4656164525911318626197741 1746061697216744484824153)
                      ·
                        rfl

theorem cell23_3400443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 7, 3].length) (baseStart_3400443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3400443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3400443 prefixEnd_3400443 := by exact prefixLift 3400443
  have htrace : WordTrace (prefixWord ++ tailWord_3400443) baseStart_3400443 baseEnd_3400443 := by
    simpa [prefixWord, tailWord_3400443, baseEnd_3400443] using wordTrace_append hprefix tailTrace_3400443
  have hstable : (prefixWord ++ tailWord_3400443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3400443).length < 2 ^ (prefixWord ++ tailWord_3400443).sum := by decide
  have hdescent : baseEnd_3400443 < baseStart_3400443 := by decide
  rcases family_descends (prefixWord ++ tailWord_3400443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3400444 : List Nat := [2, 2, 2, 1, 3, 4, 2, 1, 1, 1, 4]
def baseStart_3400444 : Nat := 118140960795 + 3400444 * 2 ^ 59
def prefixEnd_3400444 : Nat := 4983230072969 + 3 ^ 40 * 3400444 * 2
def baseEnd_3400444 : Nat := 1746062210697398980911649

theorem tailTrace_3400444 : CollatzResearch.WordTrace tailWord_3400444 prefixEnd_3400444 1746062210697398980911649 := by
  unfold tailWord_3400444
  simp only [CollatzResearch.WordTrace]
  refine ⟨62012190846389806222236193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82682921128519741629648257 62012190846389806222236193)
  ·
    refine ⟨46509143134792354666677145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62012190846389806222236193 46509143134792354666677145)
    ·
      refine ⟨34881857351094266000007859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46509143134792354666677145 34881857351094266000007859)
      ·
        refine ⟨52322786026641399000011789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34881857351094266000007859 52322786026641399000011789)
        ·
          refine ⟨19621044759990524625004421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52322786026641399000011789 19621044759990524625004421)
          ·
            refine ⟨3678945892498223367188329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19621044759990524625004421 3678945892498223367188329)
            ·
              refine ⟨2759209419373667525391247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3678945892498223367188329 2759209419373667525391247)
              ·
                refine ⟨4138814129060501288086871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2759209419373667525391247 4138814129060501288086871)
                ·
                  refine ⟨6208221193590751932130307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4138814129060501288086871 6208221193590751932130307)
                  ·
                    refine ⟨9312331790386127898195461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6208221193590751932130307 9312331790386127898195461)
                    ·
                      refine ⟨1746062210697398980911649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9312331790386127898195461 1746062210697398980911649)
                      ·
                        rfl

theorem cell23_3400444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 2, 1, 1, 1, 4].length) (baseStart_3400444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3400444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3400444 prefixEnd_3400444 := by exact prefixLift 3400444
  have htrace : WordTrace (prefixWord ++ tailWord_3400444) baseStart_3400444 baseEnd_3400444 := by
    simpa [prefixWord, tailWord_3400444, baseEnd_3400444] using wordTrace_append hprefix tailTrace_3400444
  have hstable : (prefixWord ++ tailWord_3400444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3400444).length < 2 ^ (prefixWord ++ tailWord_3400444).sum := by decide
  have hdescent : baseEnd_3400444 < baseStart_3400444 := by decide
  rcases family_descends (prefixWord ++ tailWord_3400444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3400450 : List Nat := [3, 4, 1, 1, 1, 3, 10]
def baseStart_3400450 : Nat := 118140960795 + 3400450 * 2 ^ 59
def prefixEnd_3400450 : Nat := 4983230072969 + 3 ^ 40 * 3400450 * 2
def baseEnd_3400450 : Nat := 21556361624460814289341

theorem tailTrace_3400450 : CollatzResearch.WordTrace tailWord_3400450 prefixEnd_3400450 21556361624460814289341 := by
  unfold tailWord_3400450
  simp only [CollatzResearch.WordTrace]
  refine ⟨31006150132689468867297701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82683067020505250312793869 31006150132689468867297701)
  ·
    refine ⟨5813653149879275412618319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31006150132689468867297701 5813653149879275412618319)
    ·
      refine ⟨8720479724818913118927479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5813653149879275412618319 8720479724818913118927479)
      ·
        refine ⟨13080719587228369678391219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8720479724818913118927479 13080719587228369678391219)
        ·
          refine ⟨19621079380842554517586829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13080719587228369678391219 19621079380842554517586829)
          ·
            refine ⟨7357904767815957944095061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19621079380842554517586829 7357904767815957944095061)
            ·
              refine ⟨21556361624460814289341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7357904767815957944095061 21556361624460814289341)
              ·
                rfl

theorem cell23_3400450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 10].length) (baseStart_3400450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3400450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3400450 prefixEnd_3400450 := by exact prefixLift 3400450
  have htrace : WordTrace (prefixWord ++ tailWord_3400450) baseStart_3400450 baseEnd_3400450 := by
    simpa [prefixWord, tailWord_3400450, baseEnd_3400450] using wordTrace_append hprefix tailTrace_3400450
  have hstable : (prefixWord ++ tailWord_3400450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3400450).length < 2 ^ (prefixWord ++ tailWord_3400450).sum := by decide
  have hdescent : baseEnd_3400450 < baseStart_3400450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3400450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3400484 : List Nat := [2, 3, 1, 3, 4, 1, 2, 7]
def baseStart_3400484 : Nat := 118140960795 + 3400484 * 2 ^ 59
def prefixEnd_3400484 : Nat := 4983230072969 + 3 ^ 40 * 3400484 * 2
def baseEnd_3400484 : Nat := 64669731478651067570795

theorem tailTrace_3400484 : CollatzResearch.WordTrace tailWord_3400484 prefixEnd_3400484 64669731478651067570795 := by
  unfold tailWord_3400484
  simp only [CollatzResearch.WordTrace]
  refine ⟨62012920306317349637964253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82683893741756466183952337 62012920306317349637964253)
  ·
    refine ⟨23254845114869006114236595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62012920306317349637964253 23254845114869006114236595)
    ·
      refine ⟨34882267672303509171354893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23254845114869006114236595 34882267672303509171354893)
      ·
        refine ⟨13080850377113815939258085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34882267672303509171354893 13080850377113815939258085)
        ·
          refine ⟨2452659445708840488610891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13080850377113815939258085 2452659445708840488610891)
          ·
            refine ⟨3678989168563260732916337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2452659445708840488610891 3678989168563260732916337)
            ·
              refine ⟨2759241876422445549687253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3678989168563260732916337 2759241876422445549687253)
              ·
                refine ⟨64669731478651067570795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2759241876422445549687253 64669731478651067570795)
                ·
                  rfl

theorem cell23_3400484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 2, 7].length) (baseStart_3400484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3400484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3400484 prefixEnd_3400484 := by exact prefixLift 3400484
  have htrace : WordTrace (prefixWord ++ tailWord_3400484) baseStart_3400484 baseEnd_3400484 := by
    simpa [prefixWord, tailWord_3400484, baseEnd_3400484] using wordTrace_append hprefix tailTrace_3400484
  have hstable : (prefixWord ++ tailWord_3400484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3400484).length < 2 ^ (prefixWord ++ tailWord_3400484).sum := by decide
  have hdescent : baseEnd_3400484 < baseStart_3400484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3400484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3400494 : List Nat := [4, 1, 3, 2, 1, 1, 1, 2, 4, 1, 3]
def baseStart_3400494 : Nat := 118140960795 + 3400494 * 2 ^ 59
def prefixEnd_3400494 : Nat := 4983230072969 + 3 ^ 40 * 3400494 * 2
def baseEnd_3400494 : Nat := 1746087884730123785286419

theorem tailTrace_3400494 : CollatzResearch.WordTrace tailWord_3400494 prefixEnd_3400494 1746087884730123785286419 := by
  unfold tailWord_3400494
  simp only [CollatzResearch.WordTrace]
  refine ⟨15503275667824808872974067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82684136895065647322528357 15503275667824808872974067)
  ·
    refine ⟨23254913501737213309461101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15503275667824808872974067 23254913501737213309461101)
    ·
      refine ⟨8720592563151454991047913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23254913501737213309461101 8720592563151454991047913)
      ·
        refine ⟨6540444422363591243285935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8720592563151454991047913 6540444422363591243285935)
        ·
          refine ⟨9810666633545386864928903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6540444422363591243285935 9810666633545386864928903)
          ·
            refine ⟨14715999950318080297393355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9810666633545386864928903 14715999950318080297393355)
            ·
              refine ⟨22073999925477120446090033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14715999950318080297393355 22073999925477120446090033)
              ·
                refine ⟨16555499944107840334567525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22073999925477120446090033 16555499944107840334567525)
                ·
                  refine ⟨3104156239520220062731411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16555499944107840334567525 3104156239520220062731411)
                  ·
                    refine ⟨4656234359280330094097117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3104156239520220062731411 4656234359280330094097117)
                    ·
                      refine ⟨1746087884730123785286419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4656234359280330094097117 1746087884730123785286419)
                      ·
                        rfl

theorem cell23_3400494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_3400494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3400494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3400494 prefixEnd_3400494 := by exact prefixLift 3400494
  have htrace : WordTrace (prefixWord ++ tailWord_3400494) baseStart_3400494 baseEnd_3400494 := by
    simpa [prefixWord, tailWord_3400494, baseEnd_3400494] using wordTrace_append hprefix tailTrace_3400494
  have hstable : (prefixWord ++ tailWord_3400494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3400494).length < 2 ^ (prefixWord ++ tailWord_3400494).sum := by decide
  have hdescent : baseEnd_3400494 < baseStart_3400494 := by decide
  rcases family_descends (prefixWord ++ tailWord_3400494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3400520 : List Nat := [2, 1, 3, 1, 1, 3, 2, 1, 2, 4, 3]
def baseStart_3400520 : Nat := 118140960795 + 3400520 * 2 ^ 59
def prefixEnd_3400520 : Nat := 4983230072969 + 3 ^ 40 * 3400520 * 2
def baseEnd_3400520 : Nat := 1746101235227140683561299

theorem tailTrace_3400520 : CollatzResearch.WordTrace tailWord_3400520 prefixEnd_3400520 1746101235227140683561299 := by
  unfold tailWord_3400520
  simp only [CollatzResearch.WordTrace]
  refine ⟨62013576820252138712119507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82684769093669518282826009 62013576820252138712119507)
  ·
    refine ⟨93020365230378208068179261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62013576820252138712119507 93020365230378208068179261)
    ·
      refine ⟨34882636961391828025567223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93020365230378208068179261 34882636961391828025567223)
      ·
        refine ⟨52323955442087742038350835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34882636961391828025567223 52323955442087742038350835)
        ·
          refine ⟨78485933163131613057526253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52323955442087742038350835 78485933163131613057526253)
          ·
            refine ⟨29432224936174354896572345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78485933163131613057526253 29432224936174354896572345)
            ·
              refine ⟨22074168702130766172429259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29432224936174354896572345 22074168702130766172429259)
              ·
                refine ⟨33111253053196149258643889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22074168702130766172429259 33111253053196149258643889)
                ·
                  refine ⟨24833439789897111943982917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33111253053196149258643889 24833439789897111943982917)
                  ·
                    refine ⟨4656269960605708489496797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24833439789897111943982917 4656269960605708489496797)
                    ·
                      refine ⟨1746101235227140683561299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4656269960605708489496797 1746101235227140683561299)
                      ·
                        rfl

theorem cell23_3400520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 2, 4, 3].length) (baseStart_3400520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3400520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3400520 prefixEnd_3400520 := by exact prefixLift 3400520
  have htrace : WordTrace (prefixWord ++ tailWord_3400520) baseStart_3400520 baseEnd_3400520 := by
    simpa [prefixWord, tailWord_3400520, baseEnd_3400520] using wordTrace_append hprefix tailTrace_3400520
  have hstable : (prefixWord ++ tailWord_3400520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3400520).length < 2 ^ (prefixWord ++ tailWord_3400520).sum := by decide
  have hdescent : baseEnd_3400520 < baseStart_3400520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3400520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3400530 : List Nat := [3, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4]
def baseStart_3400530 : Nat := 118140960795 + 3400530 * 2 ^ 59
def prefixEnd_3400530 : Nat := 4983230072969 + 3 ^ 40 * 3400530 * 2
def baseEnd_3400530 : Nat := 1746106370033685644436253

theorem tailTrace_3400530 : CollatzResearch.WordTrace tailWord_3400530 prefixEnd_3400530 1746106370033685644436253 := by
  unfold tailWord_3400530
  simp only [CollatzResearch.WordTrace]
  refine ⟨31006879592617012283025761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82685012246978699421402029 31006879592617012283025761)
  ·
    refine ⟨23255159694462759212269321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31006879592617012283025761 23255159694462759212269321)
    ·
      refine ⟨17441369770847069409201991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23255159694462759212269321 17441369770847069409201991)
      ·
        refine ⟨26162054656270604113802987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17441369770847069409201991 26162054656270604113802987)
        ·
          refine ⟨39243081984405906170704481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26162054656270604113802987 39243081984405906170704481)
          ·
            refine ⟨29432311488304429628028361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39243081984405906170704481 29432311488304429628028361)
            ·
              refine ⟨22074233616228322221021271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29432311488304429628028361 22074233616228322221021271)
              ·
                refine ⟨33111350424342483331531907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22074233616228322221021271 33111350424342483331531907)
                ·
                  refine ⟨49667025636513724997297861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33111350424342483331531907 49667025636513724997297861)
                  ·
                    refine ⟨9312567306846323436993349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49667025636513724997297861 9312567306846323436993349)
                    ·
                      refine ⟨1746106370033685644436253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9312567306846323436993349 1746106370033685644436253)
                      ·
                        rfl

theorem cell23_3400530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_3400530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3400530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3400530 prefixEnd_3400530 := by exact prefixLift 3400530
  have htrace : WordTrace (prefixWord ++ tailWord_3400530) baseStart_3400530 baseEnd_3400530 := by
    simpa [prefixWord, tailWord_3400530, baseEnd_3400530] using wordTrace_append hprefix tailTrace_3400530
  have hstable : (prefixWord ++ tailWord_3400530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3400530).length < 2 ^ (prefixWord ++ tailWord_3400530).sum := by decide
  have hdescent : baseEnd_3400530 < baseStart_3400530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3400530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3400557 : List Nat := [1, 5, 1, 1, 1, 1, 1, 7, 5]
def baseStart_3400557 : Nat := 118140960795 + 3400557 * 2 ^ 59
def prefixEnd_3400557 : Nat := 4983230072969 + 3 ^ 40 * 3400557 * 2
def baseEnd_3400557 : Nat := 194013359334595226533181

theorem tailTrace_3400557 : CollatzResearch.WordTrace tailWord_3400557 prefixEnd_3400557 194013359334595226533181 := by
  unfold tailWord_3400557
  simp only [CollatzResearch.WordTrace]
  refine ⟨124028503141370232743335925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82685668760913488495557283 124028503141370232743335925)
  ·
    refine ⟨11627672169503459319687743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 124028503141370232743335925 11627672169503459319687743)
    ·
      refine ⟨17441508254255188979531615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11627672169503459319687743 17441508254255188979531615)
      ·
        refine ⟨26162262381382783469297423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17441508254255188979531615 26162262381382783469297423)
        ·
          refine ⟨39243393572074175203946135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26162262381382783469297423 39243393572074175203946135)
          ·
            refine ⟨58865090358111262805919203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39243393572074175203946135 58865090358111262805919203)
            ·
              refine ⟨88297635537166894208878805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58865090358111262805919203 88297635537166894208878805)
              ·
                refine ⟨2069475832902349083020597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 88297635537166894208878805 2069475832902349083020597)
                ·
                  refine ⟨194013359334595226533181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2069475832902349083020597 194013359334595226533181)
                  ·
                    rfl

theorem cell23_3400557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 7, 5].length) (baseStart_3400557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3400557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3400557 prefixEnd_3400557 := by exact prefixLift 3400557
  have htrace : WordTrace (prefixWord ++ tailWord_3400557) baseStart_3400557 baseEnd_3400557 := by
    simpa [prefixWord, tailWord_3400557, baseEnd_3400557] using wordTrace_append hprefix tailTrace_3400557
  have hstable : (prefixWord ++ tailWord_3400557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3400557).length < 2 ^ (prefixWord ++ tailWord_3400557).sum := by decide
  have hdescent : baseEnd_3400557 < baseStart_3400557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3400557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3400607 : List Nat := [1, 1, 2, 5, 2, 2, 1, 1, 1, 3, 4]
def baseStart_3400607 : Nat := 118140960795 + 3400607 * 2 ^ 59
def prefixEnd_3400607 : Nat := 4983230072969 + 3 ^ 40 * 3400607 * 2
def baseEnd_3400607 : Nat := 1746145908044081843173399

theorem tailTrace_3400607 : CollatzResearch.WordTrace tailWord_3400607 prefixEnd_3400607 1746145908044081843173399 := by
  unfold tailWord_3400607
  simp only [CollatzResearch.WordTrace]
  refine ⟨124030326791189091282656075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82686884527459394188437383 124030326791189091282656075)
  ·
    refine ⟨186045490186783636923984113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124030326791189091282656075 186045490186783636923984113)
    ·
      refine ⟨139534117640087727692988085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186045490186783636923984113 139534117640087727692988085)
      ·
        refine ⟨13081323528758224471217633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 139534117640087727692988085 13081323528758224471217633)
        ·
          refine ⟨9810992646568668353413225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13081323528758224471217633 9810992646568668353413225)
          ·
            refine ⟨7358244484926501265059919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9810992646568668353413225 7358244484926501265059919)
            ·
              refine ⟨11037366727389751897589879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7358244484926501265059919 11037366727389751897589879)
              ·
                refine ⟨16556050091084627846384819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11037366727389751897589879 16556050091084627846384819)
                ·
                  refine ⟨24834075136626941769577229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16556050091084627846384819 24834075136626941769577229)
                  ·
                    refine ⟨9312778176235103163591461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24834075136626941769577229 9312778176235103163591461)
                    ·
                      refine ⟨1746145908044081843173399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9312778176235103163591461 1746145908044081843173399)
                      ·
                        rfl

theorem cell23_3400607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_3400607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3400607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3400607 prefixEnd_3400607 := by exact prefixLift 3400607
  have htrace : WordTrace (prefixWord ++ tailWord_3400607) baseStart_3400607 baseEnd_3400607 := by
    simpa [prefixWord, tailWord_3400607, baseEnd_3400607] using wordTrace_append hprefix tailTrace_3400607
  have hstable : (prefixWord ++ tailWord_3400607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3400607).length < 2 ^ (prefixWord ++ tailWord_3400607).sum := by decide
  have hdescent : baseEnd_3400607 < baseStart_3400607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3400607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3400634 : List Nat := [3, 1, 1, 1, 2, 1, 3, 6, 1, 4]
def baseStart_3400634 : Nat := 118140960795 + 3400634 * 2 ^ 59
def prefixEnd_3400634 : Nat := 4983230072969 + 3 ^ 40 * 3400634 * 2
def baseEnd_3400634 : Nat := 582053257340584412511925

theorem tailTrace_3400634 : CollatzResearch.WordTrace tailWord_3400634 prefixEnd_3400634 582053257340584412511925 := by
  unfold tailWord_3400634
  simp only [CollatzResearch.WordTrace]
  refine ⟨31007827890522818723472239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82687541041394183262592637 31007827890522818723472239)
  ·
    refine ⟨46511741835784228085208359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31007827890522818723472239 46511741835784228085208359)
    ·
      refine ⟨69767612753676342127812539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46511741835784228085208359 69767612753676342127812539)
      ·
        refine ⟨104651419130514513191718809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69767612753676342127812539 104651419130514513191718809)
        ·
          refine ⟨78488564347885884893789107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104651419130514513191718809 78488564347885884893789107)
          ·
            refine ⟨117732846521828827340683661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78488564347885884893789107 117732846521828827340683661)
            ·
              refine ⟨44149817445685810252756373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117732846521828827340683661 44149817445685810252756373)
              ·
                refine ⟨2069522692766522355597955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 44149817445685810252756373 2069522692766522355597955)
                ·
                  refine ⟨3104284039149783533396933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2069522692766522355597955 3104284039149783533396933)
                  ·
                    refine ⟨582053257340584412511925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3104284039149783533396933 582053257340584412511925)
                    ·
                      rfl

theorem cell23_3400634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 6, 1, 4].length) (baseStart_3400634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3400634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3400634 prefixEnd_3400634 := by exact prefixLift 3400634
  have htrace : WordTrace (prefixWord ++ tailWord_3400634) baseStart_3400634 baseEnd_3400634 := by
    simpa [prefixWord, tailWord_3400634, baseEnd_3400634] using wordTrace_append hprefix tailTrace_3400634
  have hstable : (prefixWord ++ tailWord_3400634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3400634).length < 2 ^ (prefixWord ++ tailWord_3400634).sum := by decide
  have hdescent : baseEnd_3400634 < baseStart_3400634 := by decide
  rcases family_descends (prefixWord ++ tailWord_3400634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3400650 : List Nat := [3, 1, 2, 1, 2, 1, 1, 1, 3, 2, 6]
def baseStart_3400650 : Nat := 118140960795 + 3400650 * 2 ^ 59
def prefixEnd_3400650 : Nat := 4983230072969 + 3 ^ 40 * 3400650 * 2
def baseEnd_3400650 : Nat := 1746167987712225174935701

theorem tailTrace_3400650 : CollatzResearch.WordTrace tailWord_3400650 prefixEnd_3400650 1746167987712225174935701 := by
  unfold tailWord_3400650
  simp only [CollatzResearch.WordTrace]
  refine ⟨31007973782508327406617851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82687930086688873084314269 31007973782508327406617851)
  ·
    refine ⟨46511960673762491109926777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31007973782508327406617851 46511960673762491109926777)
    ·
      refine ⟨34883970505321868332445083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46511960673762491109926777 34883970505321868332445083)
      ·
        refine ⟨52325955757982802498667625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34883970505321868332445083 52325955757982802498667625)
        ·
          refine ⟨39244466818487101874000719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52325955757982802498667625 39244466818487101874000719)
          ·
            refine ⟨58866700227730652811001079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39244466818487101874000719 58866700227730652811001079)
            ·
              refine ⟨88300050341595979216501619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58866700227730652811001079 88300050341595979216501619)
              ·
                refine ⟨132450075512393968824752429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88300050341595979216501619 132450075512393968824752429)
                ·
                  refine ⟨49668778317147738309282161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 132450075512393968824752429 49668778317147738309282161)
                  ·
                    refine ⟨37251583737860803731961621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49668778317147738309282161 37251583737860803731961621)
                    ·
                      refine ⟨1746167987712225174935701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37251583737860803731961621 1746167987712225174935701)
                      ·
                        rfl

theorem cell23_3400650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 3, 2, 6].length) (baseStart_3400650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3400650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3400650 prefixEnd_3400650 := by exact prefixLift 3400650
  have htrace : WordTrace (prefixWord ++ tailWord_3400650) baseStart_3400650 baseEnd_3400650 := by
    simpa [prefixWord, tailWord_3400650, baseEnd_3400650] using wordTrace_append hprefix tailTrace_3400650
  have hstable : (prefixWord ++ tailWord_3400650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3400650).length < 2 ^ (prefixWord ++ tailWord_3400650).sum := by decide
  have hdescent : baseEnd_3400650 < baseStart_3400650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3400650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3400697 : List Nat := [1, 2, 1, 3, 1, 3, 2, 2, 3, 1, 4]
def baseStart_3400697 : Nat := 118140960795 + 3400697 * 2 ^ 59
def prefixEnd_3400697 : Nat := 4983230072969 + 3 ^ 40 * 3400697 * 2
def baseEnd_3400697 : Nat := 1746192121302986491047985

theorem tailTrace_3400697 : CollatzResearch.WordTrace tailWord_3400697 prefixEnd_3400697 1746192121302986491047985 := by
  unfold tailWord_3400697
  simp only [CollatzResearch.WordTrace]
  refine ⟨124033609360863036653432345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82689072907242024435621563 124033609360863036653432345)
  ·
    refine ⟨93025207020647277490074259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124033609360863036653432345 93025207020647277490074259)
    ·
      refine ⟨139537810530970916235111389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93025207020647277490074259 139537810530970916235111389)
      ·
        refine ⟨52326678949114093588166771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139537810530970916235111389 52326678949114093588166771)
        ·
          refine ⟨78490018423671140382250157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52326678949114093588166771 78490018423671140382250157)
          ·
            refine ⟨29433756908876677643343809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78490018423671140382250157 29433756908876677643343809)
            ·
              refine ⟨22075317681657508232507857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29433756908876677643343809 22075317681657508232507857)
              ·
                refine ⟨16556488261243131174380893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22075317681657508232507857 16556488261243131174380893)
                ·
                  refine ⟨6208683097966174190392835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16556488261243131174380893 6208683097966174190392835)
                  ·
                    refine ⟨9313024646949261285589253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6208683097966174190392835 9313024646949261285589253)
                    ·
                      refine ⟨1746192121302986491047985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9313024646949261285589253 1746192121302986491047985)
                      ·
                        rfl

theorem cell23_3400697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 2, 3, 1, 4].length) (baseStart_3400697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3400697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3400697 prefixEnd_3400697 := by exact prefixLift 3400697
  have htrace : WordTrace (prefixWord ++ tailWord_3400697) baseStart_3400697 baseEnd_3400697 := by
    simpa [prefixWord, tailWord_3400697, baseEnd_3400697] using wordTrace_append hprefix tailTrace_3400697
  have hstable : (prefixWord ++ tailWord_3400697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3400697).length < 2 ^ (prefixWord ++ tailWord_3400697).sum := by decide
  have hdescent : baseEnd_3400697 < baseStart_3400697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3400697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3400714 : List Nat := [3, 1, 2, 2, 3, 2, 1, 1, 3, 1, 4]
def baseStart_3400714 : Nat := 118140960795 + 3400714 * 2 ^ 59
def prefixEnd_3400714 : Nat := 4983230072969 + 3 ^ 40 * 3400714 * 2
def baseEnd_3400714 : Nat := 1746200850474112924535407

theorem tailTrace_3400714 : CollatzResearch.WordTrace tailWord_3400714 prefixEnd_3400714 1746200850474112924535407 := by
  unfold tailWord_3400714
  simp only [CollatzResearch.WordTrace]
  refine ⟨31008557350450362139200299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82689486267867632371200797 31008557350450362139200299)
  ·
    refine ⟨46512836025675543208800449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31008557350450362139200299 46512836025675543208800449)
    ·
      refine ⟨34884627019256657406600337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46512836025675543208800449 34884627019256657406600337)
      ·
        refine ⟨26163470264442493054950253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34884627019256657406600337 26163470264442493054950253)
        ·
          refine ⟨9811301349165934895606345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26163470264442493054950253 9811301349165934895606345)
          ·
            refine ⟨7358476011874451171704759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9811301349165934895606345 7358476011874451171704759)
            ·
              refine ⟨11037714017811676757557139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7358476011874451171704759 11037714017811676757557139)
              ·
                refine ⟨16556571026717515136335709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11037714017811676757557139 16556571026717515136335709)
                ·
                  refine ⟨6208714135019068176125891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16556571026717515136335709 6208714135019068176125891)
                  ·
                    refine ⟨9313071202528602264188837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6208714135019068176125891 9313071202528602264188837)
                    ·
                      refine ⟨1746200850474112924535407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9313071202528602264188837 1746200850474112924535407)
                      ·
                        rfl

theorem cell23_3400714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_3400714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3400714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3400714 prefixEnd_3400714 := by exact prefixLift 3400714
  have htrace : WordTrace (prefixWord ++ tailWord_3400714) baseStart_3400714 baseEnd_3400714 := by
    simpa [prefixWord, tailWord_3400714, baseEnd_3400714] using wordTrace_append hprefix tailTrace_3400714
  have hstable : (prefixWord ++ tailWord_3400714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3400714).length < 2 ^ (prefixWord ++ tailWord_3400714).sum := by decide
  have hdescent : baseEnd_3400714 < baseStart_3400714 := by decide
  rcases family_descends (prefixWord ++ tailWord_3400714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3400747 : List Nat := [1, 1, 1, 1, 2, 1, 5, 2, 3, 3, 3]
def baseStart_3400747 : Nat := 118140960795 + 3400747 * 2 ^ 59
def prefixEnd_3400747 : Nat := 4983230072969 + 3 ^ 40 * 3400747 * 2
def baseEnd_3400747 : Nat := 1746217795335711295422755

theorem tailTrace_3400747 : CollatzResearch.WordTrace tailWord_3400747 prefixEnd_3400747 1746217795335711295422755 := by
  unfold tailWord_3400747
  simp only [CollatzResearch.WordTrace]
  refine ⟨124035433010681895192752495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82690288673787930128501663 124035433010681895192752495)
  ·
    refine ⟨186053149516022842789128743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124035433010681895192752495 186053149516022842789128743)
    ·
      refine ⟨279079724274034264183693115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186053149516022842789128743 279079724274034264183693115)
      ·
        refine ⟨418619586411051396275539673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279079724274034264183693115 418619586411051396275539673)
        ·
          refine ⟨313964689808288547206654755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 418619586411051396275539673 313964689808288547206654755)
          ·
            refine ⟨470947034712432820809982133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313964689808288547206654755 470947034712432820809982133)
            ·
              refine ⟨44151284504290576950935825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 470947034712432820809982133 44151284504290576950935825)
              ·
                refine ⟨33113463378217932713201869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44151284504290576950935825 33113463378217932713201869)
                ·
                  refine ⟨12417548766831724767450701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33113463378217932713201869 12417548766831724767450701)
                  ·
                    refine ⟨4656580787561896787794013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12417548766831724767450701 4656580787561896787794013)
                    ·
                      refine ⟨1746217795335711295422755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4656580787561896787794013 1746217795335711295422755)
                      ·
                        rfl

theorem cell23_3400747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 3, 3, 3].length) (baseStart_3400747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3400747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3400747 prefixEnd_3400747 := by exact prefixLift 3400747
  have htrace : WordTrace (prefixWord ++ tailWord_3400747) baseStart_3400747 baseEnd_3400747 := by
    simpa [prefixWord, tailWord_3400747, baseEnd_3400747] using wordTrace_append hprefix tailTrace_3400747
  have hstable : (prefixWord ++ tailWord_3400747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3400747).length < 2 ^ (prefixWord ++ tailWord_3400747).sum := by decide
  have hdescent : baseEnd_3400747 < baseStart_3400747 := by decide
  rcases family_descends (prefixWord ++ tailWord_3400747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3400748 : List Nat := [2, 2, 1, 1, 1, 2, 5, 4, 1, 2, 2]
def baseStart_3400748 : Nat := 118140960795 + 3400748 * 2 ^ 59
def prefixEnd_3400748 : Nat := 4983230072969 + 3 ^ 40 * 3400748 * 2
def baseEnd_3400748 : Nat := 1746218308816365791510251

theorem tailTrace_3400748 : CollatzResearch.WordTrace tailWord_3400748 prefixEnd_3400748 1746218308816365791510251 := by
  unfold tailWord_3400748
  simp only [CollatzResearch.WordTrace]
  refine ⟨62017734741839136181769449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82690312989118848242359265 62017734741839136181769449)
  ·
    refine ⟨46513301056379352136327087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62017734741839136181769449 46513301056379352136327087)
    ·
      refine ⟨69769951584569028204490631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46513301056379352136327087 69769951584569028204490631)
      ·
        refine ⟨104654927376853542306735947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69769951584569028204490631 104654927376853542306735947)
        ·
          refine ⟨156982391065280313460103921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104654927376853542306735947 156982391065280313460103921)
          ·
            refine ⟨117736793298960235095077941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156982391065280313460103921 117736793298960235095077941)
            ·
              refine ⟨11037824371777522040163557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 117736793298960235095077941 11037824371777522040163557)
              ·
                refine ⟨2069592069708285382530667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11037824371777522040163557 2069592069708285382530667)
                ·
                  refine ⟨3104388104562428073796001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2069592069708285382530667 3104388104562428073796001)
                  ·
                    refine ⟨2328291078421821055347001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3104388104562428073796001 2328291078421821055347001)
                    ·
                      refine ⟨1746218308816365791510251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2328291078421821055347001 1746218308816365791510251)
                      ·
                        rfl

theorem cell23_3400748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 4, 1, 2, 2].length) (baseStart_3400748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3400748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3400748 prefixEnd_3400748 := by exact prefixLift 3400748
  have htrace : WordTrace (prefixWord ++ tailWord_3400748) baseStart_3400748 baseEnd_3400748 := by
    simpa [prefixWord, tailWord_3400748, baseEnd_3400748] using wordTrace_append hprefix tailTrace_3400748
  have hstable : (prefixWord ++ tailWord_3400748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3400748).length < 2 ^ (prefixWord ++ tailWord_3400748).sum := by decide
  have hdescent : baseEnd_3400748 < baseStart_3400748 := by decide
  rcases family_descends (prefixWord ++ tailWord_3400748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3400764 : List Nat := [2, 2, 2, 2, 2, 2, 1, 3, 1, 3, 3]
def baseStart_3400764 : Nat := 118140960795 + 3400764 * 2 ^ 59
def prefixEnd_3400764 : Nat := 4983230072969 + 3 ^ 40 * 3400764 * 2
def baseEnd_3400764 : Nat := 1746226524506837728910177

theorem tailTrace_3400764 : CollatzResearch.WordTrace tailWord_3400764 prefixEnd_3400764 1746226524506837728910177 := by
  unfold tailWord_3400764
  simp only [CollatzResearch.WordTrace]
  refine ⟨62018026525810153548060673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82690702034413538064080897 62018026525810153548060673)
  ·
    refine ⟨46513519894357615161045505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62018026525810153548060673 46513519894357615161045505)
    ·
      refine ⟨34885139920768211370784129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46513519894357615161045505 34885139920768211370784129)
      ·
        refine ⟨26163854940576158528088097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34885139920768211370784129 26163854940576158528088097)
        ·
          refine ⟨19622891205432118896066073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26163854940576158528088097 19622891205432118896066073)
          ·
            refine ⟨14717168404074089172049555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19622891205432118896066073 14717168404074089172049555)
            ·
              refine ⟨22075752606111133758074333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14717168404074089172049555 22075752606111133758074333)
              ·
                refine ⟨8278407227291675159277875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22075752606111133758074333 8278407227291675159277875)
                ·
                  refine ⟨12417610840937512738916813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8278407227291675159277875 12417610840937512738916813)
                  ·
                    refine ⟨4656604065351567277093805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12417610840937512738916813 4656604065351567277093805)
                    ·
                      refine ⟨1746226524506837728910177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4656604065351567277093805 1746226524506837728910177)
                      ·
                        rfl

theorem cell23_3400764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 3, 1, 3, 3].length) (baseStart_3400764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3400764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3400764 prefixEnd_3400764 := by exact prefixLift 3400764
  have htrace : WordTrace (prefixWord ++ tailWord_3400764) baseStart_3400764 baseEnd_3400764 := by
    simpa [prefixWord, tailWord_3400764, baseEnd_3400764] using wordTrace_append hprefix tailTrace_3400764
  have hstable : (prefixWord ++ tailWord_3400764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3400764).length < 2 ^ (prefixWord ++ tailWord_3400764).sum := by decide
  have hdescent : baseEnd_3400764 < baseStart_3400764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3400764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3400781 : List Nat := [1, 6, 1, 1, 1, 2, 2, 2, 1, 3, 3]
def baseStart_3400781 : Nat := 118140960795 + 3400781 * 2 ^ 59
def prefixEnd_3400781 : Nat := 4983230072969 + 3 ^ 40 * 3400781 * 2
def baseEnd_3400781 : Nat := 1746235253677964162397599

theorem tailTrace_3400781 : CollatzResearch.WordTrace tailWord_3400781 prefixEnd_3400781 1746235253677964162397599 := by
  unfold tailWord_3400781
  simp only [CollatzResearch.WordTrace]
  refine ⟨124036673092558718999490197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82691115395039145999660131 124036673092558718999490197)
  ·
    refine ⟨5814219051213689953101103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 124036673092558718999490197 5814219051213689953101103)
    ·
      refine ⟨8721328576820534929651655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5814219051213689953101103 8721328576820534929651655)
      ·
        refine ⟨13081992865230802394477483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8721328576820534929651655 13081992865230802394477483)
        ·
          refine ⟨19622989297846203591716225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13081992865230802394477483 19622989297846203591716225)
          ·
            refine ⟨14717241973384652693787169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19622989297846203591716225 14717241973384652693787169)
            ·
              refine ⟨11037931480038489520340377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14717241973384652693787169 11037931480038489520340377)
              ·
                refine ⟨8278448610028867140255283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11037931480038489520340377 8278448610028867140255283)
                ·
                  refine ⟨12417672915043300710382925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8278448610028867140255283 12417672915043300710382925)
                  ·
                    refine ⟨4656627343141237766393597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12417672915043300710382925 4656627343141237766393597)
                    ·
                      refine ⟨1746235253677964162397599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4656627343141237766393597 1746235253677964162397599)
                      ·
                        rfl

theorem cell23_3400781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_3400781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3400781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3400781 prefixEnd_3400781 := by exact prefixLift 3400781
  have htrace : WordTrace (prefixWord ++ tailWord_3400781) baseStart_3400781 baseEnd_3400781 := by
    simpa [prefixWord, tailWord_3400781, baseEnd_3400781] using wordTrace_append hprefix tailTrace_3400781
  have hstable : (prefixWord ++ tailWord_3400781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3400781).length < 2 ^ (prefixWord ++ tailWord_3400781).sum := by decide
  have hdescent : baseEnd_3400781 < baseStart_3400781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3400781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3400814 : List Nat := [4, 1, 2, 2, 1, 2, 2, 1, 2, 6]
def baseStart_3400814 : Nat := 118140960795 + 3400814 * 2 ^ 59
def prefixEnd_3400814 : Nat := 4983230072969 + 3 ^ 40 * 3400814 * 2
def baseEnd_3400814 : Nat := 582084066179854177761649

theorem tailTrace_3400814 : CollatzResearch.WordTrace tailWord_3400814 prefixEnd_3400814 582084066179854177761649 := by
  unfold tailWord_3400814
  simp only [CollatzResearch.WordTrace]
  refine ⟨15504734587679895704430187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82691917800959443756960997 15504734587679895704430187)
  ·
    refine ⟨23257101881519843556645281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15504734587679895704430187 23257101881519843556645281)
    ·
      refine ⟨17442826411139882667483961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23257101881519843556645281 17442826411139882667483961)
      ·
        refine ⟨13082119808354912000612971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17442826411139882667483961 13082119808354912000612971)
        ·
          refine ⟨19623179712532368000919457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13082119808354912000612971 19623179712532368000919457)
          ·
            refine ⟨14717384784399276000689593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19623179712532368000919457 14717384784399276000689593)
            ·
              refine ⟨11038038588299457000517195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14717384784399276000689593 11038038588299457000517195)
              ·
                refine ⟨16557057882449185500775793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11038038588299457000517195 16557057882449185500775793)
                ·
                  refine ⟨12417793411836889125581845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16557057882449185500775793 12417793411836889125581845)
                  ·
                    refine ⟨582084066179854177761649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12417793411836889125581845 582084066179854177761649)
                    ·
                      rfl

theorem cell23_3400814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 1, 2, 6].length) (baseStart_3400814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3400814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3400814 prefixEnd_3400814 := by exact prefixLift 3400814
  have htrace : WordTrace (prefixWord ++ tailWord_3400814) baseStart_3400814 baseEnd_3400814 := by
    simpa [prefixWord, tailWord_3400814, baseEnd_3400814] using wordTrace_append hprefix tailTrace_3400814
  have hstable : (prefixWord ++ tailWord_3400814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3400814).length < 2 ^ (prefixWord ++ tailWord_3400814).sum := by decide
  have hdescent : baseEnd_3400814 < baseStart_3400814 := by decide
  rcases family_descends (prefixWord ++ tailWord_3400814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3400817 : List Nat := [1, 2, 2, 2, 1, 1, 2, 3, 1, 4, 4]
def baseStart_3400817 : Nat := 118140960795 + 3400817 * 2 ^ 59
def prefixEnd_3400817 : Nat := 4983230072969 + 3 ^ 40 * 3400817 * 2
def baseEnd_3400817 : Nat := 1746253738981526021547433

theorem tailTrace_3400817 : CollatzResearch.WordTrace tailWord_3400817 prefixEnd_3400817 1746253738981526021547433 := by
  unfold tailWord_3400817
  simp only [CollatzResearch.WordTrace]
  refine ⟨124037986120428297147800705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82691990746952198098533803 124037986120428297147800705)
  ·
    refine ⟨93028489590321222860850529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124037986120428297147800705 93028489590321222860850529)
    ·
      refine ⟨69771367192740917145637897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93028489590321222860850529 69771367192740917145637897)
      ·
        refine ⟨52328525394555687859228423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69771367192740917145637897 52328525394555687859228423)
        ·
          refine ⟨78492788091833531788842635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52328525394555687859228423 78492788091833531788842635)
          ·
            refine ⟨117739182137750297683263953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78492788091833531788842635 117739182137750297683263953)
            ·
              refine ⟨88304386603312723262447965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117739182137750297683263953 88304386603312723262447965)
              ·
                refine ⟨33114144976242271223417987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88304386603312723262447965 33114144976242271223417987)
                ·
                  refine ⟨49671217464363406835126981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33114144976242271223417987 49671217464363406835126981)
                  ·
                    refine ⟨9313353274568138781586309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49671217464363406835126981 9313353274568138781586309)
                    ·
                      refine ⟨1746253738981526021547433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9313353274568138781586309 1746253738981526021547433)
                      ·
                        rfl

theorem cell23_3400817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 4, 4].length) (baseStart_3400817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3400817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3400817 prefixEnd_3400817 := by exact prefixLift 3400817
  have htrace : WordTrace (prefixWord ++ tailWord_3400817) baseStart_3400817 baseEnd_3400817 := by
    simpa [prefixWord, tailWord_3400817, baseEnd_3400817] using wordTrace_append hprefix tailTrace_3400817
  have hstable : (prefixWord ++ tailWord_3400817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3400817).length < 2 ^ (prefixWord ++ tailWord_3400817).sum := by decide
  have hdescent : baseEnd_3400817 < baseStart_3400817 := by decide
  rcases family_descends (prefixWord ++ tailWord_3400817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3400914 : List Nat := [3, 2, 2, 2, 1, 1, 1, 1, 2, 3, 5]
def baseStart_3400914 : Nat := 118140960795 + 3400914 * 2 ^ 59
def prefixEnd_3400914 : Nat := 4983230072969 + 3 ^ 40 * 3400914 * 2
def baseEnd_3400914 : Nat := 1746303546605012142034487

theorem tailTrace_3400914 : CollatzResearch.WordTrace tailWord_3400914 prefixEnd_3400914 1746303546605012142034487 := by
  unfold tailWord_3400914
  simp only [CollatzResearch.WordTrace]
  refine ⟨31010381000269220678520449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82694349334051255142721197 31010381000269220678520449)
  ·
    refine ⟨23257785750201915508890337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31010381000269220678520449 23257785750201915508890337)
    ·
      refine ⟨17443339312651436631667753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23257785750201915508890337 17443339312651436631667753)
      ·
        refine ⟨13082504484488577473750815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17443339312651436631667753 13082504484488577473750815)
        ·
          refine ⟨19623756726732866210626223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13082504484488577473750815 19623756726732866210626223)
          ·
            refine ⟨29435635090099299315939335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19623756726732866210626223 29435635090099299315939335)
            ·
              refine ⟨44153452635148948973909003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29435635090099299315939335 44153452635148948973909003)
              ·
                refine ⟨66230178952723423460863505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44153452635148948973909003 66230178952723423460863505)
                ·
                  refine ⟨49672634214542567595647629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66230178952723423460863505 49672634214542567595647629)
                  ·
                    refine ⟨18627237830453462848367861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49672634214542567595647629 18627237830453462848367861)
                    ·
                      refine ⟨1746303546605012142034487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18627237830453462848367861 1746303546605012142034487)
                      ·
                        rfl

theorem cell23_3400914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_3400914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3400914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3400914 prefixEnd_3400914 := by exact prefixLift 3400914
  have htrace : WordTrace (prefixWord ++ tailWord_3400914) baseStart_3400914 baseEnd_3400914 := by
    simpa [prefixWord, tailWord_3400914, baseEnd_3400914] using wordTrace_append hprefix tailTrace_3400914
  have hstable : (prefixWord ++ tailWord_3400914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3400914).length < 2 ^ (prefixWord ++ tailWord_3400914).sum := by decide
  have hdescent : baseEnd_3400914 < baseStart_3400914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3400914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3400968 : List Nat := [2, 1, 3, 2, 4, 2, 1, 2, 6]
def baseStart_3400968 : Nat := 118140960795 + 3400968 * 2 ^ 59
def prefixEnd_3400968 : Nat := 4983230072969 + 3 ^ 40 * 3400968 * 2
def baseEnd_3400968 : Nat := 194036808284483881195471

theorem tailTrace_3400968 : CollatzResearch.WordTrace tailWord_3400968 prefixEnd_3400968 194036808284483881195471 := by
  unfold tailWord_3400968
  simp only [CollatzResearch.WordTrace]
  refine ⟨62021746771440624968273779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82695662361920833291031705 62021746771440624968273779)
  ·
    refine ⟨93032620157160937452410669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62021746771440624968273779 93032620157160937452410669)
    ·
      refine ⟨34887232558935351544654001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93032620157160937452410669 34887232558935351544654001)
      ·
        refine ⟨26165424419201513658490501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34887232558935351544654001 26165424419201513658490501)
        ·
          refine ⟨4906017078600283810966969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26165424419201513658490501 4906017078600283810966969)
          ·
            refine ⟨3679512808950212858225227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4906017078600283810966969 3679512808950212858225227)
            ·
              refine ⟨5519269213425319287337841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3679512808950212858225227 5519269213425319287337841)
              ·
                refine ⟨4139451910068989465503381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5519269213425319287337841 4139451910068989465503381)
                ·
                  refine ⟨194036808284483881195471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4139451910068989465503381 194036808284483881195471)
                  ·
                    rfl

theorem cell23_3400968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 2, 6].length) (baseStart_3400968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3400968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3400968 prefixEnd_3400968 := by exact prefixLift 3400968
  have htrace : WordTrace (prefixWord ++ tailWord_3400968) baseStart_3400968 baseEnd_3400968 := by
    simpa [prefixWord, tailWord_3400968, baseEnd_3400968] using wordTrace_append hprefix tailTrace_3400968
  have hstable : (prefixWord ++ tailWord_3400968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3400968).length < 2 ^ (prefixWord ++ tailWord_3400968).sum := by decide
  have hdescent : baseEnd_3400968 < baseStart_3400968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3400968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401004 : List Nat := [2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 5]
def baseStart_3401004 : Nat := 118140960795 + 3401004 * 2 ^ 59
def prefixEnd_3401004 : Nat := 4983230072969 + 3 ^ 40 * 3401004 * 2
def baseEnd_3401004 : Nat := 1746349759863916789909073

theorem tailTrace_3401004 : CollatzResearch.WordTrace tailWord_3401004 prefixEnd_3401004 1746349759863916789909073 := by
  unfold tailWord_3401004
  simp only [CollatzResearch.WordTrace]
  refine ⟨62022403285375414042429033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82696537713833885389905377 62022403285375414042429033)
  ·
    refine ⟨46516802464031560531821775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62022403285375414042429033 46516802464031560531821775)
    ·
      refine ⟨69775203696047340797732663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46516802464031560531821775 69775203696047340797732663)
      ·
        refine ⟨104662805544071011196598995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69775203696047340797732663 104662805544071011196598995)
        ·
          refine ⟨156994208316106516794898493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104662805544071011196598995 156994208316106516794898493)
          ·
            refine ⟨58872828118539943798086935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156994208316106516794898493 58872828118539943798086935)
            ·
              refine ⟨88309242177809915697130403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58872828118539943798086935 88309242177809915697130403)
              ·
                refine ⟨132463863266714873545695605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88309242177809915697130403 132463863266714873545695605)
                ·
                  refine ⟨12418487181254519394908963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 132463863266714873545695605 12418487181254519394908963)
                  ·
                    refine ⟨18627730771881779092363445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12418487181254519394908963 18627730771881779092363445)
                    ·
                      refine ⟨1746349759863916789909073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18627730771881779092363445 1746349759863916789909073)
                      ·
                        rfl

theorem cell23_3401004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 5].length) (baseStart_3401004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3401004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3401004 prefixEnd_3401004 := by exact prefixLift 3401004
  have htrace : WordTrace (prefixWord ++ tailWord_3401004) baseStart_3401004 baseEnd_3401004 := by
    simpa [prefixWord, tailWord_3401004, baseEnd_3401004] using wordTrace_append hprefix tailTrace_3401004
  have hstable : (prefixWord ++ tailWord_3401004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401004).length < 2 ^ (prefixWord ++ tailWord_3401004).sum := by decide
  have hdescent : baseEnd_3401004 < baseStart_3401004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401005 : List Nat := [1, 5, 3, 1, 1, 1, 2, 1, 1, 5, 2]
def baseStart_3401005 : Nat := 118140960795 + 3401005 * 2 ^ 59
def prefixEnd_3401005 : Nat := 4983230072969 + 3 ^ 40 * 3401005 * 2
def baseEnd_3401005 : Nat := 1746350273344571285996569

theorem tailTrace_3401005 : CollatzResearch.WordTrace tailWord_3401005 prefixEnd_3401005 1746350273344571285996569 := by
  unfold tailWord_3401005
  simp only [CollatzResearch.WordTrace]
  refine ⟨124044843043747205255644469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82696562029164803503762979 124044843043747205255644469)
  ·
    refine ⟨11629204035351300492716669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 124044843043747205255644469 11629204035351300492716669)
    ·
      refine ⟨4360951513256737684768751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11629204035351300492716669 4360951513256737684768751)
      ·
        refine ⟨6541427269885106527153127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4360951513256737684768751 6541427269885106527153127)
        ·
          refine ⟨9812140904827659790729691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6541427269885106527153127 9812140904827659790729691)
          ·
            refine ⟨14718211357241489686094537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9812140904827659790729691 14718211357241489686094537)
            ·
              refine ⟨11038658517931117264570903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14718211357241489686094537 11038658517931117264570903)
              ·
                refine ⟨16557987776896675896856355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11038658517931117264570903 16557987776896675896856355)
                ·
                  refine ⟨24836981665345013845284533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16557987776896675896856355 24836981665345013845284533)
                  ·
                    refine ⟨2328467031126095047995425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24836981665345013845284533 2328467031126095047995425)
                    ·
                      refine ⟨1746350273344571285996569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2328467031126095047995425 1746350273344571285996569)
                      ·
                        rfl

theorem cell23_3401005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_3401005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3401005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3401005 prefixEnd_3401005 := by exact prefixLift 3401005
  have htrace : WordTrace (prefixWord ++ tailWord_3401005) baseStart_3401005 baseEnd_3401005 := by
    simpa [prefixWord, tailWord_3401005, baseEnd_3401005] using wordTrace_append hprefix tailTrace_3401005
  have hstable : (prefixWord ++ tailWord_3401005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401005).length < 2 ^ (prefixWord ++ tailWord_3401005).sum := by decide
  have hdescent : baseEnd_3401005 < baseStart_3401005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401011 : List Nat := [1, 1, 1, 2, 5, 2, 1, 2, 4, 4]
def baseStart_3401011 : Nat := 118140960795 + 3401011 * 2 ^ 59
def prefixEnd_3401011 : Nat := 4983230072969 + 3 ^ 40 * 3401011 * 2
def baseEnd_3401011 : Nat := 582117784742832754173847

theorem tailTrace_3401011 : CollatzResearch.WordTrace tailWord_3401011 prefixEnd_3401011 582117784742832754173847 := by
  unfold tailWord_3401011
  simp only [CollatzResearch.WordTrace]
  refine ⟨124045061881725468280362887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82696707921150312186908591 124045061881725468280362887)
  ·
    refine ⟨186067592822588202420544331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124045061881725468280362887 186067592822588202420544331)
    ·
      refine ⟨279101389233882303630816497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186067592822588202420544331 279101389233882303630816497)
      ·
        refine ⟨209326041925411727723112373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279101389233882303630816497 209326041925411727723112373)
        ·
          refine ⟨19624316430507349474041785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 209326041925411727723112373 19624316430507349474041785)
          ·
            refine ⟨14718237322880512105531339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19624316430507349474041785 14718237322880512105531339)
            ·
              refine ⟨22077355984320768158297009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14718237322880512105531339 22077355984320768158297009)
              ·
                refine ⟨16558016988240576118722757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22077355984320768158297009 16558016988240576118722757)
                ·
                  refine ⟨3104628185295108022260517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16558016988240576118722757 3104628185295108022260517)
                  ·
                    refine ⟨582117784742832754173847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3104628185295108022260517 582117784742832754173847)
                    ·
                      rfl

theorem cell23_3401011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 2, 4, 4].length) (baseStart_3401011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3401011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3401011 prefixEnd_3401011 := by exact prefixLift 3401011
  have htrace : WordTrace (prefixWord ++ tailWord_3401011) baseStart_3401011 baseEnd_3401011 := by
    simpa [prefixWord, tailWord_3401011, baseEnd_3401011] using wordTrace_append hprefix tailTrace_3401011
  have hstable : (prefixWord ++ tailWord_3401011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401011).length < 2 ^ (prefixWord ++ tailWord_3401011).sum := by decide
  have hdescent : baseEnd_3401011 < baseStart_3401011 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401045 : List Nat := [1, 3, 2, 2, 3, 1, 4, 1, 2, 4]
def baseStart_3401045 : Nat := 118140960795 + 3401045 * 2 ^ 59
def prefixEnd_3401045 : Nat := 4983230072969 + 3 ^ 40 * 3401045 * 2
def baseEnd_3401045 : Nat := 582123604190250376498795

theorem tailTrace_3401045 : CollatzResearch.WordTrace tailWord_3401045 prefixEnd_3401045 582123604190250376498795 := by
  unfold tailWord_3401045
  simp only [CollatzResearch.WordTrace]
  refine ⟨124046301963602292087100589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82697534642401528058067059 124046301963602292087100589)
  ·
    refine ⟨46517363236350859532662721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124046301963602292087100589 46517363236350859532662721)
    ·
      refine ⟨34888022427263144649497041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46517363236350859532662721 34888022427263144649497041)
      ·
        refine ⟨26166016820447358487122781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34888022427263144649497041 26166016820447358487122781)
        ·
          refine ⟨9812256307667759432671043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26166016820447358487122781 9812256307667759432671043)
          ·
            refine ⟨14718384461501639149006565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9812256307667759432671043 14718384461501639149006565)
            ·
              refine ⟨2759697086531557340438731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14718384461501639149006565 2759697086531557340438731)
              ·
                refine ⟨4139545629797336010658097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2759697086531557340438731 4139545629797336010658097)
                ·
                  refine ⟨3104659222348002007993573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4139545629797336010658097 3104659222348002007993573)
                  ·
                    refine ⟨582123604190250376498795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3104659222348002007993573 582123604190250376498795)
                    ·
                      rfl

theorem cell23_3401045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 4, 1, 2, 4].length) (baseStart_3401045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3401045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3401045 prefixEnd_3401045 := by exact prefixLift 3401045
  have htrace : WordTrace (prefixWord ++ tailWord_3401045) baseStart_3401045 baseEnd_3401045 := by
    simpa [prefixWord, tailWord_3401045, baseEnd_3401045] using wordTrace_append hprefix tailTrace_3401045
  have hstable : (prefixWord ++ tailWord_3401045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401045).length < 2 ^ (prefixWord ++ tailWord_3401045).sum := by decide
  have hdescent : baseEnd_3401045 < baseStart_3401045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401068 : List Nat := [2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 3]
def baseStart_3401068 : Nat := 118140960795 + 3401068 * 2 ^ 59
def prefixEnd_3401068 : Nat := 4983230072969 + 3 ^ 40 * 3401068 * 2
def baseEnd_3401068 : Nat := 1746382622625804539508779

theorem tailTrace_3401068 : CollatzResearch.WordTrace tailWord_3401068 prefixEnd_3401068 1746382622625804539508779 := by
  unfold tailWord_3401068
  simp only [CollatzResearch.WordTrace]
  refine ⟨62023570421259483507593929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82698093895012644676791905 62023570421259483507593929)
  ·
    refine ⟨46517677815944612630695447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62023570421259483507593929 46517677815944612630695447)
    ·
      refine ⟨69776516723916918946043171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46517677815944612630695447 69776516723916918946043171)
      ·
        refine ⟨104664775085875378419064757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69776516723916918946043171 104664775085875378419064757)
        ·
          refine ⟨9812322664300816726787321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 104664775085875378419064757 9812322664300816726787321)
          ·
            refine ⟨7359241998225612545090491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9812322664300816726787321 7359241998225612545090491)
            ·
              refine ⟨11038862997338418817635737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7359241998225612545090491 11038862997338418817635737)
              ·
                refine ⟨8279147248003814113226803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11038862997338418817635737 8279147248003814113226803)
                ·
                  refine ⟨12418720872005721169840205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8279147248003814113226803 12418720872005721169840205)
                  ·
                    refine ⟨4657020327002145438690077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12418720872005721169840205 4657020327002145438690077)
                    ·
                      refine ⟨1746382622625804539508779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4657020327002145438690077 1746382622625804539508779)
                      ·
                        rfl

theorem cell23_3401068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 3].length) (baseStart_3401068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3401068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3401068 prefixEnd_3401068 := by exact prefixLift 3401068
  have htrace : WordTrace (prefixWord ++ tailWord_3401068) baseStart_3401068 baseEnd_3401068 := by
    simpa [prefixWord, tailWord_3401068, baseEnd_3401068] using wordTrace_append hprefix tailTrace_3401068
  have hstable : (prefixWord ++ tailWord_3401068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401068).length < 2 ^ (prefixWord ++ tailWord_3401068).sum := by decide
  have hdescent : baseEnd_3401068 < baseStart_3401068 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401085 : List Nat := [1, 4, 1, 1, 2, 2, 4, 2, 2, 1, 3]
def baseStart_3401085 : Nat := 118140960795 + 3401085 * 2 ^ 59
def prefixEnd_3401085 : Nat := 4983230072969 + 3 ^ 40 * 3401085 * 2
def baseEnd_3401085 : Nat := 1746391351796930972996201

theorem tailTrace_3401085 : CollatzResearch.WordTrace tailWord_3401085 prefixEnd_3401085 1746391351796930972996201 := by
  unfold tailWord_3401085
  simp only [CollatzResearch.WordTrace]
  refine ⟨124047760883457378918556709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82698507255638252612371139 124047760883457378918556709)
  ·
    refine ⟨23258955165648258547229383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124047760883457378918556709 23258955165648258547229383)
    ·
      refine ⟨34888432748472387820844075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23258955165648258547229383 34888432748472387820844075)
      ·
        refine ⟨52332649122708581731266113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34888432748472387820844075 52332649122708581731266113)
        ·
          refine ⟨39249486842031436298449585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52332649122708581731266113 39249486842031436298449585)
          ·
            refine ⟨29437115131523577223837189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39249486842031436298449585 29437115131523577223837189)
            ·
              refine ⟨5519459087160670729469473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29437115131523577223837189 5519459087160670729469473)
              ·
                refine ⟨4139594315370503047102105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5519459087160670729469473 4139594315370503047102105)
                ·
                  refine ⟨3104695736527877285326579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4139594315370503047102105 3104695736527877285326579)
                  ·
                    refine ⟨4657043604791815927989869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3104695736527877285326579 4657043604791815927989869)
                    ·
                      refine ⟨1746391351796930972996201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4657043604791815927989869 1746391351796930972996201)
                      ·
                        rfl

theorem cell23_3401085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 2, 2, 1, 3].length) (baseStart_3401085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3401085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3401085 prefixEnd_3401085 := by exact prefixLift 3401085
  have htrace : WordTrace (prefixWord ++ tailWord_3401085) baseStart_3401085 baseEnd_3401085 := by
    simpa [prefixWord, tailWord_3401085, baseEnd_3401085] using wordTrace_append hprefix tailTrace_3401085
  have hstable : (prefixWord ++ tailWord_3401085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401085).length < 2 ^ (prefixWord ++ tailWord_3401085).sum := by decide
  have hdescent : baseEnd_3401085 < baseStart_3401085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401091 : List Nat := [1, 1, 1, 3, 5, 1, 1, 1, 2, 3, 4]
def baseStart_3401091 : Nat := 118140960795 + 3401091 * 2 ^ 59
def prefixEnd_3401091 : Nat := 4983230072969 + 3 ^ 40 * 3401091 * 2
def baseEnd_3401091 : Nat := 1746394432680857949521173

theorem tailTrace_3401091 : CollatzResearch.WordTrace tailWord_3401091 prefixEnd_3401091 1746394432680857949521173 := by
  unfold tailWord_3401091
  simp only [CollatzResearch.WordTrace]
  refine ⟨124047979721435641943275127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82698653147623761295516751 124047979721435641943275127)
  ·
    refine ⟨186071969582153462914912691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124047979721435641943275127 186071969582153462914912691)
    ·
      refine ⟨279107954373230194372369037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186071969582153462914912691 279107954373230194372369037)
      ·
        refine ⟨104665482889961322889638389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 279107954373230194372369037 104665482889961322889638389)
        ·
          refine ⟨9812389020933874020903599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 104665482889961322889638389 9812389020933874020903599)
          ·
            refine ⟨14718583531400811031355399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9812389020933874020903599 14718583531400811031355399)
            ·
              refine ⟨22077875297101216547033099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14718583531400811031355399 22077875297101216547033099)
              ·
                refine ⟨33116812945651824820549649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22077875297101216547033099 33116812945651824820549649)
                ·
                  refine ⟨24837609709238868615412237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33116812945651824820549649 24837609709238868615412237)
                  ·
                    refine ⟨9314103640964575730779589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24837609709238868615412237 9314103640964575730779589)
                    ·
                      refine ⟨1746394432680857949521173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9314103640964575730779589 1746394432680857949521173)
                      ·
                        rfl

theorem cell23_3401091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 2, 3, 4].length) (baseStart_3401091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3401091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3401091 prefixEnd_3401091 := by exact prefixLift 3401091
  have htrace : WordTrace (prefixWord ++ tailWord_3401091) baseStart_3401091 baseEnd_3401091 := by
    simpa [prefixWord, tailWord_3401091, baseEnd_3401091] using wordTrace_append hprefix tailTrace_3401091
  have hstable : (prefixWord ++ tailWord_3401091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401091).length < 2 ^ (prefixWord ++ tailWord_3401091).sum := by decide
  have hdescent : baseEnd_3401091 < baseStart_3401091 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401104 : List Nat := [2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 10]
def baseStart_3401104 : Nat := 118140960795 + 3401104 * 2 ^ 59
def prefixEnd_3401104 : Nat := 4983230072969 + 3 ^ 40 * 3401104 * 2
def baseEnd_3401104 : Nat := 1746401107929366398658613

theorem tailTrace_3401104 : CollatzResearch.WordTrace tailWord_3401104 prefixEnd_3401104 1746401107929366398658613 := by
  unfold tailWord_3401104
  simp only [CollatzResearch.WordTrace]
  refine ⟨62024226935194272581749183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82698969246925696775665577 62024226935194272581749183)
  ·
    refine ⟨93036340402791408872623775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62024226935194272581749183 93036340402791408872623775)
    ·
      refine ⟨139554510604187113308935663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93036340402791408872623775 139554510604187113308935663)
      ·
        refine ⟨209331765906280669963403495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139554510604187113308935663 209331765906280669963403495)
        ·
          refine ⟨313997648859421004945105243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209331765906280669963403495 313997648859421004945105243)
          ·
            refine ⟨470996473289131507417657865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313997648859421004945105243 470996473289131507417657865)
            ·
              refine ⟨353247354966848630563243399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 470996473289131507417657865 353247354966848630563243399)
              ·
                refine ⟨529871032450272945844865099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 353247354966848630563243399 529871032450272945844865099)
                ·
                  refine ⟨794806548675409418767297649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 529871032450272945844865099 794806548675409418767297649)
                  ·
                    refine ⟨596104911506557064075473237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 794806548675409418767297649 596104911506557064075473237)
                    ·
                      refine ⟨1746401107929366398658613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 596104911506557064075473237 1746401107929366398658613)
                      ·
                        rfl

theorem cell23_3401104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 10].length) (baseStart_3401104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3401104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3401104 prefixEnd_3401104 := by exact prefixLift 3401104
  have htrace : WordTrace (prefixWord ++ tailWord_3401104) baseStart_3401104 baseEnd_3401104 := by
    simpa [prefixWord, tailWord_3401104, baseEnd_3401104] using wordTrace_append hprefix tailTrace_3401104
  have hstable : (prefixWord ++ tailWord_3401104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401104).length < 2 ^ (prefixWord ++ tailWord_3401104).sum := by decide
  have hdescent : baseEnd_3401104 < baseStart_3401104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401111 : List Nat := [1, 1, 3, 3, 1, 1, 1, 1, 4, 4, 3]
def baseStart_3401111 : Nat := 118140960795 + 3401111 * 2 ^ 59
def prefixEnd_3401111 : Nat := 4983230072969 + 3 ^ 40 * 3401111 * 2
def baseEnd_3401111 : Nat := 1746404702293947871271081

theorem tailTrace_3401111 : CollatzResearch.WordTrace tailWord_3401111 prefixEnd_3401111 1746404702293947871271081 := by
  unfold tailWord_3401111
  simp only [CollatzResearch.WordTrace]
  refine ⟨124048709181363185359003187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82699139454242123572668791 124048709181363185359003187)
  ·
    refine ⟨186073063772044778038504781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124048709181363185359003187 186073063772044778038504781)
    ·
      refine ⟨69777398914516791764439293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186073063772044778038504781 69777398914516791764439293)
      ·
        refine ⟨26166524592943796911664735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69777398914516791764439293 26166524592943796911664735)
        ·
          refine ⟨39249786889415695367497103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26166524592943796911664735 39249786889415695367497103)
          ·
            refine ⟨58874680334123543051245655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39249786889415695367497103 58874680334123543051245655)
            ·
              refine ⟨88312020501185314576868483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58874680334123543051245655 88312020501185314576868483)
              ·
                refine ⟨132468030751777971865302725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88312020501185314576868483 132468030751777971865302725)
                ·
                  refine ⟨24837755765958369724744261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 132468030751777971865302725 24837755765958369724744261)
                  ·
                    refine ⟨4657079206117194323389549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24837755765958369724744261 4657079206117194323389549)
                    ·
                      refine ⟨1746404702293947871271081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4657079206117194323389549 1746404702293947871271081)
                      ·
                        rfl

theorem cell23_3401111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 4, 4, 3].length) (baseStart_3401111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3401111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3401111 prefixEnd_3401111 := by exact prefixLift 3401111
  have htrace : WordTrace (prefixWord ++ tailWord_3401111) baseStart_3401111 baseEnd_3401111 := by
    simpa [prefixWord, tailWord_3401111, baseEnd_3401111] using wordTrace_append hprefix tailTrace_3401111
  have hstable : (prefixWord ++ tailWord_3401111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401111).length < 2 ^ (prefixWord ++ tailWord_3401111).sum := by decide
  have hdescent : baseEnd_3401111 < baseStart_3401111 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401205 : List Nat := [1, 3, 5, 1, 1, 2, 1, 1, 1, 2, 5]
def baseStart_3401205 : Nat := 118140960795 + 3401205 * 2 ^ 59
def prefixEnd_3401205 : Nat := 4983230072969 + 3 ^ 40 * 3401205 * 2
def baseEnd_3401205 : Nat := 1746452969475470503495649

theorem tailTrace_3401205 : CollatzResearch.WordTrace tailWord_3401205 prefixEnd_3401205 1746452969475470503495649 := by
  unfold tailWord_3401205
  simp only [CollatzResearch.WordTrace]
  refine ⟨124052137643022639412925069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82701425095348426275283379 124052137643022639412925069)
  ·
    refine ⟨46519551616133489779846901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124052137643022639412925069 46519551616133489779846901)
    ·
      refine ⟨4361207964012514666860647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46519551616133489779846901 4361207964012514666860647)
      ·
        refine ⟨6541811946018772000290971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4361207964012514666860647 6541811946018772000290971)
        ·
          refine ⟨9812717919028158000436457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6541811946018772000290971 9812717919028158000436457)
          ·
            refine ⟨7359538439271118500327343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9812717919028158000436457 7359538439271118500327343)
            ·
              refine ⟨11039307658906677750491015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7359538439271118500327343 11039307658906677750491015)
              ·
                refine ⟨16558961488360016625736523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11039307658906677750491015 16558961488360016625736523)
                ·
                  refine ⟨24838442232540024938604785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16558961488360016625736523 24838442232540024938604785)
                  ·
                    refine ⟨18628831674405018703953589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24838442232540024938604785 18628831674405018703953589)
                    ·
                      refine ⟨1746452969475470503495649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18628831674405018703953589 1746452969475470503495649)
                      ·
                        rfl

theorem cell23_3401205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_3401205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3401205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3401205 prefixEnd_3401205 := by exact prefixLift 3401205
  have htrace : WordTrace (prefixWord ++ tailWord_3401205) baseStart_3401205 baseEnd_3401205 := by
    simpa [prefixWord, tailWord_3401205, baseEnd_3401205] using wordTrace_append hprefix tailTrace_3401205
  have hstable : (prefixWord ++ tailWord_3401205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401205).length < 2 ^ (prefixWord ++ tailWord_3401205).sum := by decide
  have hdescent : baseEnd_3401205 < baseStart_3401205 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401229 : List Nat := [1, 7, 1, 1, 2, 1, 2, 1, 2, 5]
def baseStart_3401229 : Nat := 118140960795 + 3401229 * 2 ^ 59
def prefixEnd_3401229 : Nat := 4983230072969 + 3 ^ 40 * 3401229 * 2
def baseEnd_3401229 : Nat := 582155097670392803198513

theorem tailTrace_3401229 : CollatzResearch.WordTrace tailWord_3401229 prefixEnd_3401229 582155097670392803198513 := by
  unfold tailWord_3401229
  simp only [CollatzResearch.WordTrace]
  refine ⟨124053012994935691511798741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82702008663290461007865827 124053012994935691511798741)
  ·
    refine ⟨2907492492068805269807783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 124053012994935691511798741 2907492492068805269807783)
    ·
      refine ⟨4361238738103207904711675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2907492492068805269807783 4361238738103207904711675)
      ·
        refine ⟨6541858107154811857067513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4361238738103207904711675 6541858107154811857067513)
        ·
          refine ⟨4906393580366108892800635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6541858107154811857067513 4906393580366108892800635)
          ·
            refine ⟨7359590370549163339200953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4906393580366108892800635 7359590370549163339200953)
            ·
              refine ⟨5519692777911872504400715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7359590370549163339200953 5519692777911872504400715)
              ·
                refine ⟨8279539166867808756601073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5519692777911872504400715 8279539166867808756601073)
                ·
                  refine ⟨6209654375150856567450805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8279539166867808756601073 6209654375150856567450805)
                  ·
                    refine ⟨582155097670392803198513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6209654375150856567450805 582155097670392803198513)
                    ·
                      rfl

theorem cell23_3401229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_3401229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3401229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3401229 prefixEnd_3401229 := by exact prefixLift 3401229
  have htrace : WordTrace (prefixWord ++ tailWord_3401229) baseStart_3401229 baseEnd_3401229 := by
    simpa [prefixWord, tailWord_3401229, baseEnd_3401229] using wordTrace_append hprefix tailTrace_3401229
  have hstable : (prefixWord ++ tailWord_3401229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401229).length < 2 ^ (prefixWord ++ tailWord_3401229).sum := by decide
  have hdescent : baseEnd_3401229 < baseStart_3401229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401235 : List Nat := [1, 1, 1, 2, 1, 7, 2, 1, 2, 2, 3]
def baseStart_3401235 : Nat := 118140960795 + 3401235 * 2 ^ 59
def prefixEnd_3401235 : Nat := 4983230072969 + 3 ^ 40 * 3401235 * 2
def baseEnd_3401235 : Nat := 1746468373895105386120511

theorem tailTrace_3401235 : CollatzResearch.WordTrace tailWord_3401235 prefixEnd_3401235 1746468373895105386120511 := by
  unfold tailWord_3401235
  simp only [CollatzResearch.WordTrace]
  refine ⟨124053231832913954536517159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82702154555275969691011439 124053231832913954536517159)
  ·
    refine ⟨186079847749370931804775739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124053231832913954536517159 186079847749370931804775739)
    ·
      refine ⟨279119771624056397707163609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186079847749370931804775739 279119771624056397707163609)
      ·
        refine ⟨209339828718042298280372707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279119771624056397707163609 209339828718042298280372707)
        ·
          refine ⟨314009743077063447420559061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209339828718042298280372707 314009743077063447420559061)
          ·
            refine ⟨7359603353368674548919353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 314009743077063447420559061 7359603353368674548919353)
            ·
              refine ⟨5519702515026505911689515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7359603353368674548919353 5519702515026505911689515)
              ·
                refine ⟨8279553772539758867534273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5519702515026505911689515 8279553772539758867534273)
                ·
                  refine ⟨6209665329404819150650705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8279553772539758867534273 6209665329404819150650705)
                  ·
                    refine ⟨4657248997053614362988029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6209665329404819150650705 4657248997053614362988029)
                    ·
                      refine ⟨1746468373895105386120511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4657248997053614362988029 1746468373895105386120511)
                      ·
                        rfl

theorem cell23_3401235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 1, 2, 2, 3].length) (baseStart_3401235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3401235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3401235 prefixEnd_3401235 := by exact prefixLift 3401235
  have htrace : WordTrace (prefixWord ++ tailWord_3401235) baseStart_3401235 baseEnd_3401235 := by
    simpa [prefixWord, tailWord_3401235, baseEnd_3401235] using wordTrace_append hprefix tailTrace_3401235
  have hstable : (prefixWord ++ tailWord_3401235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401235).length < 2 ^ (prefixWord ++ tailWord_3401235).sum := by decide
  have hdescent : baseEnd_3401235 < baseStart_3401235 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401258 : List Nat := [3, 1, 4, 1, 1, 1, 2, 1, 1, 2, 6]
def baseStart_3401258 : Nat := 118140960795 + 3401258 * 2 ^ 59
def prefixEnd_3401258 : Nat := 4983230072969 + 3 ^ 40 * 3401258 * 2
def baseEnd_3401258 : Nat := 1746480183950158796132905

theorem tailTrace_3401258 : CollatzResearch.WordTrace tailWord_3401258 prefixEnd_3401258 1746480183950158796132905 := by
  unfold tailWord_3401258
  simp only [CollatzResearch.WordTrace]
  refine ⟨31013517677957657366151107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82702713807887086309736285 31013517677957657366151107)
  ·
    refine ⟨46520276516936486049226661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31013517677957657366151107 46520276516936486049226661)
    ·
      refine ⟨8722551846925591134229999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46520276516936486049226661 8722551846925591134229999)
      ·
        refine ⟨13083827770388386701344999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8722551846925591134229999 13083827770388386701344999)
        ·
          refine ⟨19625741655582580052017499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13083827770388386701344999 19625741655582580052017499)
          ·
            refine ⟨29438612483373870078026249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19625741655582580052017499 29438612483373870078026249)
            ·
              refine ⟨22078959362530402558519687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29438612483373870078026249 22078959362530402558519687)
              ·
                refine ⟨33118439043795603837779531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22078959362530402558519687 33118439043795603837779531)
                ·
                  refine ⟨49677658565693405756669297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33118439043795603837779531 49677658565693405756669297)
                  ·
                    refine ⟨37258243924270054317501973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49677658565693405756669297 37258243924270054317501973)
                    ·
                      refine ⟨1746480183950158796132905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37258243924270054317501973 1746480183950158796132905)
                      ·
                        rfl

theorem cell23_3401258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_3401258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3401258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3401258 prefixEnd_3401258 := by exact prefixLift 3401258
  have htrace : WordTrace (prefixWord ++ tailWord_3401258) baseStart_3401258 baseEnd_3401258 := by
    simpa [prefixWord, tailWord_3401258, baseEnd_3401258] using wordTrace_append hprefix tailTrace_3401258
  have hstable : (prefixWord ++ tailWord_3401258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401258).length < 2 ^ (prefixWord ++ tailWord_3401258).sum := by decide
  have hdescent : baseEnd_3401258 < baseStart_3401258 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401265 : List Nat := [1, 2, 2, 3, 1, 1, 1, 5, 3, 1, 3]
def baseStart_3401265 : Nat := 118140960795 + 3401265 * 2 ^ 59
def prefixEnd_3401265 : Nat := 4983230072969 + 3 ^ 40 * 3401265 * 2
def baseEnd_3401265 : Nat := 1746483778314740268745373

theorem tailTrace_3401265 : CollatzResearch.WordTrace tailWord_3401265 prefixEnd_3401265 1746483778314740268745373 := by
  unfold tailWord_3401265
  simp only [CollatzResearch.WordTrace]
  refine ⟨124054326022805269660109249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82702884015203513106739499 124054326022805269660109249)
  ·
    refine ⟨93040744517103952245081937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124054326022805269660109249 93040744517103952245081937)
    ·
      refine ⟨69780558387827964183811453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93040744517103952245081937 69780558387827964183811453)
      ·
        refine ⟨26167709395435486568929295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69780558387827964183811453 26167709395435486568929295)
        ·
          refine ⟨39251564093153229853393943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26167709395435486568929295 39251564093153229853393943)
          ·
            refine ⟨58877346139729844780090915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39251564093153229853393943 58877346139729844780090915)
            ·
              refine ⟨88316019209594767170136373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58877346139729844780090915 88316019209594767170136373)
              ·
                refine ⟨8279626800899509422200285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 88316019209594767170136373 8279626800899509422200285)
                ·
                  refine ⟨3104860050337316033325107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8279626800899509422200285 3104860050337316033325107)
                  ·
                    refine ⟨4657290075505974049987661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3104860050337316033325107 4657290075505974049987661)
                    ·
                      refine ⟨1746483778314740268745373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4657290075505974049987661 1746483778314740268745373)
                      ·
                        rfl

theorem cell23_3401265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 5, 3, 1, 3].length) (baseStart_3401265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3401265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3401265 prefixEnd_3401265 := by exact prefixLift 3401265
  have htrace : WordTrace (prefixWord ++ tailWord_3401265) baseStart_3401265 baseEnd_3401265 := by
    simpa [prefixWord, tailWord_3401265, baseEnd_3401265] using wordTrace_append hprefix tailTrace_3401265
  have hstable : (prefixWord ++ tailWord_3401265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401265).length < 2 ^ (prefixWord ++ tailWord_3401265).sum := by decide
  have hdescent : baseEnd_3401265 < baseStart_3401265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401286 : List Nat := [6, 1, 1, 1, 3, 2, 1, 1, 2, 2, 3]
def baseStart_3401286 : Nat := 118140960795 + 3401286 * 2 ^ 59
def prefixEnd_3401286 : Nat := 4983230072969 + 3 ^ 40 * 3401286 * 2
def baseEnd_3401286 : Nat := 1746494561408484686582777

theorem tailTrace_3401286 : CollatzResearch.WordTrace tailWord_3401286 prefixEnd_3401286 1746494561408484686582777 := by
  unfold tailWord_3401286
  simp only [CollatzResearch.WordTrace]
  refine ⟨3876721623616537195206991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 82703394637152793497749141 3876721623616537195206991)
  ·
    refine ⟨5815082435424805792810487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3876721623616537195206991 5815082435424805792810487)
    ·
      refine ⟨8722623653137208689215731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5815082435424805792810487 8722623653137208689215731)
      ·
        refine ⟨13083935479705813033823597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8722623653137208689215731 13083935479705813033823597)
        ·
          refine ⟨4906475804889679887683849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13083935479705813033823597 4906475804889679887683849)
          ·
            refine ⟨3679856853667259915762887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4906475804889679887683849 3679856853667259915762887)
            ·
              refine ⟨5519785280500889873644331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3679856853667259915762887 5519785280500889873644331)
              ·
                refine ⟨8279677920751334810466497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5519785280500889873644331 8279677920751334810466497)
                ·
                  refine ⟨6209758440563501107849873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8279677920751334810466497 6209758440563501107849873)
                  ·
                    refine ⟨4657318830422625830887405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6209758440563501107849873 4657318830422625830887405)
                    ·
                      refine ⟨1746494561408484686582777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4657318830422625830887405 1746494561408484686582777)
                      ·
                        rfl

theorem cell23_3401286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_3401286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3401286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3401286 prefixEnd_3401286 := by exact prefixLift 3401286
  have htrace : WordTrace (prefixWord ++ tailWord_3401286) baseStart_3401286 baseEnd_3401286 := by
    simpa [prefixWord, tailWord_3401286, baseEnd_3401286] using wordTrace_append hprefix tailTrace_3401286
  have hstable : (prefixWord ++ tailWord_3401286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401286).length < 2 ^ (prefixWord ++ tailWord_3401286).sum := by decide
  have hdescent : baseEnd_3401286 < baseStart_3401286 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401292 : List Nat := [2, 2, 1, 3, 1, 3, 3, 1, 2, 3, 2]
def baseStart_3401292 : Nat := 118140960795 + 3401292 * 2 ^ 59
def prefixEnd_3401292 : Nat := 4983230072969 + 3 ^ 40 * 3401292 * 2
def baseEnd_3401292 : Nat := 1746497642292411663107749

theorem tailTrace_3401292 : CollatzResearch.WordTrace tailWord_3401292 prefixEnd_3401292 1746497642292411663107749 := by
  unfold tailWord_3401292
  simp only [CollatzResearch.WordTrace]
  refine ⟨62027655396853726635671065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82703540529138302180894753 62027655396853726635671065)
  ·
    refine ⟨46520741547640294976753299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62027655396853726635671065 46520741547640294976753299)
    ·
      refine ⟨69781112321460442465129949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46520741547640294976753299 69781112321460442465129949)
      ·
        refine ⟨26167917120547665924423731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69781112321460442465129949 26167917120547665924423731)
        ·
          refine ⟨39251875680821498886635597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26167917120547665924423731 39251875680821498886635597)
          ·
            refine ⟨14719453380308062082488349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39251875680821498886635597 14719453380308062082488349)
            ·
              refine ⟨5519795017615523280933131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14719453380308062082488349 5519795017615523280933131)
              ·
                refine ⟨8279692526423284921399697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5519795017615523280933131 8279692526423284921399697)
                ·
                  refine ⟨6209769394817463691049773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8279692526423284921399697 6209769394817463691049773)
                  ·
                    refine ⟨2328663523056548884143665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6209769394817463691049773 2328663523056548884143665)
                    ·
                      refine ⟨1746497642292411663107749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2328663523056548884143665 1746497642292411663107749)
                      ·
                        rfl

theorem cell23_3401292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 1, 2, 3, 2].length) (baseStart_3401292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3401292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3401292 prefixEnd_3401292 := by exact prefixLift 3401292
  have htrace : WordTrace (prefixWord ++ tailWord_3401292) baseStart_3401292 baseEnd_3401292 := by
    simpa [prefixWord, tailWord_3401292, baseEnd_3401292] using wordTrace_append hprefix tailTrace_3401292
  have hstable : (prefixWord ++ tailWord_3401292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401292).length < 2 ^ (prefixWord ++ tailWord_3401292).sum := by decide
  have hdescent : baseEnd_3401292 < baseStart_3401292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401315 : List Nat := [1, 1, 1, 5, 1, 4, 1, 1, 4, 4]
def baseStart_3401315 : Nat := 118140960795 + 3401315 * 2 ^ 59
def prefixEnd_3401315 : Nat := 4983230072969 + 3 ^ 40 * 3401315 * 2
def baseEnd_3401315 : Nat := 582169817449155024373381

theorem tailTrace_3401315 : CollatzResearch.WordTrace tailWord_3401315 prefixEnd_3401315 582169817449155024373381 := by
  unfold tailWord_3401315
  simp only [CollatzResearch.WordTrace]
  refine ⟨124056149672624128199429399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82704099781749418799619599 124056149672624128199429399)
  ·
    refine ⟨186084224508936192299144099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124056149672624128199429399 186084224508936192299144099)
    ·
      refine ⟨279126336763404288448716149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186084224508936192299144099 279126336763404288448716149)
      ·
        refine ⟨26168094071569152042067139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 279126336763404288448716149 26168094071569152042067139)
        ·
          refine ⟨39252141107353728063100709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26168094071569152042067139 39252141107353728063100709)
          ·
            refine ⟨7359776457628824011831383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39252141107353728063100709 7359776457628824011831383)
            ·
              refine ⟨11039664686443236017747075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7359776457628824011831383 11039664686443236017747075)
              ·
                refine ⟨16559497029664854026620613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11039664686443236017747075 16559497029664854026620613)
                ·
                  refine ⟨3104905693062160129991365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16559497029664854026620613 3104905693062160129991365)
                  ·
                    refine ⟨582169817449155024373381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3104905693062160129991365 582169817449155024373381)
                    ·
                      rfl

theorem cell23_3401315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 1, 4, 4].length) (baseStart_3401315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3401315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3401315 prefixEnd_3401315 := by exact prefixLift 3401315
  have htrace : WordTrace (prefixWord ++ tailWord_3401315) baseStart_3401315 baseEnd_3401315 := by
    simpa [prefixWord, tailWord_3401315, baseEnd_3401315] using wordTrace_append hprefix tailTrace_3401315
  have hstable : (prefixWord ++ tailWord_3401315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401315).length < 2 ^ (prefixWord ++ tailWord_3401315).sum := by decide
  have hdescent : baseEnd_3401315 < baseStart_3401315 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401345 : List Nat := [1, 2, 4, 2, 1, 2, 4, 7]
def baseStart_3401345 : Nat := 118140960795 + 3401345 * 2 ^ 59
def prefixEnd_3401345 : Nat := 4983230072969 + 3 ^ 40 * 3401345 * 2
def baseEnd_3401345 : Nat := 64686105806188887249815

theorem tailTrace_3401345 : CollatzResearch.WordTrace tailWord_3401345 prefixEnd_3401345 64686105806188887249815 := by
  unfold tailWord_3401345
  simp only [CollatzResearch.WordTrace]
  refine ⟨124057243862515443323021489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82704829241676962215347659 124057243862515443323021489)
  ·
    refine ⟨93042932896886582492266117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124057243862515443323021489 93042932896886582492266117)
    ·
      refine ⟨17445549918166234217299897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93042932896886582492266117 17445549918166234217299897)
      ·
        refine ⟨13084162438624675662974923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17445549918166234217299897 13084162438624675662974923)
        ·
          refine ⟨19626243657937013494462385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13084162438624675662974923 19626243657937013494462385)
          ·
            refine ⟨14719682743452760120846789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19626243657937013494462385 14719682743452760120846789)
            ·
              refine ⟨2759940514397392522658773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14719682743452760120846789 2759940514397392522658773)
              ·
                refine ⟨64686105806188887249815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2759940514397392522658773 64686105806188887249815)
                ·
                  rfl

theorem cell23_3401345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 4, 7].length) (baseStart_3401345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3401345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3401345 prefixEnd_3401345 := by exact prefixLift 3401345
  have htrace : WordTrace (prefixWord ++ tailWord_3401345) baseStart_3401345 baseEnd_3401345 := by
    simpa [prefixWord, tailWord_3401345, baseEnd_3401345] using wordTrace_append hprefix tailTrace_3401345
  have hstable : (prefixWord ++ tailWord_3401345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401345).length < 2 ^ (prefixWord ++ tailWord_3401345).sum := by decide
  have hdescent : baseEnd_3401345 < baseStart_3401345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401355 : List Nat := [1, 1, 1, 1, 4, 1, 3, 1, 6, 1, 3]
def baseStart_3401355 : Nat := 118140960795 + 3401355 * 2 ^ 59
def prefixEnd_3401355 : Nat := 4983230072969 + 3 ^ 40 * 3401355 * 2
def baseEnd_3401355 : Nat := 1746529991573644916619959

theorem tailTrace_3401355 : CollatzResearch.WordTrace tailWord_3401355 prefixEnd_3401355 1746529991573644916619959 := by
  unfold tailWord_3401355
  simp only [CollatzResearch.WordTrace]
  refine ⟨124057608592479215030885519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82705072394986143353923679 124057608592479215030885519)
  ·
    refine ⟨186086412888718822546328279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124057608592479215030885519 186086412888718822546328279)
    ·
      refine ⟨279129619333078233819492419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186086412888718822546328279 279129619333078233819492419)
      ·
        refine ⟨418694428999617350729238629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279129619333078233819492419 418694428999617350729238629)
        ·
          refine ⟨78505205437428253261732243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 418694428999617350729238629 78505205437428253261732243)
          ·
            refine ⟨117757808156142379892598365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78505205437428253261732243 117757808156142379892598365)
            ·
              refine ⟨44159178058553392459724387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117757808156142379892598365 44159178058553392459724387)
              ·
                refine ⟨66238767087830088689586581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44159178058553392459724387 66238767087830088689586581)
                ·
                  refine ⟨3104942207242035407324371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 66238767087830088689586581 3104942207242035407324371)
                  ·
                    refine ⟨4657413310863053110986557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3104942207242035407324371 4657413310863053110986557)
                    ·
                      refine ⟨1746529991573644916619959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4657413310863053110986557 1746529991573644916619959)
                      ·
                        rfl

theorem cell23_3401355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 6, 1, 3].length) (baseStart_3401355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3401355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3401355 prefixEnd_3401355 := by exact prefixLift 3401355
  have htrace : WordTrace (prefixWord ++ tailWord_3401355) baseStart_3401355 baseEnd_3401355 := by
    simpa [prefixWord, tailWord_3401355, baseEnd_3401355] using wordTrace_append hprefix tailTrace_3401355
  have hstable : (prefixWord ++ tailWord_3401355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401355).length < 2 ^ (prefixWord ++ tailWord_3401355).sum := by decide
  have hdescent : baseEnd_3401355 < baseStart_3401355 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401362 : List Nat := [3, 2, 3, 1, 4, 1, 9]
def baseStart_3401362 : Nat := 118140960795 + 3401362 * 2 ^ 59
def prefixEnd_3401362 : Nat := 4983230072969 + 3 ^ 40 * 3401362 * 2
def baseEnd_3401362 : Nat := 21562143036274399867067

theorem tailTrace_3401362 : CollatzResearch.WordTrace tailWord_3401362 prefixEnd_3401362 21562143036274399867067 := by
  unfold tailWord_3401362
  simp only [CollatzResearch.WordTrace]
  refine ⟨31014465975863463806597585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82705242602302570150926893 31014465975863463806597585)
  ·
    refine ⟨23260849481897597854948189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31014465975863463806597585 23260849481897597854948189)
    ·
      refine ⟨8722818555711599195605571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23260849481897597854948189 8722818555711599195605571)
      ·
        refine ⟨13084227833567398793408357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8722818555711599195605571 13084227833567398793408357)
        ·
          refine ⟨2453292718793887273764067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13084227833567398793408357 2453292718793887273764067)
          ·
            refine ⟨3679939078190830910646101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2453292718793887273764067 3679939078190830910646101)
            ·
              refine ⟨21562143036274399867067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3679939078190830910646101 21562143036274399867067)
              ·
                rfl

theorem cell23_3401362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 9].length) (baseStart_3401362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3401362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3401362 prefixEnd_3401362 := by exact prefixLift 3401362
  have htrace : WordTrace (prefixWord ++ tailWord_3401362) baseStart_3401362 baseEnd_3401362 := by
    simpa [prefixWord, tailWord_3401362, baseEnd_3401362] using wordTrace_append hprefix tailTrace_3401362
  have hstable : (prefixWord ++ tailWord_3401362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401362).length < 2 ^ (prefixWord ++ tailWord_3401362).sum := by decide
  have hdescent : baseEnd_3401362 < baseStart_3401362 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401389 : List Nat := [1, 5, 2, 1, 1, 1, 3, 3, 2, 1, 3]
def baseStart_3401389 : Nat := 118140960795 + 3401389 * 2 ^ 59
def prefixEnd_3401389 : Nat := 4983230072969 + 3 ^ 40 * 3401389 * 2
def baseEnd_3401389 : Nat := 1746547449915897783594803

theorem tailTrace_3401389 : CollatzResearch.WordTrace tailWord_3401389 prefixEnd_3401389 1746547449915897783594803 := by
  unfold tailWord_3401389
  simp only [CollatzResearch.WordTrace]
  refine ⟨124058848674356038837623221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82705899116237359225082147 124058848674356038837623221)
  ·
    refine ⟨11630517063220878641027177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 124058848674356038837623221 11630517063220878641027177)
    ·
      refine ⟨8722887797415658980770383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11630517063220878641027177 8722887797415658980770383)
      ·
        refine ⟨13084331696123488471155575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8722887797415658980770383 13084331696123488471155575)
        ·
          refine ⟨19626497544185232706733363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13084331696123488471155575 19626497544185232706733363)
          ·
            refine ⟨29439746316277849060100045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19626497544185232706733363 29439746316277849060100045)
            ·
              refine ⟨11039904868604193397537517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29439746316277849060100045 11039904868604193397537517)
              ·
                refine ⟨4139964325726572524076569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11039904868604193397537517 4139964325726572524076569)
                ·
                  refine ⟨3104973244294929393057427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4139964325726572524076569 3104973244294929393057427)
                  ·
                    refine ⟨4657459866442394089586141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3104973244294929393057427 4657459866442394089586141)
                    ·
                      refine ⟨1746547449915897783594803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4657459866442394089586141 1746547449915897783594803)
                      ·
                        rfl

theorem cell23_3401389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_3401389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3401389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3401389 prefixEnd_3401389 := by exact prefixLift 3401389
  have htrace : WordTrace (prefixWord ++ tailWord_3401389) baseStart_3401389 baseEnd_3401389 := by
    simpa [prefixWord, tailWord_3401389, baseEnd_3401389] using wordTrace_append hprefix tailTrace_3401389
  have hstable : (prefixWord ++ tailWord_3401389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401389).length < 2 ^ (prefixWord ++ tailWord_3401389).sum := by decide
  have hdescent : baseEnd_3401389 < baseStart_3401389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401399 : List Nat := [1, 1, 3, 1, 5, 1, 3, 2, 1, 3, 2]
def baseStart_3401399 : Nat := 118140960795 + 3401399 * 2 ^ 59
def prefixEnd_3401399 : Nat := 4983230072969 + 3 ^ 40 * 3401399 * 2
def baseEnd_3401399 : Nat := 1746552584722442744469757

theorem tailTrace_3401399 : CollatzResearch.WordTrace tailWord_3401399 prefixEnd_3401399 1746552584722442744469757 := by
  unfold tailWord_3401399
  simp only [CollatzResearch.WordTrace]
  refine ⟨124059213404319810545487251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82706142269546540363658167 124059213404319810545487251)
  ·
    refine ⟨186088820106479715818230877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124059213404319810545487251 186088820106479715818230877)
    ·
      refine ⟨69783307539929893431836579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186088820106479715818230877 69783307539929893431836579)
      ·
        refine ⟨104674961309894840147754869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69783307539929893431836579 104674961309894840147754869)
        ·
          refine ⟨9813277622802641263852019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 104674961309894840147754869 9813277622802641263852019)
          ·
            refine ⟨14719916434203961895778029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9813277622802641263852019 14719916434203961895778029)
            ·
              refine ⟨5519968662826485710916761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14719916434203961895778029 5519968662826485710916761)
              ·
                refine ⟨4139976497119864283187571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5519968662826485710916761 4139976497119864283187571)
                ·
                  refine ⟨6209964745679796424781357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4139976497119864283187571 6209964745679796424781357)
                  ·
                    refine ⟨2328736779629923659293009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6209964745679796424781357 2328736779629923659293009)
                    ·
                      refine ⟨1746552584722442744469757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2328736779629923659293009 1746552584722442744469757)
                      ·
                        rfl

theorem cell23_3401399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 2, 1, 3, 2].length) (baseStart_3401399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3401399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3401399 prefixEnd_3401399 := by exact prefixLift 3401399
  have htrace : WordTrace (prefixWord ++ tailWord_3401399) baseStart_3401399 baseEnd_3401399 := by
    simpa [prefixWord, tailWord_3401399, baseEnd_3401399] using wordTrace_append hprefix tailTrace_3401399
  have hstable : (prefixWord ++ tailWord_3401399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401399).length < 2 ^ (prefixWord ++ tailWord_3401399).sum := by decide
  have hdescent : baseEnd_3401399 < baseStart_3401399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401410 : List Nat := [3, 5, 1, 2, 1, 1, 3, 1, 1, 2, 3]
def baseStart_3401410 : Nat := 118140960795 + 3401410 * 2 ^ 59
def prefixEnd_3401410 : Nat := 4983230072969 + 3 ^ 40 * 3401410 * 2
def baseEnd_3401410 : Nat := 1746558233009642201432207

theorem tailTrace_3401410 : CollatzResearch.WordTrace tailWord_3401410 prefixEnd_3401410 1746558233009642201432207 := by
  unfold tailWord_3401410
  simp only [CollatzResearch.WordTrace]
  refine ⟨31014903651819989856034421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82706409738186639616091789 31014903651819989856034421)
  ·
    refine ⟨2907647217358124049003227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31014903651819989856034421 2907647217358124049003227)
    ·
      refine ⟨4361470826037186073504841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2907647217358124049003227 4361470826037186073504841)
      ·
        refine ⟨3271103119527889555128631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4361470826037186073504841 3271103119527889555128631)
        ·
          refine ⟨4906654679291834332692947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3271103119527889555128631 4906654679291834332692947)
          ·
            refine ⟨7359982018937751499039421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4906654679291834332692947 7359982018937751499039421)
            ·
              refine ⟨2759993257101656812139783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7359982018937751499039421 2759993257101656812139783)
              ·
                refine ⟨4139989885652485218209675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2759993257101656812139783 4139989885652485218209675)
                ·
                  refine ⟨6209984828478727827314513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4139989885652485218209675 6209984828478727827314513)
                  ·
                    refine ⟨4657488621359045870485885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6209984828478727827314513 4657488621359045870485885)
                    ·
                      refine ⟨1746558233009642201432207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4657488621359045870485885 1746558233009642201432207)
                      ·
                        rfl

theorem cell23_3401410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_3401410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3401410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3401410 prefixEnd_3401410 := by exact prefixLift 3401410
  have htrace : WordTrace (prefixWord ++ tailWord_3401410) baseStart_3401410 baseEnd_3401410 := by
    simpa [prefixWord, tailWord_3401410, baseEnd_3401410] using wordTrace_append hprefix tailTrace_3401410
  have hstable : (prefixWord ++ tailWord_3401410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401410).length < 2 ^ (prefixWord ++ tailWord_3401410).sum := by decide
  have hdescent : baseEnd_3401410 < baseStart_3401410 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401522 : List Nat := [3, 2, 1, 1, 3, 2, 2, 1, 1, 4, 3]
def baseStart_3401522 : Nat := 118140960795 + 3401522 * 2 ^ 59
def prefixEnd_3401522 : Nat := 4983230072969 + 3 ^ 40 * 3401522 * 2
def baseEnd_3401522 : Nat := 1746615742842945763231691

theorem tailTrace_3401522 : CollatzResearch.WordTrace tailWord_3401522 prefixEnd_3401522 1746615742842945763231691 := by
  unfold tailWord_3401522
  simp only [CollatzResearch.WordTrace]
  refine ⟨31015924895718550638053705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82709133055249468368143213 31015924895718550638053705)
  ·
    refine ⟨23261943671788912978540279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31015924895718550638053705 23261943671788912978540279)
    ·
      refine ⟨34892915507683369467810419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23261943671788912978540279 34892915507683369467810419)
      ·
        refine ⟨52339373261525054201715629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34892915507683369467810419 52339373261525054201715629)
        ·
          refine ⟨19627264973071895325643361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52339373261525054201715629 19627264973071895325643361)
          ·
            refine ⟨14720448729803921494232521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19627264973071895325643361 14720448729803921494232521)
            ·
              refine ⟨11040336547352941120674391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14720448729803921494232521 11040336547352941120674391)
              ·
                refine ⟨16560504821029411681011587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11040336547352941120674391 16560504821029411681011587)
                ·
                  refine ⟨24840757231544117521517381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16560504821029411681011587 24840757231544117521517381)
                  ·
                    refine ⟨4657641980914522035284509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24840757231544117521517381 4657641980914522035284509)
                    ·
                      refine ⟨1746615742842945763231691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4657641980914522035284509 1746615742842945763231691)
                      ·
                        rfl

theorem cell23_3401522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 1, 1, 4, 3].length) (baseStart_3401522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3401522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3401522 prefixEnd_3401522 := by exact prefixLift 3401522
  have htrace : WordTrace (prefixWord ++ tailWord_3401522) baseStart_3401522 baseEnd_3401522 := by
    simpa [prefixWord, tailWord_3401522, baseEnd_3401522] using wordTrace_append hprefix tailTrace_3401522
  have hstable : (prefixWord ++ tailWord_3401522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401522).length < 2 ^ (prefixWord ++ tailWord_3401522).sum := by decide
  have hdescent : baseEnd_3401522 < baseStart_3401522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401546 : List Nat := [3, 1, 2, 1, 1, 1, 7, 2, 1, 4]
def baseStart_3401546 : Nat := 118140960795 + 3401546 * 2 ^ 59
def prefixEnd_3401546 : Nat := 4983230072969 + 3 ^ 40 * 3401546 * 2
def baseEnd_3401546 : Nat := 582209355459551223110527

theorem tailTrace_3401546 : CollatzResearch.WordTrace tailWord_3401546 prefixEnd_3401546 582209355459551223110527 := by
  unfold tailWord_3401546
  simp only [CollatzResearch.WordTrace]
  refine ⟨31016143733696813662772123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82709716623191503100725661 31016143733696813662772123)
  ·
    refine ⟨46524215600545220494158185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31016143733696813662772123 46524215600545220494158185)
    ·
      refine ⟨34893161700408915370618639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46524215600545220494158185 34893161700408915370618639)
      ·
        refine ⟨52339742550613373055927959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34893161700408915370618639 52339742550613373055927959)
        ·
          refine ⟨78509613825920059583891939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52339742550613373055927959 78509613825920059583891939)
          ·
            refine ⟨117764420738880089375837909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78509613825920059583891939 117764420738880089375837909)
            ·
              refine ⟨2760103611067502094746201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 117764420738880089375837909 2760103611067502094746201)
              ·
                refine ⟨2070077708300626571059651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2760103611067502094746201 2070077708300626571059651)
                ·
                  refine ⟨3105116562450939856589477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2070077708300626571059651 3105116562450939856589477)
                  ·
                    refine ⟨582209355459551223110527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3105116562450939856589477 582209355459551223110527)
                    ·
                      rfl

theorem cell23_3401546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 7, 2, 1, 4].length) (baseStart_3401546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3401546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3401546 prefixEnd_3401546 := by exact prefixLift 3401546
  have htrace : WordTrace (prefixWord ++ tailWord_3401546) baseStart_3401546 baseEnd_3401546 := by
    simpa [prefixWord, tailWord_3401546, baseEnd_3401546] using wordTrace_append hprefix tailTrace_3401546
  have hstable : (prefixWord ++ tailWord_3401546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401546).length < 2 ^ (prefixWord ++ tailWord_3401546).sum := by decide
  have hdescent : baseEnd_3401546 < baseStart_3401546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401586 : List Nat := [3, 2, 1, 2, 1, 1, 1, 7, 1, 1, 3]
def baseStart_3401586 : Nat := 118140960795 + 3401586 * 2 ^ 59
def prefixEnd_3401586 : Nat := 4983230072969 + 3 ^ 40 * 3401586 * 2
def baseEnd_3401586 : Nat := 1746648605604833512831397

theorem tailTrace_3401586 : CollatzResearch.WordTrace tailWord_3401586 prefixEnd_3401586 1746648605604833512831397 := by
  unfold tailWord_3401586
  simp only [CollatzResearch.WordTrace]
  refine ⟨31016508463660585370636153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82710689236428227655029741 31016508463660585370636153)
  ·
    refine ⟨23262381347745439027977115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31016508463660585370636153 23262381347745439027977115)
    ·
      refine ⟨34893572021618158541965673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23262381347745439027977115 34893572021618158541965673)
      ·
        refine ⟨26170179016213618906474255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34893572021618158541965673 26170179016213618906474255)
        ·
          refine ⟨39255268524320428359711383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26170179016213618906474255 39255268524320428359711383)
          ·
            refine ⟨58882902786480642539567075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39255268524320428359711383 58882902786480642539567075)
            ·
              refine ⟨88324354179720963809350613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58882902786480642539567075 88324354179720963809350613)
              ·
                refine ⟨2070102051087210089281655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 88324354179720963809350613 2070102051087210089281655)
                ·
                  refine ⟨3105153076630815133922483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2070102051087210089281655 3105153076630815133922483)
                  ·
                    refine ⟨4657729614946222700883725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3105153076630815133922483 4657729614946222700883725)
                    ·
                      refine ⟨1746648605604833512831397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4657729614946222700883725 1746648605604833512831397)
                      ·
                        rfl

theorem cell23_3401586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 7, 1, 1, 3].length) (baseStart_3401586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3401586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3401586 prefixEnd_3401586 := by exact prefixLift 3401586
  have htrace : WordTrace (prefixWord ++ tailWord_3401586) baseStart_3401586 baseEnd_3401586 := by
    simpa [prefixWord, tailWord_3401586, baseEnd_3401586] using wordTrace_append hprefix tailTrace_3401586
  have hstable : (prefixWord ++ tailWord_3401586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401586).length < 2 ^ (prefixWord ++ tailWord_3401586).sum := by decide
  have hdescent : baseEnd_3401586 < baseStart_3401586 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401592 : List Nat := [2, 1, 2, 1, 1, 1, 1, 2, 4, 6, 2]
def baseStart_3401592 : Nat := 118140960795 + 3401592 * 2 ^ 59
def prefixEnd_3401592 : Nat := 4983230072969 + 3 ^ 40 * 3401592 * 2
def baseEnd_3401592 : Nat := 1746651686488760489356369

theorem tailTrace_3401592 : CollatzResearch.WordTrace tailWord_3401592 prefixEnd_3401592 1746651686488760489356369 := by
  unfold tailWord_3401592
  simp only [CollatzResearch.WordTrace]
  refine ⟨62033126346310302253631515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82710835128413736338175353 62033126346310302253631515)
  ·
    refine ⟨93049689519465453380447273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62033126346310302253631515 93049689519465453380447273)
    ·
      refine ⟨69787267139599090035335455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93049689519465453380447273 69787267139599090035335455)
      ·
        refine ⟨104680900709398635053003183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69787267139599090035335455 104680900709398635053003183)
        ·
          refine ⟨157021351064097952579504775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104680900709398635053003183 157021351064097952579504775)
          ·
            refine ⟨235532026596146928869257163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157021351064097952579504775 235532026596146928869257163)
            ·
              refine ⟨353298039894220393303885745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235532026596146928869257163 353298039894220393303885745)
              ·
                refine ⟨264973529920665294977914309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 353298039894220393303885745 264973529920665294977914309)
                ·
                  refine ⟨49682536860124742808358933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 264973529920665294977914309 49682536860124742808358933)
                  ·
                    refine ⟨2328868915318347319141825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 49682536860124742808358933 2328868915318347319141825)
                    ·
                      refine ⟨1746651686488760489356369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2328868915318347319141825 1746651686488760489356369)
                      ·
                        rfl

theorem cell23_3401592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 4, 6, 2].length) (baseStart_3401592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3401592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3401592 prefixEnd_3401592 := by exact prefixLift 3401592
  have htrace : WordTrace (prefixWord ++ tailWord_3401592) baseStart_3401592 baseEnd_3401592 := by
    simpa [prefixWord, tailWord_3401592, baseEnd_3401592] using wordTrace_append hprefix tailTrace_3401592
  have hstable : (prefixWord ++ tailWord_3401592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401592).length < 2 ^ (prefixWord ++ tailWord_3401592).sum := by decide
  have hdescent : baseEnd_3401592 < baseStart_3401592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401603 : List Nat := [1, 1, 1, 3, 4, 2, 4, 2, 1, 1, 3]
def baseStart_3401603 : Nat := 118140960795 + 3401603 * 2 ^ 59
def prefixEnd_3401603 : Nat := 4983230072969 + 3 ^ 40 * 3401603 * 2
def baseEnd_3401603 : Nat := 1746657334775959946318819

theorem tailTrace_3401603 : CollatzResearch.WordTrace tailWord_3401603 prefixEnd_3401603 1746657334775959946318819 := by
  unfold tailWord_3401603
  simp only [CollatzResearch.WordTrace]
  refine ⟨124066653895580753385913463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82711102597053835590608975 124066653895580753385913463)
  ·
    refine ⟨186099980843371130078870195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124066653895580753385913463 186099980843371130078870195)
    ·
      refine ⟨279149971265056695118305293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186099980843371130078870195 279149971265056695118305293)
      ·
        refine ⟨104681239224396260669364485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 279149971265056695118305293 104681239224396260669364485)
        ·
          refine ⟨19627732354574298875505841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104681239224396260669364485 19627732354574298875505841)
          ·
            refine ⟨14720799265930724156629381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19627732354574298875505841 14720799265930724156629381)
            ·
              refine ⟨2760149862362010779368009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14720799265930724156629381 2760149862362010779368009)
              ·
                refine ⟨2070112396771508084526007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2760149862362010779368009 2070112396771508084526007)
                ·
                  refine ⟨3105168595157262126789011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2070112396771508084526007 3105168595157262126789011)
                  ·
                    refine ⟨4657752892735893190183517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3105168595157262126789011 4657752892735893190183517)
                    ·
                      refine ⟨1746657334775959946318819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4657752892735893190183517 1746657334775959946318819)
                      ·
                        rfl

theorem cell23_3401603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 4, 2, 1, 1, 3].length) (baseStart_3401603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3401603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3401603 prefixEnd_3401603 := by exact prefixLift 3401603
  have htrace : WordTrace (prefixWord ++ tailWord_3401603) baseStart_3401603 baseEnd_3401603 := by
    simpa [prefixWord, tailWord_3401603, baseEnd_3401603] using wordTrace_append hprefix tailTrace_3401603
  have hstable : (prefixWord ++ tailWord_3401603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401603).length < 2 ^ (prefixWord ++ tailWord_3401603).sum := by decide
  have hdescent : baseEnd_3401603 < baseStart_3401603 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401626 : List Nat := [3, 1, 1, 4, 2, 1, 1, 1, 5, 2, 2]
def baseStart_3401626 : Nat := 118140960795 + 3401626 * 2 ^ 59
def prefixEnd_3401626 : Nat := 4983230072969 + 3 ^ 40 * 3401626 * 2
def baseEnd_3401626 : Nat := 1746669144831013356331213

theorem tailTrace_3401626 : CollatzResearch.WordTrace tailWord_3401626 prefixEnd_3401626 1746669144831013356331213 := by
  unfold tailWord_3401626
  simp only [CollatzResearch.WordTrace]
  refine ⟨31016873193624357078500183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82711661849664952209333821 31016873193624357078500183)
  ·
    refine ⟨46525309790436535617750275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31016873193624357078500183 46525309790436535617750275)
    ·
      refine ⟨69787964685654803426625413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46525309790436535617750275 69787964685654803426625413)
      ·
        refine ⟨13085243378560275642492265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69787964685654803426625413 13085243378560275642492265)
        ·
          refine ⟨9813932533920206731869199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13085243378560275642492265 9813932533920206731869199)
          ·
            refine ⟨14720898800880310097803799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9813932533920206731869199 14720898800880310097803799)
            ·
              refine ⟨22081348201320465146705699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14720898800880310097803799 22081348201320465146705699)
              ·
                refine ⟨33122022301980697720058549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22081348201320465146705699 33122022301980697720058549)
                ·
                  refine ⟨3105189590810690411255489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33122022301980697720058549 3105189590810690411255489)
                  ·
                    refine ⟨2328892193108017808441617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3105189590810690411255489 2328892193108017808441617)
                    ·
                      refine ⟨1746669144831013356331213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2328892193108017808441617 1746669144831013356331213)
                      ·
                        rfl

theorem cell23_3401626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 5, 2, 2].length) (baseStart_3401626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3401626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3401626 prefixEnd_3401626 := by exact prefixLift 3401626
  have htrace : WordTrace (prefixWord ++ tailWord_3401626) baseStart_3401626 baseEnd_3401626 := by
    simpa [prefixWord, tailWord_3401626, baseEnd_3401626] using wordTrace_append hprefix tailTrace_3401626
  have hstable : (prefixWord ++ tailWord_3401626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401626).length < 2 ^ (prefixWord ++ tailWord_3401626).sum := by decide
  have hdescent : baseEnd_3401626 < baseStart_3401626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401629 : List Nat := [1, 4, 2, 1, 2, 2, 2, 1, 3, 2, 3]
def baseStart_3401629 : Nat := 118140960795 + 3401629 * 2 ^ 59
def prefixEnd_3401629 : Nat := 4983230072969 + 3 ^ 40 * 3401629 * 2
def baseEnd_3401629 : Nat := 1746670685272976844593699

theorem tailTrace_3401629 : CollatzResearch.WordTrace tailWord_3401629 prefixEnd_3401629 1746670685272976844593699 := by
  unfold tailWord_3401629
  simp only [CollatzResearch.WordTrace]
  refine ⟨124067602193486559826359941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82711734795657706550906627 124067602193486559826359941)
  ·
    refine ⟨23262675411278729967442489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124067602193486559826359941 23262675411278729967442489)
    ·
      refine ⟨17447006558459047475581867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23262675411278729967442489 17447006558459047475581867)
      ·
        refine ⟨26170509837688571213372801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17447006558459047475581867 26170509837688571213372801)
        ·
          refine ⟨19627882378266428410029601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26170509837688571213372801 19627882378266428410029601)
          ·
            refine ⟨14720911783699821307522201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19627882378266428410029601 14720911783699821307522201)
            ·
              refine ⟨11040683837774865980641651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14720911783699821307522201 11040683837774865980641651)
              ·
                refine ⟨16561025756662298970962477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11040683837774865980641651 16561025756662298970962477)
                ·
                  refine ⟨6210384658748362114110929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16561025756662298970962477 6210384658748362114110929)
                  ·
                    refine ⟨4657788494061271585583197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6210384658748362114110929 4657788494061271585583197)
                    ·
                      refine ⟨1746670685272976844593699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4657788494061271585583197 1746670685272976844593699)
                      ·
                        rfl

theorem cell23_3401629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 1, 3, 2, 3].length) (baseStart_3401629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3401629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3401629 prefixEnd_3401629 := by exact prefixLift 3401629
  have htrace : WordTrace (prefixWord ++ tailWord_3401629) baseStart_3401629 baseEnd_3401629 := by
    simpa [prefixWord, tailWord_3401629, baseEnd_3401629] using wordTrace_append hprefix tailTrace_3401629
  have hstable : (prefixWord ++ tailWord_3401629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401629).length < 2 ^ (prefixWord ++ tailWord_3401629).sum := by decide
  have hdescent : baseEnd_3401629 < baseStart_3401629 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401639 : List Nat := [1, 1, 6, 1, 2, 1, 2, 2, 1, 2, 4]
def baseStart_3401639 : Nat := 118140960795 + 3401639 * 2 ^ 59
def prefixEnd_3401639 : Nat := 4983230072969 + 3 ^ 40 * 3401639 * 2
def baseEnd_3401639 : Nat := 1746675820079521805468653

theorem tailTrace_3401639 : CollatzResearch.WordTrace tailWord_3401639 prefixEnd_3401639 1746675820079521805468653 := by
  unfold tailWord_3401639
  simp only [CollatzResearch.WordTrace]
  refine ⟨124067966923450331534223971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82711977948966887689482647 124067966923450331534223971)
  ·
    refine ⟨186101950385175497301335957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124067966923450331534223971 186101950385175497301335957)
    ·
      refine ⟨8723528924305101436000123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 186101950385175497301335957 8723528924305101436000123)
      ·
        refine ⟨13085293386457652154000185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8723528924305101436000123 13085293386457652154000185)
        ·
          refine ⟨9813970039843239115500139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13085293386457652154000185 9813970039843239115500139)
          ·
            refine ⟨14720955059764858673250209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9813970039843239115500139 14720955059764858673250209)
            ·
              refine ⟨11040716294823644004937657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14720955059764858673250209 11040716294823644004937657)
              ·
                refine ⟨8280537221117733003703243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11040716294823644004937657 8280537221117733003703243)
                ·
                  refine ⟨12420805831676599505554865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8280537221117733003703243 12420805831676599505554865)
                  ·
                    refine ⟨9315604373757449629166149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12420805831676599505554865 9315604373757449629166149)
                    ·
                      refine ⟨1746675820079521805468653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9315604373757449629166149 1746675820079521805468653)
                      ·
                        rfl

theorem cell23_3401639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_3401639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3401639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3401639 prefixEnd_3401639 := by exact prefixLift 3401639
  have htrace : WordTrace (prefixWord ++ tailWord_3401639) baseStart_3401639 baseEnd_3401639 := by
    simpa [prefixWord, tailWord_3401639, baseEnd_3401639] using wordTrace_append hprefix tailTrace_3401639
  have hstable : (prefixWord ++ tailWord_3401639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401639).length < 2 ^ (prefixWord ++ tailWord_3401639).sum := by decide
  have hdescent : baseEnd_3401639 < baseStart_3401639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401640 : List Nat := [2, 1, 6, 2, 1, 2, 2, 1, 1, 5]
def baseStart_3401640 : Nat := 118140960795 + 3401640 * 2 ^ 59
def prefixEnd_3401640 : Nat := 4983230072969 + 3 ^ 40 * 3401640 * 2
def baseEnd_3401640 : Nat := 582225444520058767185383

theorem tailTrace_3401640 : CollatzResearch.WordTrace tailWord_3401640 prefixEnd_3401640 582225444520058767185383 := by
  unfold tailWord_3401640
  simp only [CollatzResearch.WordTrace]
  refine ⟨62034001698223354352505187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82712002264297805803340249 62034001698223354352505187)
  ·
    refine ⟨93051002547335031528757781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62034001698223354352505187 93051002547335031528757781)
    ·
      refine ⟨4361765744406329602910521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 93051002547335031528757781 4361765744406329602910521)
      ·
        refine ⟨3271324308304747202182891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4361765744406329602910521 3271324308304747202182891)
        ·
          refine ⟨4906986462457120803274337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3271324308304747202182891 4906986462457120803274337)
          ·
            refine ⟨3680239846842840602455753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4906986462457120803274337 3680239846842840602455753)
            ·
              refine ⟨2760179885132130451841815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3680239846842840602455753 2760179885132130451841815)
              ·
                refine ⟨4140269827698195677762723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2760179885132130451841815 4140269827698195677762723)
                ·
                  refine ⟨6210404741547293516644085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4140269827698195677762723 6210404741547293516644085)
                  ·
                    refine ⟨582225444520058767185383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6210404741547293516644085 582225444520058767185383)
                    ·
                      rfl

theorem cell23_3401640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_3401640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3401640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3401640 prefixEnd_3401640 := by exact prefixLift 3401640
  have htrace : WordTrace (prefixWord ++ tailWord_3401640) baseStart_3401640 baseEnd_3401640 := by
    simpa [prefixWord, tailWord_3401640, baseEnd_3401640] using wordTrace_append hprefix tailTrace_3401640
  have hstable : (prefixWord ++ tailWord_3401640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401640).length < 2 ^ (prefixWord ++ tailWord_3401640).sum := by decide
  have hdescent : baseEnd_3401640 < baseStart_3401640 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401660 : List Nat := [2, 2, 2, 5, 1, 1, 2, 1, 3, 2, 2]
def baseStart_3401660 : Nat := 118140960795 + 3401660 * 2 ^ 59
def prefixEnd_3401660 : Nat := 4983230072969 + 3 ^ 40 * 3401660 * 2
def baseEnd_3401660 : Nat := 1746686603173266223306057

theorem tailTrace_3401660 : CollatzResearch.WordTrace tailWord_3401660 prefixEnd_3401660 1746686603173266223306057 := by
  unfold tailWord_3401660
  simp only [CollatzResearch.WordTrace]
  refine ⟨62034366428187126060369217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82712488570916168080492289 62034366428187126060369217)
  ·
    refine ⟨46525774821140344545276913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62034366428187126060369217 46525774821140344545276913)
    ·
      refine ⟨34894331115855258408957685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46525774821140344545276913 34894331115855258408957685)
      ·
        refine ⟨3271343542111430475839783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34894331115855258408957685 3271343542111430475839783)
        ·
          refine ⟨4907015313167145713759675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3271343542111430475839783 4907015313167145713759675)
          ·
            refine ⟨7360522969750718570639513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4907015313167145713759675 7360522969750718570639513)
            ·
              refine ⟨5520392227313038927979635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7360522969750718570639513 5520392227313038927979635)
              ·
                refine ⟨8280588340969558391969453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5520392227313038927979635 8280588340969558391969453)
                ·
                  refine ⟨3105220627863584396988545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8280588340969558391969453 3105220627863584396988545)
                  ·
                    refine ⟨2328915470897688297741409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3105220627863584396988545 2328915470897688297741409)
                    ·
                      refine ⟨1746686603173266223306057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2328915470897688297741409 1746686603173266223306057)
                      ·
                        rfl

theorem cell23_3401660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_3401660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3401660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3401660 prefixEnd_3401660 := by exact prefixLift 3401660
  have htrace : WordTrace (prefixWord ++ tailWord_3401660) baseStart_3401660 baseEnd_3401660 := by
    simpa [prefixWord, tailWord_3401660, baseEnd_3401660] using wordTrace_append hprefix tailTrace_3401660
  have hstable : (prefixWord ++ tailWord_3401660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401660).length < 2 ^ (prefixWord ++ tailWord_3401660).sum := by decide
  have hdescent : baseEnd_3401660 < baseStart_3401660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401669 : List Nat := [1, 3, 1, 1, 1, 1, 1, 6, 3, 3, 2]
def baseStart_3401669 : Nat := 118140960795 + 3401669 * 2 ^ 59
def prefixEnd_3401669 : Nat := 4983230072969 + 3 ^ 40 * 3401669 * 2
def baseEnd_3401669 : Nat := 1746691224499156688093515

theorem tailTrace_3401669 : CollatzResearch.WordTrace tailWord_3401669 prefixEnd_3401669 1746691224499156688093515 := by
  unfold tailWord_3401669
  simp only [CollatzResearch.WordTrace]
  refine ⟨124069061113341646657816061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82712707408894431105210707 124069061113341646657816061)
  ·
    refine ⟨46525897917503117496681023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124069061113341646657816061 46525897917503117496681023)
    ·
      refine ⟨69788846876254676245021535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46525897917503117496681023 69788846876254676245021535)
      ·
        refine ⟨104683270314382014367532303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69788846876254676245021535 104683270314382014367532303)
        ·
          refine ⟨157024905471573021551298455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104683270314382014367532303 157024905471573021551298455)
          ·
            refine ⟨235537358207359532326947683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157024905471573021551298455 235537358207359532326947683)
            ·
              refine ⟨353306037311039298490421525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235537358207359532326947683 353306037311039298490421525)
              ·
                refine ⟨16561220498954967116738509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 353306037311039298490421525 16561220498954967116738509)
                ·
                  refine ⟨6210457687108112668776941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16561220498954967116738509 6210457687108112668776941)
                  ·
                    refine ⟨2328921632665542250791353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6210457687108112668776941 2328921632665542250791353)
                    ·
                      refine ⟨1746691224499156688093515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2328921632665542250791353 1746691224499156688093515)
                      ·
                        rfl

theorem cell23_3401669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 6, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 6, 3, 3, 2].length) (baseStart_3401669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3401669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3401669 prefixEnd_3401669 := by exact prefixLift 3401669
  have htrace : WordTrace (prefixWord ++ tailWord_3401669) baseStart_3401669 baseEnd_3401669 := by
    simpa [prefixWord, tailWord_3401669, baseEnd_3401669] using wordTrace_append hprefix tailTrace_3401669
  have hstable : (prefixWord ++ tailWord_3401669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401669).length < 2 ^ (prefixWord ++ tailWord_3401669).sum := by decide
  have hdescent : baseEnd_3401669 < baseStart_3401669 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401676 : List Nat := [2, 2, 1, 4, 1, 4, 1, 1, 1, 3, 3]
def baseStart_3401676 : Nat := 118140960795 + 3401676 * 2 ^ 59
def prefixEnd_3401676 : Nat := 4983230072969 + 3 ^ 40 * 3401676 * 2
def baseEnd_3401676 : Nat := 1746694818863738160705983

theorem tailTrace_3401676 : CollatzResearch.WordTrace tailWord_3401676 prefixEnd_3401676 1746694818863738160705983 := by
  unfold tailWord_3401676
  simp only [CollatzResearch.WordTrace]
  refine ⟨62034658212158143426660441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82712877616210857902213921 62034658212158143426660441)
  ·
    refine ⟨46525993659118607569995331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62034658212158143426660441 46525993659118607569995331)
    ·
      refine ⟨69788990488677911354992997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46525993659118607569995331 69788990488677911354992997)
      ·
        refine ⟨13085435716627108379061187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69788990488677911354992997 13085435716627108379061187)
        ·
          refine ⟨19628153574940662568591781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13085435716627108379061187 19628153574940662568591781)
          ·
            refine ⟨3680278795301374231610959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19628153574940662568591781 3680278795301374231610959)
            ·
              refine ⟨5520418192952061347416439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3680278795301374231610959 5520418192952061347416439)
              ·
                refine ⟨8280627289428092021124659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5520418192952061347416439 8280627289428092021124659)
                ·
                  refine ⟨12420940934142138031686989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8280627289428092021124659 12420940934142138031686989)
                  ·
                    refine ⟨4657852850303301761882621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12420940934142138031686989 4657852850303301761882621)
                    ·
                      refine ⟨1746694818863738160705983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4657852850303301761882621 1746694818863738160705983)
                      ·
                        rfl

theorem cell23_3401676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_3401676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3401676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3401676 prefixEnd_3401676 := by exact prefixLift 3401676
  have htrace : WordTrace (prefixWord ++ tailWord_3401676) baseStart_3401676 baseEnd_3401676 := by
    simpa [prefixWord, tailWord_3401676, baseEnd_3401676] using wordTrace_append hprefix tailTrace_3401676
  have hstable : (prefixWord ++ tailWord_3401676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401676).length < 2 ^ (prefixWord ++ tailWord_3401676).sum := by decide
  have hdescent : baseEnd_3401676 < baseStart_3401676 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401712 : List Nat := [2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 4]
def baseStart_3401712 : Nat := 118140960795 + 3401712 * 2 ^ 59
def prefixEnd_3401712 : Nat := 4983230072969 + 3 ^ 40 * 3401712 * 2
def baseEnd_3401712 : Nat := 1746713304167300019855817

theorem tailTrace_3401712 : CollatzResearch.WordTrace tailWord_3401712 prefixEnd_3401712 1746713304167300019855817 := by
  unfold tailWord_3401712
  simp only [CollatzResearch.WordTrace]
  refine ⟨62035314726092932500815695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82713752968123910001087593 62035314726092932500815695)
  ·
    refine ⟨93052972089139398751223543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62035314726092932500815695 93052972089139398751223543)
    ·
      refine ⟨139579458133709098126835315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93052972089139398751223543 139579458133709098126835315)
      ·
        refine ⟨209369187200563647190252973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139579458133709098126835315 209369187200563647190252973)
        ·
          refine ⟨78513445200211367696344865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 209369187200563647190252973 78513445200211367696344865)
          ·
            refine ⟨58885083900158525772258649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78513445200211367696344865 58885083900158525772258649)
            ·
              refine ⟨44163812925118894329193987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58885083900158525772258649 44163812925118894329193987)
              ·
                refine ⟨66245719387678341493790981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44163812925118894329193987 66245719387678341493790981)
                ·
                  refine ⟨12421072385189689030085809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66245719387678341493790981 12421072385189689030085809)
                  ·
                    refine ⟨9315804288892266772564357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12421072385189689030085809 9315804288892266772564357)
                    ·
                      refine ⟨1746713304167300019855817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9315804288892266772564357 1746713304167300019855817)
                      ·
                        rfl

theorem cell23_3401712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 4].length) (baseStart_3401712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3401712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3401712 prefixEnd_3401712 := by exact prefixLift 3401712
  have htrace : WordTrace (prefixWord ++ tailWord_3401712) baseStart_3401712 baseEnd_3401712 := by
    simpa [prefixWord, tailWord_3401712, baseEnd_3401712] using wordTrace_append hprefix tailTrace_3401712
  have hstable : (prefixWord ++ tailWord_3401712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401712).length < 2 ^ (prefixWord ++ tailWord_3401712).sum := by decide
  have hdescent : baseEnd_3401712 < baseStart_3401712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401733 : List Nat := [1, 3, 1, 1, 2, 5, 1, 3, 2, 2, 2]
def baseStart_3401733 : Nat := 118140960795 + 3401733 * 2 ^ 59
def prefixEnd_3401733 : Nat := 4983230072969 + 3 ^ 40 * 3401733 * 2
def baseEnd_3401733 : Nat := 1746724087261044437693221

theorem tailTrace_3401733 : CollatzResearch.WordTrace tailWord_3401733 prefixEnd_3401733 1746724087261044437693221 := by
  unfold tailWord_3401733
  simp only [CollatzResearch.WordTrace]
  refine ⟨124071395385109785588145853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82714263590073190392097235 124071395385109785588145853)
  ·
    refine ⟨46526773269416169595554695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124071395385109785588145853 46526773269416169595554695)
    ·
      refine ⟨69790159904124254393332043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46526773269416169595554695 69790159904124254393332043)
      ·
        refine ⟨104685239856186381589998065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69790159904124254393332043 104685239856186381589998065)
        ·
          refine ⟨78513929892139786192498549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104685239856186381589998065 78513929892139786192498549)
          ·
            refine ⟨7360680927388104955546739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 78513929892139786192498549 7360680927388104955546739)
            ·
              refine ⟨11041021391082157433320109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7360680927388104955546739 11041021391082157433320109)
              ·
                refine ⟨4140383021655809037495041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11041021391082157433320109 4140383021655809037495041)
                ·
                  refine ⟨3105287266241856778121281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4140383021655809037495041 3105287266241856778121281)
                  ·
                    refine ⟨2328965449681392583590961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3105287266241856778121281 2328965449681392583590961)
                    ·
                      refine ⟨1746724087261044437693221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2328965449681392583590961 1746724087261044437693221)
                      ·
                        rfl

theorem cell23_3401733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 3, 2, 2, 2].length) (baseStart_3401733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3401733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3401733 prefixEnd_3401733 := by exact prefixLift 3401733
  have htrace : WordTrace (prefixWord ++ tailWord_3401733) baseStart_3401733 baseEnd_3401733 := by
    simpa [prefixWord, tailWord_3401733, baseEnd_3401733] using wordTrace_append hprefix tailTrace_3401733
  have hstable : (prefixWord ++ tailWord_3401733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401733).length < 2 ^ (prefixWord ++ tailWord_3401733).sum := by decide
  have hdescent : baseEnd_3401733 < baseStart_3401733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401767 : List Nat := [1, 1, 7, 1, 2, 1, 2, 2, 2, 2, 2]
def baseStart_3401767 : Nat := 118140960795 + 3401767 * 2 ^ 59
def prefixEnd_3401767 : Nat := 4983230072969 + 3 ^ 40 * 3401767 * 2
def baseEnd_3401767 : Nat := 1746741545603297304668065

theorem tailTrace_3401767 : CollatzResearch.WordTrace tailWord_3401767 prefixEnd_3401767 1746741545603297304668065 := by
  unfold tailWord_3401767
  simp only [CollatzResearch.WordTrace]
  refine ⟨124072635466986609394883555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82715090311324406263255703 124072635466986609394883555)
  ·
    refine ⟨186108953200479914092325333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124072635466986609394883555 186108953200479914092325333)
    ·
      refine ⟨4361928590636247986538875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 186108953200479914092325333 4361928590636247986538875)
      ·
        refine ⟨6542892885954371979808313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4361928590636247986538875 6542892885954371979808313)
        ·
          refine ⟨4907169664465778984856235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6542892885954371979808313 4907169664465778984856235)
          ·
            refine ⟨7360754496698668477284353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4907169664465778984856235 7360754496698668477284353)
            ·
              refine ⟨5520565872524001357963265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7360754496698668477284353 5520565872524001357963265)
              ·
                refine ⟨4140424404393001018472449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5520565872524001357963265 4140424404393001018472449)
                ·
                  refine ⟨3105318303294750763854337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4140424404393001018472449 3105318303294750763854337)
                  ·
                    refine ⟨2328988727471063072890753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3105318303294750763854337 2328988727471063072890753)
                    ·
                      refine ⟨1746741545603297304668065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2328988727471063072890753 1746741545603297304668065)
                      ·
                        rfl

theorem cell23_3401767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_3401767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3401767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3401767 prefixEnd_3401767 := by exact prefixLift 3401767
  have htrace : WordTrace (prefixWord ++ tailWord_3401767) baseStart_3401767 baseEnd_3401767 := by
    simpa [prefixWord, tailWord_3401767, baseEnd_3401767] using wordTrace_append hprefix tailTrace_3401767
  have hstable : (prefixWord ++ tailWord_3401767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401767).length < 2 ^ (prefixWord ++ tailWord_3401767).sum := by decide
  have hdescent : baseEnd_3401767 < baseStart_3401767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401789 : List Nat := [1, 4, 1, 3, 1, 1, 2, 2, 1, 3, 4]
def baseStart_3401789 : Nat := 118140960795 + 3401789 * 2 ^ 59
def prefixEnd_3401789 : Nat := 4983230072969 + 3 ^ 40 * 3401789 * 2
def baseEnd_3401789 : Nat := 1746752842177696218592963

theorem tailTrace_3401789 : CollatzResearch.WordTrace tailWord_3401789 prefixEnd_3401789 1746752842177696218592963 := by
  unfold tailWord_3401789
  simp only [CollatzResearch.WordTrace]
  refine ⟨124073437872906907152184421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82715625248604604768122947 124073437872906907152184421)
  ·
    refine ⟨23263769601170045091034579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124073437872906907152184421 23263769601170045091034579)
    ·
      refine ⟨34895654401755067636551869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23263769601170045091034579 34895654401755067636551869)
      ·
        refine ⟨13085870400658150363706951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34895654401755067636551869 13085870400658150363706951)
        ·
          refine ⟨19628805600987225545560427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13085870400658150363706951 19628805600987225545560427)
          ·
            refine ⟨29443208401480838318340641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19628805600987225545560427 29443208401480838318340641)
            ·
              refine ⟨22082406301110628738755481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29443208401480838318340641 22082406301110628738755481)
              ·
                refine ⟨16561804725832971554066611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22082406301110628738755481 16561804725832971554066611)
                ·
                  refine ⟨24842707088749457331099917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16561804725832971554066611 24842707088749457331099917)
                  ·
                    refine ⟨9316015158281046499162469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24842707088749457331099917 9316015158281046499162469)
                    ·
                      refine ⟨1746752842177696218592963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9316015158281046499162469 1746752842177696218592963)
                      ·
                        rfl

theorem cell23_3401789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_3401789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3401789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3401789 prefixEnd_3401789 := by exact prefixLift 3401789
  have htrace : WordTrace (prefixWord ++ tailWord_3401789) baseStart_3401789 baseEnd_3401789 := by
    simpa [prefixWord, tailWord_3401789, baseEnd_3401789] using wordTrace_append hprefix tailTrace_3401789
  have hstable : (prefixWord ++ tailWord_3401789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401789).length < 2 ^ (prefixWord ++ tailWord_3401789).sum := by decide
  have hdescent : baseEnd_3401789 < baseStart_3401789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401806 : List Nat := [4, 1, 1, 1, 1, 4, 3, 1, 2, 1, 4]
def baseStart_3401806 : Nat := 118140960795 + 3401806 * 2 ^ 59
def prefixEnd_3401806 : Nat := 4983230072969 + 3 ^ 40 * 3401806 * 2
def baseEnd_3401806 : Nat := 1746761571348822652080385

theorem tailTrace_3401806 : CollatzResearch.WordTrace tailWord_3401806 prefixEnd_3401806 1746761571348822652080385 := by
  unfold tailWord_3401806
  simp only [CollatzResearch.WordTrace]
  refine ⟨15509257239230664881944159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82716038609230212703702181 15509257239230664881944159)
  ·
    refine ⟨23263885858845997322916239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15509257239230664881944159 23263885858845997322916239)
    ·
      refine ⟨34895828788268995984374359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23263885858845997322916239 34895828788268995984374359)
      ·
        refine ⟨52343743182403493976561539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34895828788268995984374359 52343743182403493976561539)
        ·
          refine ⟨78515614773605240964842309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52343743182403493976561539 78515614773605240964842309)
          ·
            refine ⟨14721677770050982680907933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78515614773605240964842309 14721677770050982680907933)
            ·
              refine ⟨5520629163769118505340475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14721677770050982680907933 5520629163769118505340475)
              ·
                refine ⟨8280943745653677758010713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5520629163769118505340475 8280943745653677758010713)
                ·
                  refine ⟨6210707809240258318508035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8280943745653677758010713 6210707809240258318508035)
                  ·
                    refine ⟨9316061713860387477762053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6210707809240258318508035 9316061713860387477762053)
                    ·
                      refine ⟨1746761571348822652080385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9316061713860387477762053 1746761571348822652080385)
                      ·
                        rfl

theorem cell23_3401806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 1, 2, 1, 4].length) (baseStart_3401806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3401806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3401806 prefixEnd_3401806 := by exact prefixLift 3401806
  have htrace : WordTrace (prefixWord ++ tailWord_3401806) baseStart_3401806 baseEnd_3401806 := by
    simpa [prefixWord, tailWord_3401806, baseEnd_3401806] using wordTrace_append hprefix tailTrace_3401806
  have hstable : (prefixWord ++ tailWord_3401806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401806).length < 2 ^ (prefixWord ++ tailWord_3401806).sum := by decide
  have hdescent : baseEnd_3401806 < baseStart_3401806 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401829 : List Nat := [1, 3, 1, 3, 2, 3, 1, 1, 8]
def baseStart_3401829 : Nat := 118140960795 + 3401829 * 2 ^ 59
def prefixEnd_3401829 : Nat := 4983230072969 + 3 ^ 40 * 3401829 * 2
def baseEnd_3401829 : Nat := 194085931267097340232531

theorem tailTrace_3401829 : CollatzResearch.WordTrace tailWord_3401829 prefixEnd_3401829 194085931267097340232531 := by
  unfold tailWord_3401829
  simp only [CollatzResearch.WordTrace]
  refine ⟨124074896792761993983640541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82716597861841329322427027 124074896792761993983640541)
  ·
    refine ⟨46528086297285747743865203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124074896792761993983640541 46528086297285747743865203)
    ·
      refine ⟨69792129445928621615797805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46528086297285747743865203 69792129445928621615797805)
      ·
        refine ⟨26172048542223233105924177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69792129445928621615797805 26172048542223233105924177)
        ·
          refine ⟨19629036406667424829443133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26172048542223233105924177 19629036406667424829443133)
          ·
            refine ⟨7360888652500284311041175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19629036406667424829443133 7360888652500284311041175)
            ·
              refine ⟨11041332978750426466561763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7360888652500284311041175 11041332978750426466561763)
              ·
                refine ⟨16561999468125639699842645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11041332978750426466561763 16561999468125639699842645)
                ·
                  refine ⟨194085931267097340232531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16561999468125639699842645 194085931267097340232531)
                  ·
                    rfl

theorem cell23_3401829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 8].length) (baseStart_3401829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3401829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3401829 prefixEnd_3401829 := by exact prefixLift 3401829
  have htrace : WordTrace (prefixWord ++ tailWord_3401829) baseStart_3401829 baseEnd_3401829 := by
    simpa [prefixWord, tailWord_3401829, baseEnd_3401829] using wordTrace_append hprefix tailTrace_3401829
  have hstable : (prefixWord ++ tailWord_3401829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401829).length < 2 ^ (prefixWord ++ tailWord_3401829).sum := by decide
  have hdescent : baseEnd_3401829 < baseStart_3401829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401890 : List Nat := [3, 3, 1, 3, 1, 1, 3, 1, 3, 1, 3]
def baseStart_3401890 : Nat := 118140960795 + 3401890 * 2 ^ 59
def prefixEnd_3401890 : Nat := 4983230072969 + 3 ^ 40 * 3401890 * 2
def baseEnd_3401890 : Nat := 1746804703723800323429999

theorem tailTrace_3401890 : CollatzResearch.WordTrace tailWord_3401890 prefixEnd_3401890 1746804703723800323429999 := by
  unfold tailWord_3401890
  simp only [CollatzResearch.WordTrace]
  refine ⟨31019280411385250350402781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82718081097027334267740749 31019280411385250350402781)
  ·
    refine ⟨11632230154269468881401043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31019280411385250350402781 11632230154269468881401043)
    ·
      refine ⟨17448345231404203322101565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11632230154269468881401043 17448345231404203322101565)
      ·
        refine ⟨6543129461776576245788087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17448345231404203322101565 6543129461776576245788087)
        ·
          refine ⟨9814694192664864368682131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6543129461776576245788087 9814694192664864368682131)
          ·
            refine ⟨14722041288997296553023197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9814694192664864368682131 14722041288997296553023197)
            ·
              refine ⟨5520765483373986207383699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14722041288997296553023197 5520765483373986207383699)
              ·
                refine ⟨8281148225060979311075549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5520765483373986207383699 8281148225060979311075549)
                ·
                  refine ⟨3105430584397867241653331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8281148225060979311075549 3105430584397867241653331)
                  ·
                    refine ⟨4658145876596800862479997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3105430584397867241653331 4658145876596800862479997)
                    ·
                      refine ⟨1746804703723800323429999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4658145876596800862479997 1746804703723800323429999)
                      ·
                        rfl

theorem cell23_3401890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_3401890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3401890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3401890 prefixEnd_3401890 := by exact prefixLift 3401890
  have htrace : WordTrace (prefixWord ++ tailWord_3401890) baseStart_3401890 baseEnd_3401890 := by
    simpa [prefixWord, tailWord_3401890, baseEnd_3401890] using wordTrace_append hprefix tailTrace_3401890
  have hstable : (prefixWord ++ tailWord_3401890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401890).length < 2 ^ (prefixWord ++ tailWord_3401890).sum := by decide
  have hdescent : baseEnd_3401890 < baseStart_3401890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401913 : List Nat := [1, 2, 1, 4, 1, 2, 2, 1, 5, 2, 2]
def baseStart_3401913 : Nat := 118140960795 + 3401913 * 2 ^ 59
def prefixEnd_3401913 : Nat := 4983230072969 + 3 ^ 40 * 3401913 * 2
def baseEnd_3401913 : Nat := 1746816513778853733442393

theorem tailTrace_3401913 : CollatzResearch.WordTrace tailWord_3401913 prefixEnd_3401913 1746816513778853733442393 := by
  unfold tailWord_3401913
  simp only [CollatzResearch.WordTrace]
  refine ⟨124077960524457676329698393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82718640349638450886465595 124077960524457676329698393)
  ·
    refine ⟨93058470393343257247273795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124077960524457676329698393 93058470393343257247273795)
    ·
      refine ⟨139587705590014885870910693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93058470393343257247273795 139587705590014885870910693)
      ·
        refine ⟨26172694798127791100795755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139587705590014885870910693 26172694798127791100795755)
        ·
          refine ⟨39259042197191686651193633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26172694798127791100795755 39259042197191686651193633)
          ·
            refine ⟨29444281647893764988395225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39259042197191686651193633 29444281647893764988395225)
            ·
              refine ⟨22083211235920323741296419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29444281647893764988395225 22083211235920323741296419)
              ·
                refine ⟨33124816853880485611944629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22083211235920323741296419 33124816853880485611944629)
                ·
                  refine ⟨3105451580051295526119809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33124816853880485611944629 3105451580051295526119809)
                  ·
                    refine ⟨2329088685038471644589857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3105451580051295526119809 2329088685038471644589857)
                    ·
                      refine ⟨1746816513778853733442393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2329088685038471644589857 1746816513778853733442393)
                      ·
                        rfl

theorem cell23_3401913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 5, 2, 2].length) (baseStart_3401913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3401913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3401913 prefixEnd_3401913 := by exact prefixLift 3401913
  have htrace : WordTrace (prefixWord ++ tailWord_3401913) baseStart_3401913 baseEnd_3401913 := by
    simpa [prefixWord, tailWord_3401913, baseEnd_3401913] using wordTrace_append hprefix tailTrace_3401913
  have hstable : (prefixWord ++ tailWord_3401913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401913).length < 2 ^ (prefixWord ++ tailWord_3401913).sum := by decide
  have hdescent : baseEnd_3401913 < baseStart_3401913 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401941 : List Nat := [1, 3, 2, 4, 3, 1, 2, 2, 1, 1, 3]
def baseStart_3401941 : Nat := 118140960795 + 3401941 * 2 ^ 59
def prefixEnd_3401941 : Nat := 4983230072969 + 3 ^ 40 * 3401941 * 2
def baseEnd_3401941 : Nat := 1746830891237179623892265

theorem tailTrace_3401941 : CollatzResearch.WordTrace tailWord_3401941 prefixEnd_3401941 1746830891237179623892265 := by
  unfold tailWord_3401941
  simp only [CollatzResearch.WordTrace]
  refine ⟨124078981768356237111717677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82719321178904158074478451 124078981768356237111717677)
  ·
    refine ⟨46529618163133588916894129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124078981768356237111717677 46529618163133588916894129)
    ·
      refine ⟨34897213622350191687670597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46529618163133588916894129 34897213622350191687670597)
      ·
        refine ⟨6543227554190660941438237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34897213622350191687670597 6543227554190660941438237)
        ·
          refine ⟨2453710332821497853039339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6543227554190660941438237 2453710332821497853039339)
          ·
            refine ⟨3680565499232246779559009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2453710332821497853039339 3680565499232246779559009)
            ·
              refine ⟨2760424124424185084669257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3680565499232246779559009 2760424124424185084669257)
              ·
                refine ⟨2070318093318138813501943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2760424124424185084669257 2070318093318138813501943)
                ·
                  refine ⟨3105477139977208220252915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2070318093318138813501943 3105477139977208220252915)
                  ·
                    refine ⟨4658215709965812330379373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3105477139977208220252915 4658215709965812330379373)
                    ·
                      refine ⟨1746830891237179623892265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4658215709965812330379373 1746830891237179623892265)
                      ·
                        rfl

theorem cell23_3401941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_3401941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3401941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3401941 prefixEnd_3401941 := by exact prefixLift 3401941
  have htrace : WordTrace (prefixWord ++ tailWord_3401941) baseStart_3401941 baseEnd_3401941 := by
    simpa [prefixWord, tailWord_3401941, baseEnd_3401941] using wordTrace_append hprefix tailTrace_3401941
  have hstable : (prefixWord ++ tailWord_3401941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401941).length < 2 ^ (prefixWord ++ tailWord_3401941).sum := by decide
  have hdescent : baseEnd_3401941 < baseStart_3401941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3401963 : List Nat := [1, 1, 1, 1, 2, 5, 1, 5, 2, 1, 3]
def baseStart_3401963 : Nat := 118140960795 + 3401963 * 2 ^ 59
def prefixEnd_3401963 : Nat := 4983230072969 + 3 ^ 40 * 3401963 * 2
def baseEnd_3401963 : Nat := 1746842187811578537817163

theorem tailTrace_3401963 : CollatzResearch.WordTrace tailWord_3401963 prefixEnd_3401963 1746842187811578537817163 := by
  unfold tailWord_3401963
  simp only [CollatzResearch.WordTrace]
  refine ⟨124079784174276534869018543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82719856116184356579345695 124079784174276534869018543)
  ·
    refine ⟨186119676261414802303527815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124079784174276534869018543 186119676261414802303527815)
    ·
      refine ⟨279179514392122203455291723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186119676261414802303527815 279179514392122203455291723)
      ·
        refine ⟨418769271588183305182937585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279179514392122203455291723 418769271588183305182937585)
        ·
          refine ⟨314076953691137478887203189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 418769271588183305182937585 314076953691137478887203189)
          ·
            refine ⟨29444714408544138645675299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 314076953691137478887203189 29444714408544138645675299)
            ·
              refine ⟨44167071612816207968512949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29444714408544138645675299 44167071612816207968512949)
              ·
                refine ⟨4140662963701519497048089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44167071612816207968512949 4140662963701519497048089)
                ·
                  refine ⟨3105497222776139622786067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4140662963701519497048089 3105497222776139622786067)
                  ·
                    refine ⟨4658245834164209434179101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3105497222776139622786067 4658245834164209434179101)
                    ·
                      refine ⟨1746842187811578537817163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4658245834164209434179101 1746842187811578537817163)
                      ·
                        rfl

theorem cell23_3401963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 5, 2, 1, 3].length) (baseStart_3401963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3401963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3401963 prefixEnd_3401963 := by exact prefixLift 3401963
  have htrace : WordTrace (prefixWord ++ tailWord_3401963) baseStart_3401963 baseEnd_3401963 := by
    simpa [prefixWord, tailWord_3401963, baseEnd_3401963] using wordTrace_append hprefix tailTrace_3401963
  have hstable : (prefixWord ++ tailWord_3401963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3401963).length < 2 ^ (prefixWord ++ tailWord_3401963).sum := by decide
  have hdescent : baseEnd_3401963 < baseStart_3401963 := by decide
  rcases family_descends (prefixWord ++ tailWord_3401963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3402020 : List Nat := [2, 3, 1, 3, 1, 2, 3, 1, 1, 4, 2]
def baseStart_3402020 : Nat := 118140960795 + 3402020 * 2 ^ 59
def prefixEnd_3402020 : Nat := 4983230072969 + 3 ^ 40 * 3402020 * 2
def baseEnd_3402020 : Nat := 1746871456208884814804401

theorem tailTrace_3402020 : CollatzResearch.WordTrace tailWord_3402020 prefixEnd_3402020 1746871456208884814804401 := by
  unfold tailWord_3402020
  simp only [CollatzResearch.WordTrace]
  refine ⟨62040931567535016801921757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82721242090046689069229009 62040931567535016801921757)
  ·
    refine ⟨23265349337825631300720659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62040931567535016801921757 23265349337825631300720659)
    ·
      refine ⟨34898024006738446951080989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23265349337825631300720659 34898024006738446951080989)
      ·
        refine ⟨13086759002526917606655371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34898024006738446951080989 13086759002526917606655371)
        ·
          refine ⟨19630138503790376409983057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13086759002526917606655371 19630138503790376409983057)
          ·
            refine ⟨14722603877842782307487293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19630138503790376409983057 14722603877842782307487293)
            ·
              refine ⟨5520976454191043365307735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14722603877842782307487293 5520976454191043365307735)
              ·
                refine ⟨8281464681286565047961603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5520976454191043365307735 8281464681286565047961603)
                ·
                  refine ⟨12422197021929847571942405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8281464681286565047961603 12422197021929847571942405)
                  ·
                    refine ⟨2329161941611846419739201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12422197021929847571942405 2329161941611846419739201)
                    ·
                      refine ⟨1746871456208884814804401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2329161941611846419739201 1746871456208884814804401)
                      ·
                        rfl

theorem cell23_3402020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 1, 1, 4, 2].length) (baseStart_3402020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3402020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3402020 prefixEnd_3402020 := by exact prefixLift 3402020
  have htrace : WordTrace (prefixWord ++ tailWord_3402020) baseStart_3402020 baseEnd_3402020 := by
    simpa [prefixWord, tailWord_3402020, baseEnd_3402020] using wordTrace_append hprefix tailTrace_3402020
  have hstable : (prefixWord ++ tailWord_3402020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3402020).length < 2 ^ (prefixWord ++ tailWord_3402020).sum := by decide
  have hdescent : baseEnd_3402020 < baseStart_3402020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3402020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3402056 : List Nat := [2, 1, 3, 1, 1, 2, 3, 1, 4, 5]
def baseStart_3402056 : Nat := 118140960795 + 3402056 * 2 ^ 59
def prefixEnd_3402056 : Nat := 4983230072969 + 3 ^ 40 * 3402056 * 2
def baseEnd_3402056 : Nat := 582296647170815557984745

theorem tailTrace_3402056 : CollatzResearch.WordTrace tailWord_3402056 prefixEnd_3402056 582296647170815557984745 := by
  unfold tailWord_3402056
  simp only [CollatzResearch.WordTrace]
  refine ⟨62041588081469805876077011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82722117441959741168102681 62041588081469805876077011)
  ·
    refine ⟨93062382122204708814115517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62041588081469805876077011 93062382122204708814115517)
    ·
      refine ⟨34898393295826765805293319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93062382122204708814115517 34898393295826765805293319)
      ·
        refine ⟨52347589943740148707939979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34898393295826765805293319 52347589943740148707939979)
        ·
          refine ⟨78521384915610223061909969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52347589943740148707939979 78521384915610223061909969)
          ·
            refine ⟨58891038686707667296432477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78521384915610223061909969 58891038686707667296432477)
            ·
              refine ⟨22084139507515375236162179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58891038686707667296432477 22084139507515375236162179)
              ·
                refine ⟨33126209261273062854243269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22084139507515375236162179 33126209261273062854243269)
                ·
                  refine ⟨6211164236488699285170613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33126209261273062854243269 6211164236488699285170613)
                  ·
                    refine ⟨582296647170815557984745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6211164236488699285170613 582296647170815557984745)
                    ·
                      rfl

theorem cell23_3402056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 4, 5].length) (baseStart_3402056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3402056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3402056 prefixEnd_3402056 := by exact prefixLift 3402056
  have htrace : WordTrace (prefixWord ++ tailWord_3402056) baseStart_3402056 baseEnd_3402056 := by
    simpa [prefixWord, tailWord_3402056, baseEnd_3402056] using wordTrace_append hprefix tailTrace_3402056
  have hstable : (prefixWord ++ tailWord_3402056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3402056).length < 2 ^ (prefixWord ++ tailWord_3402056).sum := by decide
  have hdescent : baseEnd_3402056 < baseStart_3402056 := by decide
  rcases family_descends (prefixWord ++ tailWord_3402056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3402060 : List Nat := [2, 2, 1, 3, 2, 1, 5, 2, 5]
def baseStart_3402060 : Nat := 118140960795 + 3402060 * 2 ^ 59
def prefixEnd_3402060 : Nat := 4983230072969 + 3 ^ 40 * 3402060 * 2
def baseEnd_3402060 : Nat := 194099110603896073144913

theorem tailTrace_3402060 : CollatzResearch.WordTrace tailWord_3402060 prefixEnd_3402060 194099110603896073144913 := by
  unfold tailWord_3402060
  simp only [CollatzResearch.WordTrace]
  refine ⟨62041661027462560217649817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82722214703283413623533089 62041661027462560217649817)
  ·
    refine ⟨46531245770596920163237363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62041661027462560217649817 46531245770596920163237363)
    ·
      refine ⟨69796868655895380244856045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46531245770596920163237363 69796868655895380244856045)
      ·
        refine ⟨26173825745960767591821017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69796868655895380244856045 26173825745960767591821017)
        ·
          refine ⟨19630369309470575693865763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26173825745960767591821017 19630369309470575693865763)
          ·
            refine ⟨29445553964205863540798645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19630369309470575693865763 29445553964205863540798645)
            ·
              refine ⟨2760520684144299706949873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29445553964205863540798645 2760520684144299706949873)
              ·
                refine ⟨2070390513108224780212405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2760520684144299706949873 2070390513108224780212405)
                ·
                  refine ⟨194099110603896073144913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2070390513108224780212405 194099110603896073144913)
                  ·
                    rfl

theorem cell23_3402060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 5, 2, 5].length) (baseStart_3402060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3402060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3402060 prefixEnd_3402060 := by exact prefixLift 3402060
  have htrace : WordTrace (prefixWord ++ tailWord_3402060) baseStart_3402060 baseEnd_3402060 := by
    simpa [prefixWord, tailWord_3402060, baseEnd_3402060] using wordTrace_append hprefix tailTrace_3402060
  have hstable : (prefixWord ++ tailWord_3402060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3402060).length < 2 ^ (prefixWord ++ tailWord_3402060).sum := by decide
  have hdescent : baseEnd_3402060 < baseStart_3402060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3402060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3402066 : List Nat := [3, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7]
def baseStart_3402066 : Nat := 118140960795 + 3402066 * 2 ^ 59
def prefixEnd_3402066 : Nat := 4983230072969 + 3 ^ 40 * 3402066 * 2
def baseEnd_3402066 : Nat := 1746895076318991634829189

theorem tailTrace_3402066 : CollatzResearch.WordTrace tailWord_3402066 prefixEnd_3402066 1746895076318991634829189 := by
  unfold tailWord_3402066
  simp only [CollatzResearch.WordTrace]
  refine ⟨31020885223225845865004513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82722360595268922306678701 31020885223225845865004513)
  ·
    refine ⟨23265663917419384398753385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31020885223225845865004513 23265663917419384398753385)
    ·
      refine ⟨17449247938064538299065039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23265663917419384398753385 17449247938064538299065039)
      ·
        refine ⟨26173871907096807448597559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17449247938064538299065039 26173871907096807448597559)
        ·
          refine ⟨39260807860645211172896339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26173871907096807448597559 39260807860645211172896339)
          ·
            refine ⟨58891211790967816759344509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39260807860645211172896339 58891211790967816759344509)
            ·
              refine ⟨22084204421612931284754191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58891211790967816759344509 22084204421612931284754191)
              ·
                refine ⟨33126306632419396927131287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22084204421612931284754191 33126306632419396927131287)
                ·
                  refine ⟨49689459948629095390696931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33126306632419396927131287 49689459948629095390696931)
                  ·
                    refine ⟨74534189922943643086045397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49689459948629095390696931 74534189922943643086045397)
                    ·
                      refine ⟨1746895076318991634829189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 74534189922943643086045397 1746895076318991634829189)
                      ·
                        rfl

theorem cell23_3402066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_3402066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3402066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3402066 prefixEnd_3402066 := by exact prefixLift 3402066
  have htrace : WordTrace (prefixWord ++ tailWord_3402066) baseStart_3402066 baseEnd_3402066 := by
    simpa [prefixWord, tailWord_3402066, baseEnd_3402066] using wordTrace_append hprefix tailTrace_3402066
  have hstable : (prefixWord ++ tailWord_3402066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3402066).length < 2 ^ (prefixWord ++ tailWord_3402066).sum := by decide
  have hdescent : baseEnd_3402066 < baseStart_3402066 := by decide
  rcases family_descends (prefixWord ++ tailWord_3402066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3402090 : List Nat := [3, 1, 3, 3, 1, 2, 2, 1, 2, 5]
def baseStart_3402090 : Nat := 118140960795 + 3402090 * 2 ^ 59
def prefixEnd_3402090 : Nat := 4983230072969 + 3 ^ 40 * 3402090 * 2
def baseEnd_3402090 : Nat := 582302466618233180309693

theorem tailTrace_3402090 : CollatzResearch.WordTrace tailWord_3402090 prefixEnd_3402090 582302466618233180309693 := by
  unfold tailWord_3402090
  simp only [CollatzResearch.WordTrace]
  refine ⟨31021104061204108889722931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82722944163210957039261149 31021104061204108889722931)
  ·
    refine ⟨46531656091806163334584397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31021104061204108889722931 46531656091806163334584397)
    ·
      refine ⟨17449371034427311250469149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46531656091806163334584397 17449371034427311250469149)
      ·
        refine ⟨6543514137910241718925931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17449371034427311250469149 6543514137910241718925931)
        ·
          refine ⟨9815271206865362578388897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6543514137910241718925931 9815271206865362578388897)
          ·
            refine ⟨7361453405149021933791673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9815271206865362578388897 7361453405149021933791673)
            ·
              refine ⟨5521090053861766450343755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7361453405149021933791673 5521090053861766450343755)
              ·
                refine ⟨8281635080792649675515633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5521090053861766450343755 8281635080792649675515633)
                ·
                  refine ⟨6211226310594487256636725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8281635080792649675515633 6211226310594487256636725)
                  ·
                    refine ⟨582302466618233180309693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6211226310594487256636725 582302466618233180309693)
                    ·
                      rfl

theorem cell23_3402090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 1, 2, 5].length) (baseStart_3402090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3402090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3402090 prefixEnd_3402090 := by exact prefixLift 3402090
  have htrace : WordTrace (prefixWord ++ tailWord_3402090) baseStart_3402090 baseEnd_3402090 := by
    simpa [prefixWord, tailWord_3402090, baseEnd_3402090] using wordTrace_append hprefix tailTrace_3402090
  have hstable : (prefixWord ++ tailWord_3402090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3402090).length < 2 ^ (prefixWord ++ tailWord_3402090).sum := by decide
  have hdescent : baseEnd_3402090 < baseStart_3402090 := by decide
  rcases family_descends (prefixWord ++ tailWord_3402090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3402156 : List Nat := [2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 5]
def baseStart_3402156 : Nat := 118140960795 + 3402156 * 2 ^ 59
def prefixEnd_3402156 : Nat := 4983230072969 + 3 ^ 40 * 3402156 * 2
def baseEnd_3402156 : Nat := 1746941289577896282703775

theorem tailTrace_3402156 : CollatzResearch.WordTrace tailWord_3402156 prefixEnd_3402156 1746941289577896282703775 := by
  unfold tailWord_3402156
  simp only [CollatzResearch.WordTrace]
  refine ⟨62043411731288664415397161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82724548975051552553862881 62043411731288664415397161)
  ·
    refine ⟨46532558798466498311547871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62043411731288664415397161 46532558798466498311547871)
    ·
      refine ⟨69798838197699747467321807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46532558798466498311547871 69798838197699747467321807)
      ·
        refine ⟨104698257296549621200982711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69798838197699747467321807 104698257296549621200982711)
        ·
          refine ⟨157047385944824431801474067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104698257296549621200982711 157047385944824431801474067)
          ·
            refine ⟨235571078917236647702211101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157047385944824431801474067 235571078917236647702211101)
            ·
              refine ⟨88339154593963742888329163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 235571078917236647702211101 88339154593963742888329163)
              ·
                refine ⟨132508731890945614332493745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88339154593963742888329163 132508731890945614332493745)
                ·
                  refine ⟨99381548918209210749370309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 132508731890945614332493745 99381548918209210749370309)
                  ·
                    refine ⟨18634040422164227015506933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 99381548918209210749370309 18634040422164227015506933)
                    ·
                      refine ⟨1746941289577896282703775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18634040422164227015506933 1746941289577896282703775)
                      ·
                        rfl

theorem cell23_3402156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 5].length) (baseStart_3402156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3402156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3402156 prefixEnd_3402156 := by exact prefixLift 3402156
  have htrace : WordTrace (prefixWord ++ tailWord_3402156) baseStart_3402156 baseEnd_3402156 := by
    simpa [prefixWord, tailWord_3402156, baseEnd_3402156] using wordTrace_append hprefix tailTrace_3402156
  have hstable : (prefixWord ++ tailWord_3402156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3402156).length < 2 ^ (prefixWord ++ tailWord_3402156).sum := by decide
  have hdescent : baseEnd_3402156 < baseStart_3402156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3402156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3402170 : List Nat := [3, 1, 1, 1, 2, 1, 1, 6, 2, 3, 2]
def baseStart_3402170 : Nat := 118140960795 + 3402170 * 2 ^ 59
def prefixEnd_3402170 : Nat := 4983230072969 + 3 ^ 40 * 3402170 * 2
def baseEnd_3402170 : Nat := 1746948478307059227928711

theorem tailTrace_3402170 : CollatzResearch.WordTrace tailWord_3402170 prefixEnd_3402170 1746948478307059227928711 := by
  unfold tailWord_3402170
  simp only [CollatzResearch.WordTrace]
  refine ⟨31021833521131652305450991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82724889389684406147869309 31021833521131652305450991)
  ·
    refine ⟨46532750281697478458176487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31021833521131652305450991 46532750281697478458176487)
    ·
      refine ⟨69799125422546217687264731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46532750281697478458176487 69799125422546217687264731)
      ·
        refine ⟨104698688133819326530897097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69799125422546217687264731 104698688133819326530897097)
        ·
          refine ⟨78524016100364494898172823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104698688133819326530897097 78524016100364494898172823)
          ·
            refine ⟨117786024150546742347259235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78524016100364494898172823 117786024150546742347259235)
            ·
              refine ⟨176679036225820113520888853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117786024150546742347259235 176679036225820113520888853)
              ·
                refine ⟨8281829823085317821291665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 176679036225820113520888853 8281829823085317821291665)
                ·
                  refine ⟨6211372367313988365968749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8281829823085317821291665 6211372367313988365968749)
                  ·
                    refine ⟨2329264637742745637238281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6211372367313988365968749 2329264637742745637238281)
                    ·
                      refine ⟨1746948478307059227928711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2329264637742745637238281 1746948478307059227928711)
                      ·
                        rfl

theorem cell23_3402170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 6, 2, 3, 2].length) (baseStart_3402170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3402170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3402170 prefixEnd_3402170 := by exact prefixLift 3402170
  have htrace : WordTrace (prefixWord ++ tailWord_3402170) baseStart_3402170 baseEnd_3402170 := by
    simpa [prefixWord, tailWord_3402170, baseEnd_3402170] using wordTrace_append hprefix tailTrace_3402170
  have hstable : (prefixWord ++ tailWord_3402170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3402170).length < 2 ^ (prefixWord ++ tailWord_3402170).sum := by decide
  have hdescent : baseEnd_3402170 < baseStart_3402170 := by decide
  rcases family_descends (prefixWord ++ tailWord_3402170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3402211 : List Nat := [1, 1, 1, 6, 3, 2, 1, 3, 1, 1, 3]
def baseStart_3402211 : Nat := 118140960795 + 3402211 * 2 ^ 59
def prefixEnd_3402211 : Nat := 4983230072969 + 3 ^ 40 * 3402211 * 2
def baseEnd_3402211 : Nat := 1746969531013893567516023

theorem tailTrace_3402211 : CollatzResearch.WordTrace tailWord_3402211 prefixEnd_3402211 1746969531013893567516023 := by
  unfold tailWord_3402211
  simp only [CollatzResearch.WordTrace]
  refine ⟨124088829477378073224046487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82725886318252048816030991 124088829477378073224046487)
  ·
    refine ⟨186133244216067109836069731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124088829477378073224046487 186133244216067109836069731)
    ·
      refine ⟨279199866324100664754104597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186133244216067109836069731 279199866324100664754104597)
      ·
        refine ⟨13087493733942218660348653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 279199866324100664754104597 13087493733942218660348653)
        ·
          refine ⟨4907810150228331997630745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13087493733942218660348653 4907810150228331997630745)
          ·
            refine ⟨3680857612671248998223059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4907810150228331997630745 3680857612671248998223059)
            ·
              refine ⟨5521286419006873497334589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3680857612671248998223059 5521286419006873497334589)
              ·
                refine ⟨2070482407127577561500471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5521286419006873497334589 2070482407127577561500471)
                ·
                  refine ⟨3105723610691366342250707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2070482407127577561500471 3105723610691366342250707)
                  ·
                    refine ⟨4658585416037049513376061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3105723610691366342250707 4658585416037049513376061)
                    ·
                      refine ⟨1746969531013893567516023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4658585416037049513376061 1746969531013893567516023)
                      ·
                        rfl

theorem cell23_3402211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 3, 1, 1, 3].length) (baseStart_3402211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3402211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3402211 prefixEnd_3402211 := by exact prefixLift 3402211
  have htrace : WordTrace (prefixWord ++ tailWord_3402211) baseStart_3402211 baseEnd_3402211 := by
    simpa [prefixWord, tailWord_3402211, baseEnd_3402211] using wordTrace_append hprefix tailTrace_3402211
  have hstable : (prefixWord ++ tailWord_3402211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3402211).length < 2 ^ (prefixWord ++ tailWord_3402211).sum := by decide
  have hdescent : baseEnd_3402211 < baseStart_3402211 := by decide
  rcases family_descends (prefixWord ++ tailWord_3402211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3402220 : List Nat := [2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 3]
def baseStart_3402220 : Nat := 118140960795 + 3402220 * 2 ^ 59
def prefixEnd_3402220 : Nat := 4983230072969 + 3 ^ 40 * 3402220 * 2
def baseEnd_3402220 : Nat := 1746974152339784032303481

theorem tailTrace_3402220 : CollatzResearch.WordTrace tailWord_3402220 prefixEnd_3402220 1746974152339784032303481 := by
  unfold tailWord_3402220
  simp only [CollatzResearch.WordTrace]
  refine ⟨62044578867172733880562057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82726105156230311840749409 62044578867172733880562057)
  ·
    refine ⟨46533434150379550410421543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62044578867172733880562057 46533434150379550410421543)
    ·
      refine ⟨69800151225569325615632315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46533434150379550410421543 69800151225569325615632315)
      ·
        refine ⟨104700226838353988423448473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69800151225569325615632315 104700226838353988423448473)
        ·
          refine ⟨78525170128765491317586355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104700226838353988423448473 78525170128765491317586355)
          ·
            refine ⟨117787755193148236976379533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78525170128765491317586355 117787755193148236976379533)
            ·
              refine ⟨44170408197430588866142325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117787755193148236976379533 44170408197430588866142325)
              ·
                refine ⟨4140975768509117706200843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44170408197430588866142325 4140975768509117706200843)
                ·
                  refine ⟨6211463652763676559301265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4140975768509117706200843 6211463652763676559301265)
                  ·
                    refine ⟨4658597739572757419475949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6211463652763676559301265 4658597739572757419475949)
                    ·
                      refine ⟨1746974152339784032303481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4658597739572757419475949 1746974152339784032303481)
                      ·
                        rfl

theorem cell23_3402220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 3].length) (baseStart_3402220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3402220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3402220 prefixEnd_3402220 := by exact prefixLift 3402220
  have htrace : WordTrace (prefixWord ++ tailWord_3402220) baseStart_3402220 baseEnd_3402220 := by
    simpa [prefixWord, tailWord_3402220, baseEnd_3402220] using wordTrace_append hprefix tailTrace_3402220
  have hstable : (prefixWord ++ tailWord_3402220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3402220).length < 2 ^ (prefixWord ++ tailWord_3402220).sum := by decide
  have hdescent : baseEnd_3402220 < baseStart_3402220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3402220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3402244 : List Nat := [2, 3, 2, 3, 1, 1, 4, 1, 2, 4]
def baseStart_3402244 : Nat := 118140960795 + 3402244 * 2 ^ 59
def prefixEnd_3402244 : Nat := 4983230072969 + 3 ^ 40 * 3402244 * 2
def baseEnd_3402244 : Nat := 582328825291830646134457

theorem tailTrace_3402244 : CollatzResearch.WordTrace tailWord_3402244 prefixEnd_3402244 582328825291830646134457 := by
  unfold tailWord_3402244
  simp only [CollatzResearch.WordTrace]
  refine ⟨62045016543129259929998893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82726688724172346573331857 62045016543129259929998893)
  ·
    refine ⟨23266881203673472473749585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62045016543129259929998893 23266881203673472473749585)
    ·
      refine ⟨17450160902755104355312189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23266881203673472473749585 17450160902755104355312189)
      ·
        refine ⟨6543810338533164133242071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17450160902755104355312189 6543810338533164133242071)
        ·
          refine ⟨9815715507799746199863107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6543810338533164133242071 9815715507799746199863107)
          ·
            refine ⟨14723573261699619299794661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9815715507799746199863107 14723573261699619299794661)
            ·
              refine ⟨2760669986568678618711499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14723573261699619299794661 2760669986568678618711499)
              ·
                refine ⟨4141004979853017928067249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2760669986568678618711499 4141004979853017928067249)
                ·
                  refine ⟨3105753734889763446050437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4141004979853017928067249 3105753734889763446050437)
                  ·
                    refine ⟨582328825291830646134457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3105753734889763446050437 582328825291830646134457)
                    ·
                      rfl

theorem cell23_3402244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 4, 1, 2, 4].length) (baseStart_3402244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3402244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3402244 prefixEnd_3402244 := by exact prefixLift 3402244
  have htrace : WordTrace (prefixWord ++ tailWord_3402244) baseStart_3402244 baseEnd_3402244 := by
    simpa [prefixWord, tailWord_3402244, baseEnd_3402244] using wordTrace_append hprefix tailTrace_3402244
  have hstable : (prefixWord ++ tailWord_3402244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3402244).length < 2 ^ (prefixWord ++ tailWord_3402244).sum := by decide
  have hdescent : baseEnd_3402244 < baseStart_3402244 := by decide
  rcases family_descends (prefixWord ++ tailWord_3402244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3402250 : List Nat := [3, 1, 2, 2, 2, 1, 2, 3, 1, 3, 3]
def baseStart_3402250 : Nat := 118140960795 + 3402250 * 2 ^ 59
def prefixEnd_3402250 : Nat := 4983230072969 + 3 ^ 40 * 3402250 * 2
def baseEnd_3402250 : Nat := 1746989556759418914928343

theorem tailTrace_3402250 : CollatzResearch.WordTrace tailWord_3402250 prefixEnd_3402250 1746989556759418914928343 := by
  unfold tailWord_3402250
  simp only [CollatzResearch.WordTrace]
  refine ⟨31022562981059195721179051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82726834616157855256477469 31022562981059195721179051)
  ·
    refine ⟨46533844471588793581768577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31022562981059195721179051 46533844471588793581768577)
    ·
      refine ⟨34900383353691595186326433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46533844471588793581768577 34900383353691595186326433)
      ·
        refine ⟨26175287515268696389744825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34900383353691595186326433 26175287515268696389744825)
        ·
          refine ⟨19631465636451522292308619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26175287515268696389744825 19631465636451522292308619)
          ·
            refine ⟨29447198454677283438462929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19631465636451522292308619 29447198454677283438462929)
            ·
              refine ⟨22085398841007962578847197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29447198454677283438462929 22085398841007962578847197)
              ·
                refine ⟨8282024565377985967067699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22085398841007962578847197 8282024565377985967067699)
                ·
                  refine ⟨12423036848066978950601549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8282024565377985967067699 12423036848066978950601549)
                  ·
                    refine ⟨4658638818025117106475581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12423036848066978950601549 4658638818025117106475581)
                    ·
                      refine ⟨1746989556759418914928343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4658638818025117106475581 1746989556759418914928343)
                      ·
                        rfl

theorem cell23_3402250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 3, 1, 3, 3].length) (baseStart_3402250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3402250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3402250 prefixEnd_3402250 := by exact prefixLift 3402250
  have htrace : WordTrace (prefixWord ++ tailWord_3402250) baseStart_3402250 baseEnd_3402250 := by
    simpa [prefixWord, tailWord_3402250, baseEnd_3402250] using wordTrace_append hprefix tailTrace_3402250
  have hstable : (prefixWord ++ tailWord_3402250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3402250).length < 2 ^ (prefixWord ++ tailWord_3402250).sum := by decide
  have hdescent : baseEnd_3402250 < baseStart_3402250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3402250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3402254 : List Nat := [4, 1, 1, 2, 3, 3, 1, 2, 1, 2, 3]
def baseStart_3402254 : Nat := 118140960795 + 3402254 * 2 ^ 59
def prefixEnd_3402254 : Nat := 4983230072969 + 3 ^ 40 * 3402254 * 2
def baseEnd_3402254 : Nat := 1746991610682036899278325

theorem tailTrace_3402254 : CollatzResearch.WordTrace tailWord_3402254 prefixEnd_3402254 1746991610682036899278325 := by
  unfold tailWord_3402254
  simp only [CollatzResearch.WordTrace]
  refine ⟨15511299727027786445982727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82726931877481527711907877 15511299727027786445982727)
  ·
    refine ⟨23266949590541679668974091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15511299727027786445982727 23266949590541679668974091)
    ·
      refine ⟨34900424385812519503461137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23266949590541679668974091 34900424385812519503461137)
      ·
        refine ⟨26175318289359389627595853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34900424385812519503461137 26175318289359389627595853)
        ·
          refine ⟨9815744358509771110348445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26175318289359389627595853 9815744358509771110348445)
          ·
            refine ⟨3680904134441164166380667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9815744358509771110348445 3680904134441164166380667)
            ·
              refine ⟨5521356201661746249571001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3680904134441164166380667 5521356201661746249571001)
              ·
                refine ⟨4141017151246309687178251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5521356201661746249571001 4141017151246309687178251)
                ·
                  refine ⟨6211525726869464530767377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4141017151246309687178251 6211525726869464530767377)
                  ·
                    refine ⟨4658644295152098398075533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6211525726869464530767377 4658644295152098398075533)
                    ·
                      refine ⟨1746991610682036899278325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4658644295152098398075533 1746991610682036899278325)
                      ·
                        rfl

theorem cell23_3402254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 2, 1, 2, 3].length) (baseStart_3402254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3402254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3402254 prefixEnd_3402254 := by exact prefixLift 3402254
  have htrace : WordTrace (prefixWord ++ tailWord_3402254) baseStart_3402254 baseEnd_3402254 := by
    simpa [prefixWord, tailWord_3402254, baseEnd_3402254] using wordTrace_append hprefix tailTrace_3402254
  have hstable : (prefixWord ++ tailWord_3402254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3402254).length < 2 ^ (prefixWord ++ tailWord_3402254).sum := by decide
  have hdescent : baseEnd_3402254 < baseStart_3402254 := by decide
  rcases family_descends (prefixWord ++ tailWord_3402254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3402277 : List Nat := [1, 3, 1, 2, 2, 1, 2, 5, 1, 3, 2]
def baseStart_3402277 : Nat := 118140960795 + 3402277 * 2 ^ 59
def prefixEnd_3402277 : Nat := 4983230072969 + 3 ^ 40 * 3402277 * 2
def baseEnd_3402277 : Nat := 1747003420737090309290719

theorem tailTrace_3402277 : CollatzResearch.WordTrace tailWord_3402277 prefixEnd_3402277 1747003420737090309290719 := by
  unfold tailWord_3402277
  simp only [CollatzResearch.WordTrace]
  refine ⟨124091236695138966495949085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82727491130092644330632723 124091236695138966495949085)
  ·
    refine ⟨46534213760677112435980907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124091236695138966495949085 46534213760677112435980907)
    ·
      refine ⟨69801320641015668653971361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46534213760677112435980907 69801320641015668653971361)
      ·
        refine ⟨52350990480761751490478521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69801320641015668653971361 52350990480761751490478521)
        ·
          refine ⟨39263242860571313617858891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52350990480761751490478521 39263242860571313617858891)
          ·
            refine ⟨58894864290856970426788337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39263242860571313617858891 58894864290856970426788337)
            ·
              refine ⟨44171148218142727820091253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58894864290856970426788337 44171148218142727820091253)
              ·
                refine ⟨4141045145450880733133555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44171148218142727820091253 4141045145450880733133555)
                ·
                  refine ⟨6211567718176321099700333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4141045145450880733133555 6211567718176321099700333)
                  ·
                    refine ⟨2329337894316120412387625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6211567718176321099700333 2329337894316120412387625)
                    ·
                      refine ⟨1747003420737090309290719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2329337894316120412387625 1747003420737090309290719)
                      ·
                        rfl

theorem cell23_3402277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 5, 1, 3, 2].length) (baseStart_3402277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3402277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3402277 prefixEnd_3402277 := by exact prefixLift 3402277
  have htrace : WordTrace (prefixWord ++ tailWord_3402277) baseStart_3402277 baseEnd_3402277 := by
    simpa [prefixWord, tailWord_3402277, baseEnd_3402277] using wordTrace_append hprefix tailTrace_3402277
  have hstable : (prefixWord ++ tailWord_3402277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3402277).length < 2 ^ (prefixWord ++ tailWord_3402277).sum := by decide
  have hdescent : baseEnd_3402277 < baseStart_3402277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3402277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3402294 : List Nat := [5, 1, 2, 1, 2, 1, 1, 2, 3, 3, 2]
def baseStart_3402294 : Nat := 118140960795 + 3402294 * 2 ^ 59
def prefixEnd_3402294 : Nat := 4983230072969 + 3 ^ 40 * 3402294 * 2
def baseEnd_3402294 : Nat := 1747012149908216742778141

theorem tailTrace_3402294 : CollatzResearch.WordTrace tailWord_3402294 prefixEnd_3402294 1747012149908216742778141 := by
  unfold tailWord_3402294
  simp only [CollatzResearch.WordTrace]
  refine ⟨7755741046004836149957371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 82727904490718252266211957 7755741046004836149957371)
  ·
    refine ⟨11633611569007254224936057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7755741046004836149957371 11633611569007254224936057)
    ·
      refine ⟨8725208676755440668702043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11633611569007254224936057 8725208676755440668702043)
      ·
        refine ⟨13087813015133161003053065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8725208676755440668702043 13087813015133161003053065)
        ·
          refine ⟨9815859761349870752289799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13087813015133161003053065 9815859761349870752289799)
          ·
            refine ⟨14723789642024806128434699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9815859761349870752289799 14723789642024806128434699)
            ·
              refine ⟨22085684463037209192652049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14723789642024806128434699 22085684463037209192652049)
              ·
                refine ⟨16564263347277906894489037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22085684463037209192652049 16564263347277906894489037)
                ·
                  refine ⟨6211598755229215085433389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16564263347277906894489037 6211598755229215085433389)
                  ·
                    refine ⟨2329349533210955657037521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6211598755229215085433389 2329349533210955657037521)
                    ·
                      refine ⟨1747012149908216742778141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2329349533210955657037521 1747012149908216742778141)
                      ·
                        rfl

theorem cell23_3402294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 2, 3, 3, 2].length) (baseStart_3402294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3402294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3402294 prefixEnd_3402294 := by exact prefixLift 3402294
  have htrace : WordTrace (prefixWord ++ tailWord_3402294) baseStart_3402294 baseEnd_3402294 := by
    simpa [prefixWord, tailWord_3402294, baseEnd_3402294] using wordTrace_append hprefix tailTrace_3402294
  have hstable : (prefixWord ++ tailWord_3402294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3402294).length < 2 ^ (prefixWord ++ tailWord_3402294).sum := by decide
  have hdescent : baseEnd_3402294 < baseStart_3402294 := by decide
  rcases family_descends (prefixWord ++ tailWord_3402294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3402300 : List Nat := [2, 2, 2, 2, 3, 2, 1, 1, 2, 6]
def baseStart_3402300 : Nat := 118140960795 + 3402300 * 2 ^ 59
def prefixEnd_3402300 : Nat := 4983230072969 + 3 ^ 40 * 3402300 * 2
def baseEnd_3402300 : Nat := 582338410264047906434371

theorem tailTrace_3402300 : CollatzResearch.WordTrace tailWord_3402300 prefixEnd_3402300 582338410264047906434371 := by
  unfold tailWord_3402300
  simp only [CollatzResearch.WordTrace]
  refine ⟨62046037787027820712018177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82728050382703760949357569 62046037787027820712018177)
  ·
    refine ⟨46534528340270865534013633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62046037787027820712018177 46534528340270865534013633)
    ·
      refine ⟨34900896255203149150510225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46534528340270865534013633 34900896255203149150510225)
      ·
        refine ⟨26175672191402361862882669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34900896255203149150510225 26175672191402361862882669)
        ·
          refine ⟨9815877071775885698581001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26175672191402361862882669 9815877071775885698581001)
          ·
            refine ⟨7361907803831914273935751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9815877071775885698581001 7361907803831914273935751)
            ·
              refine ⟨11042861705747871410903627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7361907803831914273935751 11042861705747871410903627)
              ·
                refine ⟨16564292558621807116355441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11042861705747871410903627 16564292558621807116355441)
                ·
                  refine ⟨12423219418966355337266581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16564292558621807116355441 12423219418966355337266581)
                  ·
                    refine ⟨582338410264047906434371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12423219418966355337266581 582338410264047906434371)
                    ·
                      rfl

theorem cell23_3402300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 1, 2, 6].length) (baseStart_3402300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3402300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3402300 prefixEnd_3402300 := by exact prefixLift 3402300
  have htrace : WordTrace (prefixWord ++ tailWord_3402300) baseStart_3402300 baseEnd_3402300 := by
    simpa [prefixWord, tailWord_3402300, baseEnd_3402300] using wordTrace_append hprefix tailTrace_3402300
  have hstable : (prefixWord ++ tailWord_3402300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3402300).length < 2 ^ (prefixWord ++ tailWord_3402300).sum := by decide
  have hdescent : baseEnd_3402300 < baseStart_3402300 := by decide
  rcases family_descends (prefixWord ++ tailWord_3402300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3402340 : List Nat := [2, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3]
def baseStart_3402340 : Nat := 118140960795 + 3402340 * 2 ^ 59
def prefixEnd_3402340 : Nat := 4983230072969 + 3 ^ 40 * 3402340 * 2
def baseEnd_3402340 : Nat := 1747035770018323562802929

theorem tailTrace_3402340 : CollatzResearch.WordTrace tailWord_3402340 prefixEnd_3402340 1747035770018323562802929 := by
  unfold tailWord_3402340
  simp only [CollatzResearch.WordTrace]
  refine ⟨62046767246955364127746237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82729022995940485503661649 62046767246955364127746237)
  ·
    refine ⟨23267537717608261547904839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62046767246955364127746237 23267537717608261547904839)
    ·
      refine ⟨34901306576412392321857259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23267537717608261547904839 34901306576412392321857259)
      ·
        refine ⟨52351959864618588482785889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34901306576412392321857259 52351959864618588482785889)
        ·
          refine ⟨39263969898463941362089417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52351959864618588482785889 39263969898463941362089417)
          ·
            refine ⟨29447977423847956021567063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39263969898463941362089417 29447977423847956021567063)
            ·
              refine ⟨44171966135771934032350595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29447977423847956021567063 44171966135771934032350595)
              ·
                refine ⟨66257949203657901048525893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44171966135771934032350595 66257949203657901048525893)
                ·
                  refine ⟨12423365475685856446598605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66257949203657901048525893 12423365475685856446598605)
                  ·
                    refine ⟨4658762053382196167474477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12423365475685856446598605 4658762053382196167474477)
                    ·
                      refine ⟨1747035770018323562802929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4658762053382196167474477 1747035770018323562802929)
                      ·
                        rfl

theorem cell23_3402340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3].length) (baseStart_3402340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3402340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3402340 prefixEnd_3402340 := by exact prefixLift 3402340
  have htrace : WordTrace (prefixWord ++ tailWord_3402340) baseStart_3402340 baseEnd_3402340 := by
    simpa [prefixWord, tailWord_3402340, baseEnd_3402340] using wordTrace_append hprefix tailTrace_3402340
  have hstable : (prefixWord ++ tailWord_3402340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3402340).length < 2 ^ (prefixWord ++ tailWord_3402340).sum := by decide
  have hdescent : baseEnd_3402340 < baseStart_3402340 := by decide
  rcases family_descends (prefixWord ++ tailWord_3402340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3402358 : List Nat := [5, 1, 1, 2, 4, 1, 1, 1, 1, 4, 2]
def baseStart_3402358 : Nat := 118140960795 + 3402358 * 2 ^ 59
def prefixEnd_3402358 : Nat := 4983230072969 + 3 ^ 40 * 3402358 * 2
def baseEnd_3402358 : Nat := 1747045012670104492377847

theorem tailTrace_3402358 : CollatzResearch.WordTrace tailWord_3402358 prefixEnd_3402358 1747045012670104492377847 := by
  unfold tailWord_3402358
  simp only [CollatzResearch.WordTrace]
  refine ⟨7755886937990344833102983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 82729460671897011553098485 7755886937990344833102983)
  ·
    refine ⟨11633830406985517249654475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7755886937990344833102983 11633830406985517249654475)
    ·
      refine ⟨17450745610478275874481713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11633830406985517249654475 17450745610478275874481713)
      ·
        refine ⟨13088059207858706905861285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17450745610478275874481713 13088059207858706905861285)
        ·
          refine ⟨2454011101473507544848991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13088059207858706905861285 2454011101473507544848991)
          ·
            refine ⟨3681016652210261317273487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2454011101473507544848991 3681016652210261317273487)
            ·
              refine ⟨5521524978315391975910231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3681016652210261317273487 5521524978315391975910231)
              ·
                refine ⟨8282287467473087963865347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5521524978315391975910231 8282287467473087963865347)
                ·
                  refine ⟨12423431201209631945798021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8282287467473087963865347 12423431201209631945798021)
                  ·
                    refine ⟨2329393350226805989837129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12423431201209631945798021 2329393350226805989837129)
                    ·
                      refine ⟨1747045012670104492377847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2329393350226805989837129 1747045012670104492377847)
                      ·
                        rfl

theorem cell23_3402358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 1, 1, 4, 2].length) (baseStart_3402358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3402358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3402358 prefixEnd_3402358 := by exact prefixLift 3402358
  have htrace : WordTrace (prefixWord ++ tailWord_3402358) baseStart_3402358 baseEnd_3402358 := by
    simpa [prefixWord, tailWord_3402358, baseEnd_3402358] using wordTrace_append hprefix tailTrace_3402358
  have hstable : (prefixWord ++ tailWord_3402358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3402358).length < 2 ^ (prefixWord ++ tailWord_3402358).sum := by decide
  have hdescent : baseEnd_3402358 < baseStart_3402358 := by decide
  rcases family_descends (prefixWord ++ tailWord_3402358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3402394 : List Nat := [3, 1, 1, 6, 1, 1, 1, 2, 2, 5]
def baseStart_3402394 : Nat := 118140960795 + 3402394 * 2 ^ 59
def prefixEnd_3402394 : Nat := 4983230072969 + 3 ^ 40 * 3402394 * 2
def baseEnd_3402394 : Nat := 582354499324555450509227

theorem tailTrace_3402394 : CollatzResearch.WordTrace tailWord_3402394 prefixEnd_3402394 582354499324555450509227 := by
  unfold tailWord_3402394
  simp only [CollatzResearch.WordTrace]
  refine ⟨31023876008928773869489559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82730336023810063651972157 31023876008928773869489559)
  ·
    refine ⟨46535814013393160804234339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31023876008928773869489559 46535814013393160804234339)
    ·
      refine ⟨69803721020089741206351509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46535814013393160804234339 69803721020089741206351509)
      ·
        refine ⟨3272049422816706619047727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 69803721020089741206351509 3272049422816706619047727)
        ·
          refine ⟨4908074134225059928571591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3272049422816706619047727 4908074134225059928571591)
          ·
            refine ⟨7362111201337589892857387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4908074134225059928571591 7362111201337589892857387)
            ·
              refine ⟨11043166802006384839286081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7362111201337589892857387 11043166802006384839286081)
              ·
                refine ⟨8282375101504788629464561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11043166802006384839286081 8282375101504788629464561)
                ·
                  refine ⟨6211781326128591472098421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8282375101504788629464561 6211781326128591472098421)
                  ·
                    refine ⟨582354499324555450509227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6211781326128591472098421 582354499324555450509227)
                    ·
                      rfl

theorem cell23_3402394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 2, 2, 5].length) (baseStart_3402394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3402394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3402394 prefixEnd_3402394 := by exact prefixLift 3402394
  have htrace : WordTrace (prefixWord ++ tailWord_3402394) baseStart_3402394 baseEnd_3402394 := by
    simpa [prefixWord, tailWord_3402394, baseEnd_3402394] using wordTrace_append hprefix tailTrace_3402394
  have hstable : (prefixWord ++ tailWord_3402394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3402394).length < 2 ^ (prefixWord ++ tailWord_3402394).sum := by decide
  have hdescent : baseEnd_3402394 < baseStart_3402394 := by decide
  rcases family_descends (prefixWord ++ tailWord_3402394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3402397 : List Nat := [1, 4, 2, 1, 1, 1, 2, 1, 4, 4, 2]
def baseStart_3402397 : Nat := 118140960795 + 3402397 * 2 ^ 59
def prefixEnd_3402397 : Nat := 4983230072969 + 3 ^ 40 * 3402397 * 2
def baseEnd_3402397 : Nat := 1747065038415629839790167

theorem tailTrace_3402397 : CollatzResearch.WordTrace tailWord_3402397 prefixEnd_3402397 1747065038415629839790167 := by
  unfold tailWord_3402397
  simp only [CollatzResearch.WordTrace]
  refine ⟨124095613454704226990317445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82730408969802817993544963 124095613454704226990317445)
  ·
    refine ⟨23267927522757042560684521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124095613454704226990317445 23267927522757042560684521)
    ·
      refine ⟨17450945642067781920513391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23267927522757042560684521 17450945642067781920513391)
      ·
        refine ⟨26176418463101672880770087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17450945642067781920513391 26176418463101672880770087)
        ·
          refine ⟨39264627694652509321155131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26176418463101672880770087 39264627694652509321155131)
          ·
            refine ⟨58896941541978763981732697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39264627694652509321155131 58896941541978763981732697)
            ·
              refine ⟨44172706156484072986299523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58896941541978763981732697 44172706156484072986299523)
              ·
                refine ⟨66259059234726109479449285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44172706156484072986299523 66259059234726109479449285)
                ·
                  refine ⟨12423573606511145527396741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66259059234726109479449285 12423573606511145527396741)
                  ·
                    refine ⟨2329420051220839786386889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12423573606511145527396741 2329420051220839786386889)
                    ·
                      refine ⟨1747065038415629839790167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2329420051220839786386889 1747065038415629839790167)
                      ·
                        rfl

theorem cell23_3402397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 4, 4, 2].length) (baseStart_3402397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3402397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3402397 prefixEnd_3402397 := by exact prefixLift 3402397
  have htrace : WordTrace (prefixWord ++ tailWord_3402397) baseStart_3402397 baseEnd_3402397 := by
    simpa [prefixWord, tailWord_3402397, baseEnd_3402397] using wordTrace_append hprefix tailTrace_3402397
  have hstable : (prefixWord ++ tailWord_3402397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3402397).length < 2 ^ (prefixWord ++ tailWord_3402397).sum := by decide
  have hdescent : baseEnd_3402397 < baseStart_3402397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3402397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3402467 : List Nat := [1, 1, 1, 7, 1, 1, 1, 2, 3, 5]
def baseStart_3402467 : Nat := 118140960795 + 3402467 * 2 ^ 59
def prefixEnd_3402467 : Nat := 4983230072969 + 3 ^ 40 * 3402467 * 2
def baseEnd_3402467 : Nat := 582366994020481521971615

theorem tailTrace_3402467 : CollatzResearch.WordTrace tailWord_3402467 prefixEnd_3402467 582366994020481521971615 := by
  unfold tailWord_3402467
  simp only [CollatzResearch.WordTrace]
  refine ⟨124098166564450628945365655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82732111042967085963577103 124098166564450628945365655)
  ·
    refine ⟨186147249846675943418048483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124098166564450628945365655 186147249846675943418048483)
    ·
      refine ⟨279220874770013915127072725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186147249846675943418048483 279220874770013915127072725)
      ·
        refine ⟨6544239252422201135790767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 279220874770013915127072725 6544239252422201135790767)
        ·
          refine ⟨9816358878633301703686151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6544239252422201135790767 9816358878633301703686151)
          ·
            refine ⟨14724538317949952555529227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9816358878633301703686151 14724538317949952555529227)
            ·
              refine ⟨22086807476924928833293841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14724538317949952555529227 22086807476924928833293841)
              ·
                refine ⟨16565105607693696624970381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22086807476924928833293841 16565105607693696624970381)
                ·
                  refine ⟨6211914602885136234363893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16565105607693696624970381 6211914602885136234363893)
                  ·
                    refine ⟨582366994020481521971615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6211914602885136234363893 582366994020481521971615)
                    ·
                      rfl

theorem cell23_3402467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 2, 3, 5].length) (baseStart_3402467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3402467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3402467 prefixEnd_3402467 := by exact prefixLift 3402467
  have htrace : WordTrace (prefixWord ++ tailWord_3402467) baseStart_3402467 baseEnd_3402467 := by
    simpa [prefixWord, tailWord_3402467, baseEnd_3402467] using wordTrace_append hprefix tailTrace_3402467
  have hstable : (prefixWord ++ tailWord_3402467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3402467).length < 2 ^ (prefixWord ++ tailWord_3402467).sum := by decide
  have hdescent : baseEnd_3402467 < baseStart_3402467 := by decide
  rcases family_descends (prefixWord ++ tailWord_3402467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3402485 : List Nat := [1, 3, 6, 1, 1, 2, 1, 1, 2, 2, 3]
def baseStart_3402485 : Nat := 118140960795 + 3402485 * 2 ^ 59
def prefixEnd_3402485 : Nat := 4983230072969 + 3 ^ 40 * 3402485 * 2
def baseEnd_3402485 : Nat := 1747110224713225495489763

theorem tailTrace_3402485 : CollatzResearch.WordTrace tailWord_3402485 prefixEnd_3402485 1747110224713225495489763 := by
  unfold tailWord_3402485
  simp only [CollatzResearch.WordTrace]
  refine ⟨124098823078385418019520909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82732548718923612013013939 124098823078385418019520909)
  ·
    refine ⟨46537058654394531757320341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124098823078385418019520909 46537058654394531757320341)
    ·
      refine ⟨2181424624424743676124391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 46537058654394531757320341 2181424624424743676124391)
      ·
        refine ⟨3272136936637115514186587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2181424624424743676124391 3272136936637115514186587)
        ·
          refine ⟨4908205404955673271279881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3272136936637115514186587 4908205404955673271279881)
          ·
            refine ⟨3681154053716754953459911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4908205404955673271279881 3681154053716754953459911)
            ·
              refine ⟨5521731080575132430189867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3681154053716754953459911 5521731080575132430189867)
              ·
                refine ⟨8282596620862698645284801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5521731080575132430189867 8282596620862698645284801)
                ·
                  refine ⟨6211947465647023983963601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8282596620862698645284801 6211947465647023983963601)
                  ·
                    refine ⟨4658960599235267987972701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6211947465647023983963601 4658960599235267987972701)
                    ·
                      refine ⟨1747110224713225495489763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4658960599235267987972701 1747110224713225495489763)
                      ·
                        rfl

theorem cell23_3402485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_3402485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3402485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3402485 prefixEnd_3402485 := by exact prefixLift 3402485
  have htrace : WordTrace (prefixWord ++ tailWord_3402485) baseStart_3402485 baseEnd_3402485 := by
    simpa [prefixWord, tailWord_3402485, baseEnd_3402485] using wordTrace_append hprefix tailTrace_3402485
  have hstable : (prefixWord ++ tailWord_3402485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3402485).length < 2 ^ (prefixWord ++ tailWord_3402485).sum := by decide
  have hdescent : baseEnd_3402485 < baseStart_3402485 := by decide
  rcases family_descends (prefixWord ++ tailWord_3402485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3402487 : List Nat := [1, 1, 3, 1, 1, 1, 3, 6, 1, 1, 4]
def baseStart_3402487 : Nat := 118140960795 + 3402487 * 2 ^ 59
def prefixEnd_3402487 : Nat := 4983230072969 + 3 ^ 40 * 3402487 * 2
def baseEnd_3402487 : Nat := 1747111251674534487664753

theorem tailTrace_3402487 : CollatzResearch.WordTrace tailWord_3402487 prefixEnd_3402487 1747111251674534487664753 := by
  unfold tailWord_3402487
  simp only [CollatzResearch.WordTrace]
  refine ⟨124098896024378172361093715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82732597349585448240729143 124098896024378172361093715)
  ·
    refine ⟨186148344036567258541640573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124098896024378172361093715 186148344036567258541640573)
    ·
      refine ⟨69805629013712721953115215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186148344036567258541640573 69805629013712721953115215)
      ·
        refine ⟨104708443520569082929672823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69805629013712721953115215 104708443520569082929672823)
        ·
          refine ⟨157062665280853624394509235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104708443520569082929672823 157062665280853624394509235)
          ·
            refine ⟨235593997921280436591763853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157062665280853624394509235 235593997921280436591763853)
            ·
              refine ⟨88347749220480163721911445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 235593997921280436591763853 88347749220480163721911445)
              ·
                refine ⟨4141300744710007674464599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 88347749220480163721911445 4141300744710007674464599)
                ·
                  refine ⟨6211951117065011511696899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4141300744710007674464599 6211951117065011511696899)
                  ·
                    refine ⟨9317926675597517267545349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6211951117065011511696899 9317926675597517267545349)
                    ·
                      refine ⟨1747111251674534487664753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9317926675597517267545349 1747111251674534487664753)
                      ·
                        rfl

theorem cell23_3402487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 6, 1, 1, 4].length) (baseStart_3402487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3402487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3402487 prefixEnd_3402487 := by exact prefixLift 3402487
  have htrace : WordTrace (prefixWord ++ tailWord_3402487) baseStart_3402487 baseEnd_3402487 := by
    simpa [prefixWord, tailWord_3402487, baseEnd_3402487] using wordTrace_append hprefix tailTrace_3402487
  have hstable : (prefixWord ++ tailWord_3402487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3402487).length < 2 ^ (prefixWord ++ tailWord_3402487).sum := by decide
  have hdescent : baseEnd_3402487 < baseStart_3402487 := by decide
  rcases family_descends (prefixWord ++ tailWord_3402487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3402497 : List Nat := [1, 2, 4, 1, 1, 1, 1, 4, 4, 4]
def baseStart_3402497 : Nat := 118140960795 + 3402497 * 2 ^ 59
def prefixEnd_3402497 : Nat := 4983230072969 + 3 ^ 40 * 3402497 * 2
def baseEnd_3402497 : Nat := 582372128827026482846569

theorem tailTrace_3402497 : CollatzResearch.WordTrace tailWord_3402497 prefixEnd_3402497 582372128827026482846569 := by
  unfold tailWord_3402497
  simp only [CollatzResearch.WordTrace]
  refine ⟨124099260754341944068957745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82732840502894629379305163 124099260754341944068957745)
  ·
    refine ⟨93074445565756458051718309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124099260754341944068957745 93074445565756458051718309)
    ·
      refine ⟨17451458543579335884697183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93074445565756458051718309 17451458543579335884697183)
      ·
        refine ⟨26177187815369003827045775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17451458543579335884697183 26177187815369003827045775)
        ·
          refine ⟨39265781723053505740568663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26177187815369003827045775 39265781723053505740568663)
          ·
            refine ⟨58898672584580258610852995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39265781723053505740568663 58898672584580258610852995)
            ·
              refine ⟨88348008876870387916279493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58898672584580258610852995 88348008876870387916279493)
              ·
                refine ⟨16565251664413197734302405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88348008876870387916279493 16565251664413197734302405)
                ·
                  refine ⟨3105984687077474575181701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16565251664413197734302405 3105984687077474575181701)
                  ·
                    refine ⟨582372128827026482846569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3105984687077474575181701 582372128827026482846569)
                    ·
                      rfl

theorem cell23_3402497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 4, 4, 4].length) (baseStart_3402497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3402497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3402497 prefixEnd_3402497 := by exact prefixLift 3402497
  have htrace : WordTrace (prefixWord ++ tailWord_3402497) baseStart_3402497 baseEnd_3402497 := by
    simpa [prefixWord, tailWord_3402497, baseEnd_3402497] using wordTrace_append hprefix tailTrace_3402497
  have hstable : (prefixWord ++ tailWord_3402497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3402497).length < 2 ^ (prefixWord ++ tailWord_3402497).sum := by decide
  have hdescent : baseEnd_3402497 < baseStart_3402497 := by decide
  rcases family_descends (prefixWord ++ tailWord_3402497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3402498 : List Nat := [3, 4, 1, 1, 1, 2, 1, 5, 1, 1, 3]
def baseStart_3402498 : Nat := 118140960795 + 3402498 * 2 ^ 59
def prefixEnd_3402498 : Nat := 4983230072969 + 3 ^ 40 * 3402498 * 2
def baseEnd_3402498 : Nat := 1747116899961733944627203

theorem tailTrace_3402498 : CollatzResearch.WordTrace tailWord_3402498 prefixEnd_3402498 1747116899961733944627203 := by
  unfold tailWord_3402498
  simp only [CollatzResearch.WordTrace]
  refine ⟨31024824306834580309936037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82732864818225547493162765 31024824306834580309936037)
  ·
    refine ⟨5817154557531483808113007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31024824306834580309936037 5817154557531483808113007)
    ·
      refine ⟨8725731836297225712169511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5817154557531483808113007 8725731836297225712169511)
      ·
        refine ⟨13088597754445838568254267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8725731836297225712169511 13088597754445838568254267)
        ·
          refine ⟨19632896631668757852381401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13088597754445838568254267 19632896631668757852381401)
          ·
            refine ⟨14724672473751568389286051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19632896631668757852381401 14724672473751568389286051)
            ·
              refine ⟨22087008710627352583929077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14724672473751568389286051 22087008710627352583929077)
              ·
                refine ⟨2070657066621314304743351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22087008710627352583929077 2070657066621314304743351)
                ·
                  refine ⟨3105985599931971457115027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2070657066621314304743351 3105985599931971457115027)
                  ·
                    refine ⟨4658978399897957185672541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3105985599931971457115027 4658978399897957185672541)
                    ·
                      refine ⟨1747116899961733944627203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4658978399897957185672541 1747116899961733944627203)
                      ·
                        rfl

theorem cell23_3402498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 5, 1, 1, 3].length) (baseStart_3402498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3402498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3402498 prefixEnd_3402498 := by exact prefixLift 3402498
  have htrace : WordTrace (prefixWord ++ tailWord_3402498) baseStart_3402498 baseEnd_3402498 := by
    simpa [prefixWord, tailWord_3402498, baseEnd_3402498] using wordTrace_append hprefix tailTrace_3402498
  have hstable : (prefixWord ++ tailWord_3402498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3402498).length < 2 ^ (prefixWord ++ tailWord_3402498).sum := by decide
  have hdescent : baseEnd_3402498 < baseStart_3402498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3402498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3402504 : List Nat := [2, 1, 3, 2, 2, 3, 1, 3, 1, 1, 4]
def baseStart_3402504 : Nat := 118140960795 + 3402504 * 2 ^ 59
def prefixEnd_3402504 : Nat := 4983230072969 + 3 ^ 40 * 3402504 * 2
def baseEnd_3402504 : Nat := 1747119980845660921152175

theorem tailTrace_3402504 : CollatzResearch.WordTrace tailWord_3402504 prefixEnd_3402504 1747119980845660921152175 := by
  unfold tailWord_3402504
  simp only [CollatzResearch.WordTrace]
  refine ⟨62049758032658292132231283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82733010710211056176308377 62049758032658292132231283)
  ·
    refine ⟨93074637048987438198346925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62049758032658292132231283 93074637048987438198346925)
    ·
      refine ⟨34902988893370289324380097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93074637048987438198346925 34902988893370289324380097)
      ·
        refine ⟨26177241670027716993285073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34902988893370289324380097 26177241670027716993285073)
        ·
          refine ⟨19632931252520787744963805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26177241670027716993285073 19632931252520787744963805)
          ·
            refine ⟨7362349219695295404361427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19632931252520787744963805 7362349219695295404361427)
            ·
              refine ⟨11043523829542943106542141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7362349219695295404361427 11043523829542943106542141)
              ·
                refine ⟨4141321436078603664953303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11043523829542943106542141 4141321436078603664953303)
                ·
                  refine ⟨6211982154117905497429955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4141321436078603664953303 6211982154117905497429955)
                  ·
                    refine ⟨9317973231176858246144933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6211982154117905497429955 9317973231176858246144933)
                    ·
                      refine ⟨1747119980845660921152175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9317973231176858246144933 1747119980845660921152175)
                      ·
                        rfl

theorem cell23_3402504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 3, 1, 1, 4].length) (baseStart_3402504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3402504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3402504 prefixEnd_3402504 := by exact prefixLift 3402504
  have htrace : WordTrace (prefixWord ++ tailWord_3402504) baseStart_3402504 baseEnd_3402504 := by
    simpa [prefixWord, tailWord_3402504, baseEnd_3402504] using wordTrace_append hprefix tailTrace_3402504
  have hstable : (prefixWord ++ tailWord_3402504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3402504).length < 2 ^ (prefixWord ++ tailWord_3402504).sum := by decide
  have hdescent : baseEnd_3402504 < baseStart_3402504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3402504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3402520 : List Nat := [2, 1, 2, 3, 1, 1, 1, 1, 2, 2, 7]
def baseStart_3402520 : Nat := 118140960795 + 3402520 * 2 ^ 59
def prefixEnd_3402520 : Nat := 4983230072969 + 3 ^ 40 * 3402520 * 2
def baseEnd_3402520 : Nat := 1747128196536132858552101

theorem tailTrace_3402520 : CollatzResearch.WordTrace tailWord_3402520 prefixEnd_3402520 1747128196536132858552101 := by
  unfold tailWord_3402520
  simp only [CollatzResearch.WordTrace]
  refine ⟨62050049816629309498522507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82733399755505745998030009 62050049816629309498522507)
  ·
    refine ⟨93075074724943964247783761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62050049816629309498522507 93075074724943964247783761)
    ·
      refine ⟨69806306043707973185837821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93075074724943964247783761 69806306043707973185837821)
      ·
        refine ⟨26177364766390489944689183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69806306043707973185837821 26177364766390489944689183)
        ·
          refine ⟨39266047149585734917033775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26177364766390489944689183 39266047149585734917033775)
          ·
            refine ⟨58899070724378602375550663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39266047149585734917033775 58899070724378602375550663)
            ·
              refine ⟨88348606086567903563325995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58899070724378602375550663 88348606086567903563325995)
              ·
                refine ⟨132522909129851855344988993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88348606086567903563325995 132522909129851855344988993)
                ·
                  refine ⟨99392181847388891508741745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 132522909129851855344988993 99392181847388891508741745)
                  ·
                    refine ⟨74544136385541668631556309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 99392181847388891508741745 74544136385541668631556309)
                    ·
                      refine ⟨1747128196536132858552101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 74544136385541668631556309 1747128196536132858552101)
                      ·
                        rfl

theorem cell23_3402520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_3402520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3402520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3402520 prefixEnd_3402520 := by exact prefixLift 3402520
  have htrace : WordTrace (prefixWord ++ tailWord_3402520) baseStart_3402520 baseEnd_3402520 := by
    simpa [prefixWord, tailWord_3402520, baseEnd_3402520] using wordTrace_append hprefix tailTrace_3402520
  have hstable : (prefixWord ++ tailWord_3402520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3402520).length < 2 ^ (prefixWord ++ tailWord_3402520).sum := by decide
  have hdescent : baseEnd_3402520 < baseStart_3402520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3402520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3402538 : List Nat := [3, 1, 4, 3, 1, 1, 2, 2, 1, 1, 4]
def baseStart_3402538 : Nat := 118140960795 + 3402538 * 2 ^ 59
def prefixEnd_3402538 : Nat := 4983230072969 + 3 ^ 40 * 3402538 * 2
def baseEnd_3402538 : Nat := 1747137439187913788127019

theorem tailTrace_3402538 : CollatzResearch.WordTrace tailWord_3402538 prefixEnd_3402538 1747137439187913788127019 := by
  unfold tailWord_3402538
  simp only [CollatzResearch.WordTrace]
  refine ⟨31025189036798352017800067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82733837431462272047466845 31025189036798352017800067)
  ·
    refine ⟨46537783555197528026700101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31025189036798352017800067 46537783555197528026700101)
    ·
      refine ⟨8725834416599536505006269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46537783555197528026700101 8725834416599536505006269)
      ·
        refine ⟨3272187906224826189377351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8725834416599536505006269 3272187906224826189377351)
        ·
          refine ⟨4908281859337239284066027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3272187906224826189377351 4908281859337239284066027)
          ·
            refine ⟨7362422789005858926099041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4908281859337239284066027 7362422789005858926099041)
            ·
              refine ⟨5521817091754394194574281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7362422789005858926099041 5521817091754394194574281)
              ·
                refine ⟨4141362818815795645930711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5521817091754394194574281 4141362818815795645930711)
                ·
                  refine ⟨6212044228223693468896067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4141362818815795645930711 6212044228223693468896067)
                  ·
                    refine ⟨9318066342335540203344101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6212044228223693468896067 9318066342335540203344101)
                    ·
                      refine ⟨1747137439187913788127019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9318066342335540203344101 1747137439187913788127019)
                      ·
                        rfl

theorem cell23_3402538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_3402538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3402538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3402538 prefixEnd_3402538 := by exact prefixLift 3402538
  have htrace : WordTrace (prefixWord ++ tailWord_3402538) baseStart_3402538 baseEnd_3402538 := by
    simpa [prefixWord, tailWord_3402538, baseEnd_3402538] using wordTrace_append hprefix tailTrace_3402538
  have hstable : (prefixWord ++ tailWord_3402538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3402538).length < 2 ^ (prefixWord ++ tailWord_3402538).sum := by decide
  have hdescent : baseEnd_3402538 < baseStart_3402538 := by decide
  rcases family_descends (prefixWord ++ tailWord_3402538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3402560 : List Nat := [2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 8]
def baseStart_3402560 : Nat := 118140960795 + 3402560 * 2 ^ 59
def prefixEnd_3402560 : Nat := 4983230072969 + 3 ^ 40 * 3402560 * 2
def baseEnd_3402560 : Nat := 1747148735762312702051917

theorem tailTrace_3402560 : CollatzResearch.WordTrace tailWord_3402560 prefixEnd_3402560 1747148735762312702051917 := by
  unfold tailWord_3402560
  simp only [CollatzResearch.WordTrace]
  refine ⟨62050779276556852914250567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82734372368742470552334089 62050779276556852914250567)
  ·
    refine ⟨93076168914835279371375851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62050779276556852914250567 93076168914835279371375851)
    ·
      refine ⟨139614253372252919057063777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93076168914835279371375851 139614253372252919057063777)
      ·
        refine ⟨104710690029189689292797833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139614253372252919057063777 104710690029189689292797833)
        ·
          refine ⟨78533017521892266969598375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104710690029189689292797833 78533017521892266969598375)
          ·
            refine ⟨117799526282838400454397563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78533017521892266969598375 117799526282838400454397563)
            ·
              refine ⟨176699289424257600681596345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117799526282838400454397563 176699289424257600681596345)
              ·
                refine ⟨132524467068193200511197259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 176699289424257600681596345 132524467068193200511197259)
                ·
                  refine ⟨198786700602289800766795889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 132524467068193200511197259 198786700602289800766795889)
                  ·
                    refine ⟨149090025451717350575096917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 198786700602289800766795889 149090025451717350575096917)
                    ·
                      refine ⟨1747148735762312702051917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 149090025451717350575096917 1747148735762312702051917)
                      ·
                        rfl

theorem cell23_3402560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 8].length) (baseStart_3402560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3402560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3402560 prefixEnd_3402560 := by exact prefixLift 3402560
  have htrace : WordTrace (prefixWord ++ tailWord_3402560) baseStart_3402560 baseEnd_3402560 := by
    simpa [prefixWord, tailWord_3402560, baseEnd_3402560] using wordTrace_append hprefix tailTrace_3402560
  have hstable : (prefixWord ++ tailWord_3402560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3402560).length < 2 ^ (prefixWord ++ tailWord_3402560).sum := by decide
  have hdescent : baseEnd_3402560 < baseStart_3402560 := by decide
  rcases family_descends (prefixWord ++ tailWord_3402560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3402561 : List Nat := [1, 2, 5, 3, 2, 1, 9]
def baseStart_3402561 : Nat := 118140960795 + 3402561 * 2 ^ 59
def prefixEnd_3402561 : Nat := 4983230072969 + 3 ^ 40 * 3402561 * 2
def baseEnd_3402561 : Nat := 21569743817814409853573

theorem tailTrace_3402561 : CollatzResearch.WordTrace tailWord_3402561 prefixEnd_3402561 21569743817814409853573 := by
  unfold tailWord_3402561
  simp only [CollatzResearch.WordTrace]
  refine ⟨124101595026110082999287537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82734396684073388666191691 124101595026110082999287537)
  ·
    refine ⟨93076196269582562249465653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124101595026110082999287537 93076196269582562249465653)
    ·
      refine ⟨8725893400273365210887405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 93076196269582562249465653 8725893400273365210887405)
      ·
        refine ⟨3272210025102511954082777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8725893400273365210887405 3272210025102511954082777)
        ·
          refine ⟨2454157518826883965562083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3272210025102511954082777 2454157518826883965562083)
          ·
            refine ⟨3681236278240325948343125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2454157518826883965562083 3681236278240325948343125)
            ·
              refine ⟨21569743817814409853573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3681236278240325948343125 21569743817814409853573)
              ·
                rfl

theorem cell23_3402561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 9].length) (baseStart_3402561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3402561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3402561 prefixEnd_3402561 := by exact prefixLift 3402561
  have htrace : WordTrace (prefixWord ++ tailWord_3402561) baseStart_3402561 baseEnd_3402561 := by
    simpa [prefixWord, tailWord_3402561, baseEnd_3402561] using wordTrace_append hprefix tailTrace_3402561
  have hstable : (prefixWord ++ tailWord_3402561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3402561).length < 2 ^ (prefixWord ++ tailWord_3402561).sum := by decide
  have hdescent : baseEnd_3402561 < baseStart_3402561 := by decide
  rcases family_descends (prefixWord ++ tailWord_3402561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3402588 : List Nat := [2, 2, 4, 2, 1, 2, 1, 3, 2, 1, 3]
def baseStart_3402588 : Nat := 118140960795 + 3402588 * 2 ^ 59
def prefixEnd_3402588 : Nat := 4983230072969 + 3 ^ 40 * 3402588 * 2
def baseEnd_3402588 : Nat := 1747163113220638592501789

theorem tailTrace_3402588 : CollatzResearch.WordTrace tailWord_3402588 prefixEnd_3402588 1747163113220638592501789 := by
  unfold tailWord_3402588
  simp only [CollatzResearch.WordTrace]
  refine ⟨62051289898506133305260209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82735053198008177740346945 62051289898506133305260209)
  ·
    refine ⟨46538467423879599978945157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62051289898506133305260209 46538467423879599978945157)
    ·
      refine ⟨8725962641977424996052217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46538467423879599978945157 8725962641977424996052217)
      ·
        refine ⟨6544471981483068747039163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8725962641977424996052217 6544471981483068747039163)
        ·
          refine ⟨9816707972224603120558745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6544471981483068747039163 9816707972224603120558745)
          ·
            refine ⟨7362530979168452340419059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9816707972224603120558745 7362530979168452340419059)
            ·
              refine ⟨11043796468752678510628589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7362530979168452340419059 11043796468752678510628589)
              ·
                refine ⟨4141423675782254441485721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11043796468752678510628589 4141423675782254441485721)
                ·
                  refine ⟨3106067756836690831114291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4141423675782254441485721 3106067756836690831114291)
                  ·
                    refine ⟨4659101635255036246671437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3106067756836690831114291 4659101635255036246671437)
                    ·
                      refine ⟨1747163113220638592501789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4659101635255036246671437 1747163113220638592501789)
                      ·
                        rfl

theorem cell23_3402588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_3402588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3402588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3402588 prefixEnd_3402588 := by exact prefixLift 3402588
  have htrace : WordTrace (prefixWord ++ tailWord_3402588) baseStart_3402588 baseEnd_3402588 := by
    simpa [prefixWord, tailWord_3402588, baseEnd_3402588] using wordTrace_append hprefix tailTrace_3402588
  have hstable : (prefixWord ++ tailWord_3402588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3402588).length < 2 ^ (prefixWord ++ tailWord_3402588).sum := by decide
  have hdescent : baseEnd_3402588 < baseStart_3402588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3402588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3402597 : List Nat := [1, 3, 1, 3, 1, 1, 3, 2, 2, 1, 5]
def baseStart_3402597 : Nat := 118140960795 + 3402597 * 2 ^ 59
def prefixEnd_3402597 : Nat := 4983230072969 + 3 ^ 40 * 3402597 * 2
def baseEnd_3402597 : Nat := 1747167734546529057289247

theorem tailTrace_3402597 : CollatzResearch.WordTrace tailWord_3402597 prefixEnd_3402597 1747167734546529057289247 := by
  unfold tailWord_3402597
  simp only [CollatzResearch.WordTrace]
  refine ⟨124102908053979661147598045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82735272035986440765065363 124102908053979661147598045)
  ·
    refine ⟨46538590520242372930349267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124102908053979661147598045 46538590520242372930349267)
    ·
      refine ⟨69807885780363559395523901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46538590520242372930349267 69807885780363559395523901)
      ·
        refine ⟨26177957167636334773321463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69807885780363559395523901 26177957167636334773321463)
        ·
          refine ⟨39266935751454502159982195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26177957167636334773321463 39266935751454502159982195)
          ·
            refine ⟨58900403627181753239973293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39266935751454502159982195 58900403627181753239973293)
            ·
              refine ⟨22087651360193157464989985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58900403627181753239973293 22087651360193157464989985)
              ·
                refine ⟨16565738520144868098742489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22087651360193157464989985 16565738520144868098742489)
                ·
                  refine ⟨12424303890108651074056867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16565738520144868098742489 12424303890108651074056867)
                  ·
                    refine ⟨18636455835162976611085301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12424303890108651074056867 18636455835162976611085301)
                    ·
                      refine ⟨1747167734546529057289247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18636455835162976611085301 1747167734546529057289247)
                      ·
                        rfl

theorem cell23_3402597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_3402597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3402597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3402597 prefixEnd_3402597 := by exact prefixLift 3402597
  have htrace : WordTrace (prefixWord ++ tailWord_3402597) baseStart_3402597 baseEnd_3402597 := by
    simpa [prefixWord, tailWord_3402597, baseEnd_3402597] using wordTrace_append hprefix tailTrace_3402597
  have hstable : (prefixWord ++ tailWord_3402597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3402597).length < 2 ^ (prefixWord ++ tailWord_3402597).sum := by decide
  have hdescent : baseEnd_3402597 < baseStart_3402597 := by decide
  rcases family_descends (prefixWord ++ tailWord_3402597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3402647 : List Nat := [1, 1, 3, 3, 1, 2, 2, 2, 1, 7]
def baseStart_3402647 : Nat := 118140960795 + 3402647 * 2 ^ 59
def prefixEnd_3402647 : Nat := 4983230072969 + 3 ^ 40 * 3402647 * 2
def baseEnd_3402647 : Nat := 582397802859751287221339

theorem tailTrace_3402647 : CollatzResearch.WordTrace tailWord_3402647 prefixEnd_3402647 582397802859751287221339 := by
  unfold tailWord_3402647
  simp only [CollatzResearch.WordTrace]
  refine ⟨124104731703798519686918195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82736487802532346457945463 124104731703798519686918195)
  ·
    refine ⟨186157097555697779530377293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124104731703798519686918195 186157097555697779530377293)
    ·
      refine ⟨69808911583386667323891485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186157097555697779530377293 69808911583386667323891485)
      ·
        refine ⟨26178341843770000246459307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69808911583386667323891485 26178341843770000246459307)
        ·
          refine ⟨39267512765655000369688961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26178341843770000246459307 39267512765655000369688961)
          ·
            refine ⟨29450634574241250277266721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39267512765655000369688961 29450634574241250277266721)
            ·
              refine ⟨22087975930680937707950041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29450634574241250277266721 22087975930680937707950041)
              ·
                refine ⟨16565981948010703280962531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22087975930680937707950041 16565981948010703280962531)
                ·
                  refine ⟨24848972922016054921443797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16565981948010703280962531 24848972922016054921443797)
                  ·
                    refine ⟨582397802859751287221339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24848972922016054921443797 582397802859751287221339)
                    ·
                      rfl

theorem cell23_3402647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 2, 1, 7].length) (baseStart_3402647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3402647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3402647 prefixEnd_3402647 := by exact prefixLift 3402647
  have htrace : WordTrace (prefixWord ++ tailWord_3402647) baseStart_3402647 baseEnd_3402647 := by
    simpa [prefixWord, tailWord_3402647, baseEnd_3402647] using wordTrace_append hprefix tailTrace_3402647
  have hstable : (prefixWord ++ tailWord_3402647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3402647).length < 2 ^ (prefixWord ++ tailWord_3402647).sum := by decide
  have hdescent : baseEnd_3402647 < baseStart_3402647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3402647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3402667 : List Nat := [1, 1, 1, 1, 2, 1, 1, 7, 1, 3, 4]
def baseStart_3402667 : Nat := 118140960795 + 3402667 * 2 ^ 59
def prefixEnd_3402667 : Nat := 4983230072969 + 3 ^ 40 * 3402667 * 2
def baseEnd_3402667 : Nat := 1747203678192343783413925

theorem tailTrace_3402667 : CollatzResearch.WordTrace tailWord_3402667 prefixEnd_3402667 1747203678192343783413925 := by
  unfold tailWord_3402667
  simp only [CollatzResearch.WordTrace]
  refine ⟨124105461163726063102646255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82736974109150708735097503 124105461163726063102646255)
  ·
    refine ⟨186158191745589094653969383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124105461163726063102646255 186158191745589094653969383)
    ·
      refine ⟨279237287618383641980954075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186158191745589094653969383 279237287618383641980954075)
      ·
        refine ⟨418855931427575462971431113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279237287618383641980954075 418855931427575462971431113)
        ·
          refine ⟨314141948570681597228573335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 418855931427575462971431113 314141948570681597228573335)
          ·
            refine ⟨471212922856022395842860003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314141948570681597228573335 471212922856022395842860003)
            ·
              refine ⟨706819384284033593764290005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 471212922856022395842860003 706819384284033593764290005)
              ·
                refine ⟨16566079319157037353850547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 706819384284033593764290005 16566079319157037353850547)
                ·
                  refine ⟨24849118978735556030775821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16566079319157037353850547 24849118978735556030775821)
                  ·
                    refine ⟨9318419617025833511540933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24849118978735556030775821 9318419617025833511540933)
                    ·
                      refine ⟨1747203678192343783413925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9318419617025833511540933 1747203678192343783413925)
                      ·
                        rfl

theorem cell23_3402667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 7, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 7, 1, 3, 4].length) (baseStart_3402667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3402667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3402667 prefixEnd_3402667 := by exact prefixLift 3402667
  have htrace : WordTrace (prefixWord ++ tailWord_3402667) baseStart_3402667 baseEnd_3402667 := by
    simpa [prefixWord, tailWord_3402667, baseEnd_3402667] using wordTrace_append hprefix tailTrace_3402667
  have hstable : (prefixWord ++ tailWord_3402667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3402667).length < 2 ^ (prefixWord ++ tailWord_3402667).sum := by decide
  have hdescent : baseEnd_3402667 < baseStart_3402667 := by decide
  rcases family_descends (prefixWord ++ tailWord_3402667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3402697 : List Nat := [1, 2, 1, 1, 2, 1, 2, 1, 4, 4, 4]
def baseStart_3402697 : Nat := 118140960795 + 3402697 * 2 ^ 59
def prefixEnd_3402697 : Nat := 4983230072969 + 3 ^ 40 * 3402697 * 2
def baseEnd_3402697 : Nat := 1747219082611978666038787

theorem tailTrace_3402697 : CollatzResearch.WordTrace tailWord_3402697 prefixEnd_3402697 1747219082611978666038787 := by
  unfold tailWord_3402697
  simp only [CollatzResearch.WordTrace]
  refine ⟨124106555353617378226238345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82737703569078252150825563 124106555353617378226238345)
  ·
    refine ⟨93079916515213033669678759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124106555353617378226238345 93079916515213033669678759)
    ·
      refine ⟨139619874772819550504518139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93079916515213033669678759 139619874772819550504518139)
      ·
        refine ⟨209429812159229325756777209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139619874772819550504518139 209429812159229325756777209)
        ·
          refine ⟨157072359119421994317582907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209429812159229325756777209 157072359119421994317582907)
          ·
            refine ⟨235608538679132991476374361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157072359119421994317582907 235608538679132991476374361)
            ·
              refine ⟨176706404009349743607280771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 235608538679132991476374361 176706404009349743607280771)
              ·
                refine ⟨265059606014024615410921157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 176706404009349743607280771 265059606014024615410921157)
                ·
                  refine ⟨49698676127629615389547717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 265059606014024615410921157 49698676127629615389547717)
                  ·
                    refine ⟨9318501773930552885540197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49698676127629615389547717 9318501773930552885540197)
                    ·
                      refine ⟨1747219082611978666038787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9318501773930552885540197 1747219082611978666038787)
                      ·
                        rfl

theorem cell23_3402697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 4, 4].length) (baseStart_3402697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3402697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3402697 prefixEnd_3402697 := by exact prefixLift 3402697
  have htrace : WordTrace (prefixWord ++ tailWord_3402697) baseStart_3402697 baseEnd_3402697 := by
    simpa [prefixWord, tailWord_3402697, baseEnd_3402697] using wordTrace_append hprefix tailTrace_3402697
  have hstable : (prefixWord ++ tailWord_3402697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3402697).length < 2 ^ (prefixWord ++ tailWord_3402697).sum := by decide
  have hdescent : baseEnd_3402697 < baseStart_3402697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3402697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3402728 : List Nat := [2, 1, 4, 1, 1, 1, 5, 3, 1, 4]
def baseStart_3402728 : Nat := 118140960795 + 3402728 * 2 ^ 59
def prefixEnd_3402728 : Nat := 4983230072969 + 3 ^ 40 * 3402728 * 2
def baseEnd_3402728 : Nat := 582411666837422681583715

theorem tailTrace_3402728 : CollatzResearch.WordTrace tailWord_3402728 prefixEnd_3402728 582411666837422681583715 := by
  unfold tailWord_3402728
  simp only [CollatzResearch.WordTrace]
  refine ⟨62053843008252535260308419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82738457344336713680411225 62053843008252535260308419)
  ·
    refine ⟨93080764512378802890462629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62053843008252535260308419 93080764512378802890462629)
    ·
      refine ⟨17452643346071025541961743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93080764512378802890462629 17452643346071025541961743)
      ·
        refine ⟨26178965019106538312942615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17452643346071025541961743 26178965019106538312942615)
        ·
          refine ⟨39268447528659807469413923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26178965019106538312942615 39268447528659807469413923)
          ·
            refine ⟨58902671292989711204120885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39268447528659807469413923 58902671292989711204120885)
            ·
              refine ⟨5522125433717785425386333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58902671292989711204120885 5522125433717785425386333)
              ·
                refine ⟨2070797037644169534519875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5522125433717785425386333 2070797037644169534519875)
                ·
                  refine ⟨3106195556466254301779813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2070797037644169534519875 3106195556466254301779813)
                  ·
                    refine ⟨582411666837422681583715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3106195556466254301779813 582411666837422681583715)
                    ·
                      rfl

theorem cell23_3402728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 3, 1, 4].length) (baseStart_3402728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3402728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3402728 prefixEnd_3402728 := by exact prefixLift 3402728
  have htrace : WordTrace (prefixWord ++ tailWord_3402728) baseStart_3402728 baseEnd_3402728 := by
    simpa [prefixWord, tailWord_3402728, baseEnd_3402728] using wordTrace_append hprefix tailTrace_3402728
  have hstable : (prefixWord ++ tailWord_3402728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3402728).length < 2 ^ (prefixWord ++ tailWord_3402728).sum := by decide
  have hdescent : baseEnd_3402728 < baseStart_3402728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3402728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3402747 : List Nat := [1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 7]
def baseStart_3402747 : Nat := 118140960795 + 3402747 * 2 ^ 59
def prefixEnd_3402747 : Nat := 4983230072969 + 3 ^ 40 * 3402747 * 2
def baseEnd_3402747 : Nat := 1747244756644703470413557

theorem tailTrace_3402747 : CollatzResearch.WordTrace tailWord_3402747 prefixEnd_3402747 1747244756644703470413557 := by
  unfold tailWord_3402747
  simp only [CollatzResearch.WordTrace]
  refine ⟨124108379003436236765558495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82738919335624157843705663 124108379003436236765558495)
  ·
    refine ⟨186162568505154355148337743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124108379003436236765558495 186162568505154355148337743)
    ·
      refine ⟨279243852757731532722506615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186162568505154355148337743 279243852757731532722506615)
      ·
        refine ⟨418865779136597299083759923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279243852757731532722506615 418865779136597299083759923)
        ·
          refine ⟨628298668704895948625639885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 418865779136597299083759923 628298668704895948625639885)
          ·
            refine ⟨235612000764335980734614957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 628298668704895948625639885 235612000764335980734614957)
            ·
              refine ⟨88354500286625992775480609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 235612000764335980734614957 88354500286625992775480609)
              ·
                refine ⟨66265875214969494581610457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88354500286625992775480609 66265875214969494581610457)
                ·
                  refine ⟨49699406411227120936207843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66265875214969494581610457 49699406411227120936207843)
                  ·
                    refine ⟨74549109616840681404311765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49699406411227120936207843 74549109616840681404311765)
                    ·
                      refine ⟨1747244756644703470413557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 74549109616840681404311765 1747244756644703470413557)
                      ·
                        rfl

theorem cell23_3402747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 7].length) (baseStart_3402747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3402747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3402747 prefixEnd_3402747 := by exact prefixLift 3402747
  have htrace : WordTrace (prefixWord ++ tailWord_3402747) baseStart_3402747 baseEnd_3402747 := by
    simpa [prefixWord, tailWord_3402747, baseEnd_3402747] using wordTrace_append hprefix tailTrace_3402747
  have hstable : (prefixWord ++ tailWord_3402747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3402747).length < 2 ^ (prefixWord ++ tailWord_3402747).sum := by decide
  have hdescent : baseEnd_3402747 < baseStart_3402747 := by decide
  rcases family_descends (prefixWord ++ tailWord_3402747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3402778 : List Nat := [3, 1, 1, 3, 1, 2, 4, 1, 2, 3, 2]
def baseStart_3402778 : Nat := 118140960795 + 3402778 * 2 ^ 59
def prefixEnd_3402778 : Nat := 4983230072969 + 3 ^ 40 * 3402778 * 2
def baseEnd_3402778 : Nat := 1747260674544992849125915

theorem tailTrace_3402778 : CollatzResearch.WordTrace tailWord_3402778 prefixEnd_3402778 1747260674544992849125915 := by
  unfold tailWord_3402778
  simp only [CollatzResearch.WordTrace]
  refine ⟨31027377416580982264984247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82739673110882619373291325 31027377416580982264984247)
  ·
    refine ⟨46541066124871473397476371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31027377416580982264984247 46541066124871473397476371)
    ·
      refine ⟨69811599187307210096214557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46541066124871473397476371 69811599187307210096214557)
      ·
        refine ⟨26179349695240203786080459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69811599187307210096214557 26179349695240203786080459)
        ·
          refine ⟨39269024542860305679120689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26179349695240203786080459 39269024542860305679120689)
          ·
            refine ⟨29451768407145229259340517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39269024542860305679120689 29451768407145229259340517)
            ·
              refine ⟨5522206576339730486126347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29451768407145229259340517 5522206576339730486126347)
              ·
                refine ⟨8283309864509595729189521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5522206576339730486126347 8283309864509595729189521)
                ·
                  refine ⟨6212482398382196796892141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8283309864509595729189521 6212482398382196796892141)
                  ·
                    refine ⟨2329680899393323798834553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6212482398382196796892141 2329680899393323798834553)
                    ·
                      refine ⟨1747260674544992849125915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2329680899393323798834553 1747260674544992849125915)
                      ·
                        rfl

theorem cell23_3402778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 1, 2, 3, 2].length) (baseStart_3402778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3402778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3402778 prefixEnd_3402778 := by exact prefixLift 3402778
  have htrace : WordTrace (prefixWord ++ tailWord_3402778) baseStart_3402778 baseEnd_3402778 := by
    simpa [prefixWord, tailWord_3402778, baseEnd_3402778] using wordTrace_append hprefix tailTrace_3402778
  have hstable : (prefixWord ++ tailWord_3402778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3402778).length < 2 ^ (prefixWord ++ tailWord_3402778).sum := by decide
  have hdescent : baseEnd_3402778 < baseStart_3402778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3402778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3402924 : List Nat := [2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 8]
def baseStart_3402924 : Nat := 118140960795 + 3402924 * 2 ^ 59
def prefixEnd_3402924 : Nat := 4983230072969 + 3 ^ 40 * 3402924 * 2
def baseEnd_3402924 : Nat := 1747335642720549277900243

theorem tailTrace_3402924 : CollatzResearch.WordTrace tailWord_3402924 prefixEnd_3402924 1747335642720549277900243 := by
  unfold tailWord_3402924
  simp only [CollatzResearch.WordTrace]
  refine ⟨62057417361897497997375913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82743223149196663996501217 62057417361897497997375913)
  ·
    refine ⟨46543063021423123498031935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62057417361897497997375913 46543063021423123498031935)
    ·
      refine ⟨69814594532134685247047903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46543063021423123498031935 69814594532134685247047903)
      ·
        refine ⟨104721891798202027870571855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69814594532134685247047903 104721891798202027870571855)
        ·
          refine ⟨157082837697303041805857783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104721891798202027870571855 157082837697303041805857783)
          ·
            refine ⟨235624256545954562708786675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157082837697303041805857783 235624256545954562708786675)
            ·
              refine ⟨353436384818931844063180013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235624256545954562708786675 353436384818931844063180013)
              ·
                refine ⟨132538644307099441523692505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 353436384818931844063180013 132538644307099441523692505)
                ·
                  refine ⟨99403983230324581142769379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 132538644307099441523692505 99403983230324581142769379)
                  ·
                    refine ⟨149105974845486871714154069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 99403983230324581142769379 149105974845486871714154069)
                    ·
                      refine ⟨1747335642720549277900243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 149105974845486871714154069 1747335642720549277900243)
                      ·
                        rfl

theorem cell23_3402924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 8].length) (baseStart_3402924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3402924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3402924 prefixEnd_3402924 := by exact prefixLift 3402924
  have htrace : WordTrace (prefixWord ++ tailWord_3402924) baseStart_3402924 baseEnd_3402924 := by
    simpa [prefixWord, tailWord_3402924, baseEnd_3402924] using wordTrace_append hprefix tailTrace_3402924
  have hstable : (prefixWord ++ tailWord_3402924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3402924).length < 2 ^ (prefixWord ++ tailWord_3402924).sum := by decide
  have hdescent : baseEnd_3402924 < baseStart_3402924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3402924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3402931 : List Nat := [1, 1, 1, 2, 3, 2, 2, 3, 2, 3, 3]
def baseStart_3402931 : Nat := 118140960795 + 3402931 * 2 ^ 59
def prefixEnd_3402931 : Nat := 4983230072969 + 3 ^ 40 * 3402931 * 2
def baseEnd_3402931 : Nat := 1747339237085130750512711

theorem tailTrace_3402931 : CollatzResearch.WordTrace tailWord_3402931 prefixEnd_3402931 1747339237085130750512711 := by
  unfold tailWord_3402931
  simp only [CollatzResearch.WordTrace]
  refine ⟨124115090034769636190256647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82743393356513090793504431 124115090034769636190256647)
  ·
    refine ⟨186172635052154454285384971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124115090034769636190256647 186172635052154454285384971)
    ·
      refine ⟨279258952578231681428077457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186172635052154454285384971 279258952578231681428077457)
      ·
        refine ⟨209444214433673761071058093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279258952578231681428077457 209444214433673761071058093)
        ·
          refine ⟨78541580412627660401646785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 209444214433673761071058093 78541580412627660401646785)
          ·
            refine ⟨58906185309470745301235089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78541580412627660401646785 58906185309470745301235089)
            ·
              refine ⟨44179638982103058975926317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58906185309470745301235089 44179638982103058975926317)
              ·
                refine ⟨16567364618288647115972369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44179638982103058975926317 16567364618288647115972369)
                ·
                  refine ⟨12425523463716485336979277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16567364618288647115972369 12425523463716485336979277)
                  ·
                    refine ⟨4659571298893682001367229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12425523463716485336979277 4659571298893682001367229)
                    ·
                      refine ⟨1747339237085130750512711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4659571298893682001367229 1747339237085130750512711)
                      ·
                        rfl

theorem cell23_3402931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 3, 2, 3, 3].length) (baseStart_3402931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3402931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3402931 prefixEnd_3402931 := by exact prefixLift 3402931
  have htrace : WordTrace (prefixWord ++ tailWord_3402931) baseStart_3402931 baseEnd_3402931 := by
    simpa [prefixWord, tailWord_3402931, baseEnd_3402931] using wordTrace_append hprefix tailTrace_3402931
  have hstable : (prefixWord ++ tailWord_3402931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3402931).length < 2 ^ (prefixWord ++ tailWord_3402931).sum := by decide
  have hdescent : baseEnd_3402931 < baseStart_3402931 := by decide
  rcases family_descends (prefixWord ++ tailWord_3402931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3402966 : List Nat := [5, 2, 1, 2, 2, 1, 2, 2, 2, 2, 2]
def baseStart_3402966 : Nat := 118140960795 + 3402966 * 2 ^ 59
def prefixEnd_3402966 : Nat := 4983230072969 + 3 ^ 40 * 3402966 * 2
def baseEnd_3402966 : Nat := 1747357208908038113575051

theorem tailTrace_3402966 : CollatzResearch.WordTrace tailWord_3402966 prefixEnd_3402966 1747357208908038113575051 := by
  unfold tailWord_3402966
  simp only [CollatzResearch.WordTrace]
  refine ⟨7757272911852677322986297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 82744244393095224778520501 7757272911852677322986297)
  ·
    refine ⟨5817954683889507992239723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7757272911852677322986297 5817954683889507992239723)
    ·
      refine ⟨8726932025834261988359585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5817954683889507992239723 8726932025834261988359585)
      ·
        refine ⟨6545199019375696491269689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8726932025834261988359585 6545199019375696491269689)
        ·
          refine ⟨4908899264531772368452267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6545199019375696491269689 4908899264531772368452267)
          ·
            refine ⟨7363348896797658552678401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4908899264531772368452267 7363348896797658552678401)
            ·
              refine ⟨5522511672598243914508801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7363348896797658552678401 5522511672598243914508801)
              ·
                refine ⟨4141883754448682935881601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5522511672598243914508801 4141883754448682935881601)
                ·
                  refine ⟨3106412815836512201911201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4141883754448682935881601 3106412815836512201911201)
                  ·
                    refine ⟨2329809611877384151433401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3106412815836512201911201 2329809611877384151433401)
                    ·
                      refine ⟨1747357208908038113575051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2329809611877384151433401 1747357208908038113575051)
                      ·
                        rfl

theorem cell23_3402966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_3402966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3402966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3402966 prefixEnd_3402966 := by exact prefixLift 3402966
  have htrace : WordTrace (prefixWord ++ tailWord_3402966) baseStart_3402966 baseEnd_3402966 := by
    simpa [prefixWord, tailWord_3402966, baseEnd_3402966] using wordTrace_append hprefix tailTrace_3402966
  have hstable : (prefixWord ++ tailWord_3402966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3402966).length < 2 ^ (prefixWord ++ tailWord_3402966).sum := by decide
  have hdescent : baseEnd_3402966 < baseStart_3402966 := by decide
  rcases family_descends (prefixWord ++ tailWord_3402966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3402988 : List Nat := [2, 2, 1, 1, 2, 4, 1, 1, 1, 6, 2]
def baseStart_3402988 : Nat := 118140960795 + 3402988 * 2 ^ 59
def prefixEnd_3402988 : Nat := 4983230072969 + 3 ^ 40 * 3402988 * 2
def baseEnd_3402988 : Nat := 1747368505482437027499949

theorem tailTrace_3402988 : CollatzResearch.WordTrace tailWord_3402988 prefixEnd_3402988 1747368505482437027499949 := by
  unfold tailWord_3402988
  simp only [CollatzResearch.WordTrace]
  refine ⟨62058584497781567462540809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82744779330375423283387745 62058584497781567462540809)
  ·
    refine ⟨46543938373336175596905607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62058584497781567462540809 46543938373336175596905607)
    ·
      refine ⟨69815907560004263395358411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46543938373336175596905607 69815907560004263395358411)
      ·
        refine ⟨104723861340006395093037617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69815907560004263395358411 104723861340006395093037617)
        ·
          refine ⟨78542896005004796319778213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104723861340006395093037617 78542896005004796319778213)
          ·
            refine ⟨14726793000938399309958415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78542896005004796319778213 14726793000938399309958415)
            ·
              refine ⟨22090189501407598964937623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14726793000938399309958415 22090189501407598964937623)
              ·
                refine ⟨33135284252111398447406435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22090189501407598964937623 33135284252111398447406435)
                ·
                  refine ⟨49702926378167097671109653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33135284252111398447406435 49702926378167097671109653)
                  ·
                    refine ⟨2329824673976582703333265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 49702926378167097671109653 2329824673976582703333265)
                    ·
                      refine ⟨1747368505482437027499949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2329824673976582703333265 1747368505482437027499949)
                      ·
                        rfl

theorem cell23_3402988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 6, 2].length) (baseStart_3402988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3402988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3402988 prefixEnd_3402988 := by exact prefixLift 3402988
  have htrace : WordTrace (prefixWord ++ tailWord_3402988) baseStart_3402988 baseEnd_3402988 := by
    simpa [prefixWord, tailWord_3402988, baseEnd_3402988] using wordTrace_append hprefix tailTrace_3402988
  have hstable : (prefixWord ++ tailWord_3402988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3402988).length < 2 ^ (prefixWord ++ tailWord_3402988).sum := by decide
  have hdescent : baseEnd_3402988 < baseStart_3402988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3402988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3403031 : List Nat := [1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 8]
def baseStart_3403031 : Nat := 118140960795 + 3403031 * 2 ^ 59
def prefixEnd_3403031 : Nat := 4983230072969 + 3 ^ 40 * 3403031 * 2
def baseEnd_3403031 : Nat := 1747390585150580359262251

theorem tailTrace_3403031 : CollatzResearch.WordTrace tailWord_3403031 prefixEnd_3403031 1747390585150580359262251 := by
  unfold tailWord_3403031
  simp only [CollatzResearch.WordTrace]
  refine ⟨124118737334407353268896947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82745824889604902179264631 124118737334407353268896947)
  ·
    refine ⟨186178106001611029903345421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124118737334407353268896947 186178106001611029903345421)
    ·
      refine ⟨69816789750604136213754533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186178106001611029903345421 69816789750604136213754533)
      ·
        refine ⟨13090648078238275540078975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69816789750604136213754533 13090648078238275540078975)
        ·
          refine ⟨19635972117357413310118463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13090648078238275540078975 19635972117357413310118463)
          ·
            refine ⟨29453958176036119965177695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19635972117357413310118463 29453958176036119965177695)
            ·
              refine ⟨44180937264054179947766543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29453958176036119965177695 44180937264054179947766543)
              ·
                refine ⟨66271405896081269921649815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44180937264054179947766543 66271405896081269921649815)
                ·
                  refine ⟨99407108844121904882474723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66271405896081269921649815 99407108844121904882474723)
                  ·
                    refine ⟨149110663266182857323712085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 99407108844121904882474723 149110663266182857323712085)
                    ·
                      refine ⟨1747390585150580359262251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 149110663266182857323712085 1747390585150580359262251)
                      ·
                        rfl

theorem cell23_3403031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_3403031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3403031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3403031 prefixEnd_3403031 := by exact prefixLift 3403031
  have htrace : WordTrace (prefixWord ++ tailWord_3403031) baseStart_3403031 baseEnd_3403031 := by
    simpa [prefixWord, tailWord_3403031, baseEnd_3403031] using wordTrace_append hprefix tailTrace_3403031
  have hstable : (prefixWord ++ tailWord_3403031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3403031).length < 2 ^ (prefixWord ++ tailWord_3403031).sum := by decide
  have hdescent : baseEnd_3403031 < baseStart_3403031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3403031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3403045 : List Nat := [1, 3, 1, 2, 4, 2, 3, 1, 6]
def baseStart_3403045 : Nat := 118140960795 + 3403045 * 2 ^ 59
def prefixEnd_3403045 : Nat := 4983230072969 + 3 ^ 40 * 3403045 * 2
def baseEnd_3403045 : Nat := 194155308208860367165243

theorem tailTrace_3403045 : CollatzResearch.WordTrace tailWord_3403045 prefixEnd_3403045 194155308208860367165243 := by
  unfold tailWord_3403045
  simp only [CollatzResearch.WordTrace]
  refine ⟨124119247956356633659906589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82746165304237755773271059 124119247956356633659906589)
  ·
    refine ⟨46544717983633737622464971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124119247956356633659906589 46544717983633737622464971)
    ·
      refine ⟨69817076975450606433697457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46544717983633737622464971 69817076975450606433697457)
      ·
        refine ⟨52362807731587954825273093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69817076975450606433697457 52362807731587954825273093)
        ·
          refine ⟨9818026449672741529738705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52362807731587954825273093 9818026449672741529738705)
          ·
            refine ⟨7363519837254556147304029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9818026449672741529738705 7363519837254556147304029)
            ·
              refine ⟨2761319938970458555239011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7363519837254556147304029 2761319938970458555239011)
              ·
                refine ⟨4141979908455687832858517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2761319938970458555239011 4141979908455687832858517)
                ·
                  refine ⟨194155308208860367165243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4141979908455687832858517 194155308208860367165243)
                  ·
                    rfl

theorem cell23_3403045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 3, 1, 6].length) (baseStart_3403045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3403045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3403045 prefixEnd_3403045 := by exact prefixLift 3403045
  have htrace : WordTrace (prefixWord ++ tailWord_3403045) baseStart_3403045 baseEnd_3403045 := by
    simpa [prefixWord, tailWord_3403045, baseEnd_3403045] using wordTrace_append hprefix tailTrace_3403045
  have hstable : (prefixWord ++ tailWord_3403045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3403045).length < 2 ^ (prefixWord ++ tailWord_3403045).sum := by decide
  have hdescent : baseEnd_3403045 < baseStart_3403045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3403045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3403088 : List Nat := [2, 1, 1, 1, 1, 5, 1, 3, 4, 4]
def baseStart_3403088 : Nat := 118140960795 + 3403088 * 2 ^ 59
def prefixEnd_3403088 : Nat := 4983230072969 + 3 ^ 40 * 3403088 * 2
def baseEnd_3403088 : Nat := 582473284515962212083163

theorem tailTrace_3403088 : CollatzResearch.WordTrace tailWord_3403088 prefixEnd_3403088 582473284515962212083163 := by
  unfold tailWord_3403088
  simp only [CollatzResearch.WordTrace]
  refine ⟨62060408147600426001860959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82747210863467234669147945 62060408147600426001860959)
  ·
    refine ⟨93090612221400639002791439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62060408147600426001860959 93090612221400639002791439)
    ·
      refine ⟨139635918332100958504187159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93090612221400639002791439 139635918332100958504187159)
      ·
        refine ⟨209453877498151437756280739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139635918332100958504187159 209453877498151437756280739)
        ·
          refine ⟨314180816247227156634421109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209453877498151437756280739 314180816247227156634421109)
          ·
            refine ⟨29454451523177545934476979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 314180816247227156634421109 29454451523177545934476979)
            ·
              refine ⟨44181677284766318901715469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29454451523177545934476979 44181677284766318901715469)
              ·
                refine ⟨16568128981787369588143301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44181677284766318901715469 16568128981787369588143301)
                ·
                  refine ⟨3106524184085131797776869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16568128981787369588143301 3106524184085131797776869)
                  ·
                    refine ⟨582473284515962212083163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3106524184085131797776869 582473284515962212083163)
                    ·
                      rfl

theorem cell23_3403088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 3, 4, 4].length) (baseStart_3403088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3403088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3403088 prefixEnd_3403088 := by exact prefixLift 3403088
  have htrace : WordTrace (prefixWord ++ tailWord_3403088) baseStart_3403088 baseEnd_3403088 := by
    simpa [prefixWord, tailWord_3403088, baseEnd_3403088] using wordTrace_append hprefix tailTrace_3403088
  have hstable : (prefixWord ++ tailWord_3403088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3403088).length < 2 ^ (prefixWord ++ tailWord_3403088).sum := by decide
  have hdescent : baseEnd_3403088 < baseStart_3403088 := by decide
  rcases family_descends (prefixWord ++ tailWord_3403088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3403089 : List Nat := [1, 2, 2, 1, 4, 1, 5, 2, 1, 1, 3]
def baseStart_3403089 : Nat := 118140960795 + 3403089 * 2 ^ 59
def prefixEnd_3403089 : Nat := 4983230072969 + 3 ^ 40 * 3403089 * 2
def baseEnd_3403089 : Nat := 1747420367028541132336985

theorem tailTrace_3403089 : CollatzResearch.WordTrace tailWord_3403089 prefixEnd_3403089 1747420367028541132336985 := by
  unfold tailWord_3403089
  simp only [CollatzResearch.WordTrace]
  refine ⟨124120852768197229174508321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82747235178798152783005547 124120852768197229174508321)
  ·
    refine ⟨93090639576147921880881241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124120852768197229174508321 93090639576147921880881241)
    ·
      refine ⟨69817979682110941410660931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93090639576147921880881241 69817979682110941410660931)
      ·
        refine ⟨104726969523166412115991397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69817979682110941410660931 104726969523166412115991397)
        ·
          refine ⟨19636306785593702271748387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104726969523166412115991397 19636306785593702271748387)
          ·
            refine ⟨29454460178390553407622581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19636306785593702271748387 29454460178390553407622581)
            ·
              refine ⟨2761355641724114381964617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29454460178390553407622581 2761355641724114381964617)
              ·
                refine ⟨2071016731293085786473463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2761355641724114381964617 2071016731293085786473463)
                ·
                  refine ⟨3106525096939628679710195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2071016731293085786473463 3106525096939628679710195)
                  ·
                    refine ⟨4659787645409443019565293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3106525096939628679710195 4659787645409443019565293)
                    ·
                      refine ⟨1747420367028541132336985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4659787645409443019565293 1747420367028541132336985)
                      ·
                        rfl

theorem cell23_3403089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 5, 2, 1, 1, 3].length) (baseStart_3403089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3403089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3403089 prefixEnd_3403089 := by exact prefixLift 3403089
  have htrace : WordTrace (prefixWord ++ tailWord_3403089) baseStart_3403089 baseEnd_3403089 := by
    simpa [prefixWord, tailWord_3403089, baseEnd_3403089] using wordTrace_append hprefix tailTrace_3403089
  have hstable : (prefixWord ++ tailWord_3403089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3403089).length < 2 ^ (prefixWord ++ tailWord_3403089).sum := by decide
  have hdescent : baseEnd_3403089 < baseStart_3403089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3403089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3403091 : List Nat := [1, 1, 1, 2, 1, 1, 5, 1, 3, 1, 6]
def baseStart_3403091 : Nat := 118140960795 + 3403091 * 2 ^ 59
def prefixEnd_3403091 : Nat := 4983230072969 + 3 ^ 40 * 3403091 * 2
def baseEnd_3403091 : Nat := 1747421393989850124511975

theorem tailTrace_3403091 : CollatzResearch.WordTrace tailWord_3403091 prefixEnd_3403091 1747421393989850124511975 := by
  unfold tailWord_3403091
  simp only [CollatzResearch.WordTrace]
  refine ⟨124120925714189983516081127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82747283809459989010720751 124120925714189983516081127)
  ·
    refine ⟨186181388571284975274121691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124120925714189983516081127 186181388571284975274121691)
    ·
      refine ⟨279272082856927462911182537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186181388571284975274121691 279272082856927462911182537)
      ·
        refine ⟨209454062142695597183386903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279272082856927462911182537 209454062142695597183386903)
        ·
          refine ⟨314181093214043395775080355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209454062142695597183386903 314181093214043395775080355)
          ·
            refine ⟨471271639821065093662620533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314181093214043395775080355 471271639821065093662620533)
            ·
              refine ⟨44181716233224852530870675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 471271639821065093662620533 44181716233224852530870675)
              ·
                refine ⟨66272574349837278796306013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44181716233224852530870675 66272574349837278796306013)
                ·
                  refine ⟨24852215381188979548614755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66272574349837278796306013 24852215381188979548614755)
                  ·
                    refine ⟨37278323071783469322922133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24852215381188979548614755 37278323071783469322922133)
                    ·
                      refine ⟨1747421393989850124511975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37278323071783469322922133 1747421393989850124511975)
                      ·
                        rfl

theorem cell23_3403091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 3, 1, 6].length) (baseStart_3403091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3403091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3403091 prefixEnd_3403091 := by exact prefixLift 3403091
  have htrace : WordTrace (prefixWord ++ tailWord_3403091) baseStart_3403091 baseEnd_3403091 := by
    simpa [prefixWord, tailWord_3403091, baseEnd_3403091] using wordTrace_append hprefix tailTrace_3403091
  have hstable : (prefixWord ++ tailWord_3403091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3403091).length < 2 ^ (prefixWord ++ tailWord_3403091).sum := by decide
  have hdescent : baseEnd_3403091 < baseStart_3403091 := by decide
  rcases family_descends (prefixWord ++ tailWord_3403091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3403098 : List Nat := [3, 1, 1, 2, 1, 2, 4, 2, 1, 1, 5]
def baseStart_3403098 : Nat := 118140960795 + 3403098 * 2 ^ 59
def prefixEnd_3403098 : Nat := 4983230072969 + 3 ^ 40 * 3403098 * 2
def baseEnd_3403098 : Nat := 1747424988354431597124443

theorem tailTrace_3403098 : CollatzResearch.WordTrace tailWord_3403098 prefixEnd_3403098 1747424988354431597124443 := by
  unfold tailWord_3403098
  simp only [CollatzResearch.WordTrace]
  refine ⟨31030295256291155927896487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82747454016776415807723965 31030295256291155927896487)
  ·
    refine ⟨46545442884436733891844731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31030295256291155927896487 46545442884436733891844731)
    ·
      refine ⟨69818164326655100837767097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46545442884436733891844731 69818164326655100837767097)
      ·
        refine ⟨52363623244991325628325323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69818164326655100837767097 52363623244991325628325323)
        ·
          refine ⟨78545434867486988442487985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52363623244991325628325323 78545434867486988442487985)
          ·
            refine ⟨58909076150615241331865989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78545434867486988442487985 58909076150615241331865989)
            ·
              refine ⟨11045451778240357749724873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58909076150615241331865989 11045451778240357749724873)
              ·
                refine ⟨8284088833680268312293655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11045451778240357749724873 8284088833680268312293655)
                ·
                  refine ⟨12426133250520402468440483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8284088833680268312293655 12426133250520402468440483)
                  ·
                    refine ⟨18639199875780603702660725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12426133250520402468440483 18639199875780603702660725)
                    ·
                      refine ⟨1747424988354431597124443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18639199875780603702660725 1747424988354431597124443)
                      ·
                        rfl

theorem cell23_3403098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 2, 1, 1, 5].length) (baseStart_3403098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3403098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3403098 prefixEnd_3403098 := by exact prefixLift 3403098
  have htrace : WordTrace (prefixWord ++ tailWord_3403098) baseStart_3403098 baseEnd_3403098 := by
    simpa [prefixWord, tailWord_3403098, baseEnd_3403098] using wordTrace_append hprefix tailTrace_3403098
  have hstable : (prefixWord ++ tailWord_3403098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3403098).length < 2 ^ (prefixWord ++ tailWord_3403098).sum := by decide
  have hdescent : baseEnd_3403098 < baseStart_3403098 := by decide
  rcases family_descends (prefixWord ++ tailWord_3403098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3403108 : List Nat := [2, 3, 1, 1, 3, 2, 2, 1, 1, 1, 6]
def baseStart_3403108 : Nat := 118140960795 + 3403108 * 2 ^ 59
def prefixEnd_3403108 : Nat := 4983230072969 + 3 ^ 40 * 3403108 * 2
def baseEnd_3403108 : Nat := 1747430123160976557999397

theorem tailTrace_3403108 : CollatzResearch.WordTrace tailWord_3403108 prefixEnd_3403108 1747430123160976557999397 := by
  unfold tailWord_3403108
  simp only [CollatzResearch.WordTrace]
  refine ⟨62060772877564197709724989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82747697170085596946299985 62060772877564197709724989)
  ·
    refine ⟨23272789829086574141146871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62060772877564197709724989 23272789829086574141146871)
    ·
      refine ⟨34909184743629861211720307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23272789829086574141146871 34909184743629861211720307)
      ·
        refine ⟨52363777115444791817580461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34909184743629861211720307 52363777115444791817580461)
        ·
          refine ⟨19636416418291796931592673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52363777115444791817580461 19636416418291796931592673)
          ·
            refine ⟨14727312313718847698694505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19636416418291796931592673 14727312313718847698694505)
            ·
              refine ⟨11045484235289135774020879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14727312313718847698694505 11045484235289135774020879)
              ·
                refine ⟨16568226352933703661031319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11045484235289135774020879 16568226352933703661031319)
                ·
                  refine ⟨24852339529400555491546979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16568226352933703661031319 24852339529400555491546979)
                  ·
                    refine ⟨37278509294100833237320469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24852339529400555491546979 37278509294100833237320469)
                    ·
                      refine ⟨1747430123160976557999397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37278509294100833237320469 1747430123160976557999397)
                      ·
                        rfl

theorem cell23_3403108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 1, 1, 1, 6].length) (baseStart_3403108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3403108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3403108 prefixEnd_3403108 := by exact prefixLift 3403108
  have htrace : WordTrace (prefixWord ++ tailWord_3403108) baseStart_3403108 baseEnd_3403108 := by
    simpa [prefixWord, tailWord_3403108, baseEnd_3403108] using wordTrace_append hprefix tailTrace_3403108
  have hstable : (prefixWord ++ tailWord_3403108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3403108).length < 2 ^ (prefixWord ++ tailWord_3403108).sum := by decide
  have hdescent : baseEnd_3403108 < baseStart_3403108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3403108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3403132 : List Nat := [2, 2, 2, 1, 1, 1, 7, 1, 1, 2, 3]
def baseStart_3403132 : Nat := 118140960795 + 3403132 * 2 ^ 59
def prefixEnd_3403132 : Nat := 4983230072969 + 3 ^ 40 * 3403132 * 2
def baseEnd_3403132 : Nat := 1747442446696684464099287

theorem tailTrace_3403132 : CollatzResearch.WordTrace tailWord_3403132 prefixEnd_3403132 1747442446696684464099287 := by
  unfold tailWord_3403132
  simp only [CollatzResearch.WordTrace]
  refine ⟨62061210553520723759161825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82748280738027631678882433 62061210553520723759161825)
  ·
    refine ⟨46545907915140542819371369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62061210553520723759161825 46545907915140542819371369)
    ·
      refine ⟨34909430936355407114528527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46545907915140542819371369 34909430936355407114528527)
      ·
        refine ⟨52364146404533110671792791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34909430936355407114528527 52364146404533110671792791)
        ·
          refine ⟨78546219606799666007689187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52364146404533110671792791 78546219606799666007689187)
          ·
            refine ⟨117819329410199499011533781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78546219606799666007689187 117819329410199499011533781)
            ·
              refine ⟨2761390533051550758082823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 117819329410199499011533781 2761390533051550758082823)
              ·
                refine ⟨4142085799577326137124235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2761390533051550758082823 4142085799577326137124235)
                ·
                  refine ⟨6213128699365989205686353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4142085799577326137124235 6213128699365989205686353)
                  ·
                    refine ⟨4659846524524491904264765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6213128699365989205686353 4659846524524491904264765)
                    ·
                      refine ⟨1747442446696684464099287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4659846524524491904264765 1747442446696684464099287)
                      ·
                        rfl

theorem cell23_3403132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 7, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 7, 1, 1, 2, 3].length) (baseStart_3403132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3403132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3403132 prefixEnd_3403132 := by exact prefixLift 3403132
  have htrace : WordTrace (prefixWord ++ tailWord_3403132) baseStart_3403132 baseEnd_3403132 := by
    simpa [prefixWord, tailWord_3403132, baseEnd_3403132] using wordTrace_append hprefix tailTrace_3403132
  have hstable : (prefixWord ++ tailWord_3403132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3403132).length < 2 ^ (prefixWord ++ tailWord_3403132).sum := by decide
  have hdescent : baseEnd_3403132 < baseStart_3403132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3403132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3403162 : List Nat := [3, 1, 1, 4, 1, 1, 1, 5, 2, 1, 3]
def baseStart_3403162 : Nat := 118140960795 + 3403162 * 2 ^ 59
def prefixEnd_3403162 : Nat := 4983230072969 + 3 ^ 40 * 3403162 * 2
def baseEnd_3403162 : Nat := 1747457851116319346724149

theorem tailTrace_3403162 : CollatzResearch.WordTrace tailWord_3403162 prefixEnd_3403162 1747457851116319346724149 := by
  unfold tailWord_3403162
  simp only [CollatzResearch.WordTrace]
  refine ⟨31030878824233190660478935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82749010197955175094610493 31030878824233190660478935)
  ·
    refine ⟨46546318236349785990718403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31030878824233190660478935 46546318236349785990718403)
    ·
      refine ⟨69819477354524678986077605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46546318236349785990718403 69819477354524678986077605)
      ·
        refine ⟨13091152003973377309889551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69819477354524678986077605 13091152003973377309889551)
        ·
          refine ⟨19636728005960065964834327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13091152003973377309889551 19636728005960065964834327)
          ·
            refine ⟨29455092008940098947251491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19636728005960065964834327 29455092008940098947251491)
            ·
              refine ⟨44182638013410148420877237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29455092008940098947251491 44182638013410148420877237)
              ·
                refine ⟨4142122313757201414457241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44182638013410148420877237 4142122313757201414457241)
                ·
                  refine ⟨3106591735317901060842931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4142122313757201414457241 3106591735317901060842931)
                  ·
                    refine ⟨4659887602976851591264397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3106591735317901060842931 4659887602976851591264397)
                    ·
                      refine ⟨1747457851116319346724149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4659887602976851591264397 1747457851116319346724149)
                      ·
                        rfl

theorem cell23_3403162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_3403162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3403162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3403162 prefixEnd_3403162 := by exact prefixLift 3403162
  have htrace : WordTrace (prefixWord ++ tailWord_3403162) baseStart_3403162 baseEnd_3403162 := by
    simpa [prefixWord, tailWord_3403162, baseEnd_3403162] using wordTrace_append hprefix tailTrace_3403162
  have hstable : (prefixWord ++ tailWord_3403162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3403162).length < 2 ^ (prefixWord ++ tailWord_3403162).sum := by decide
  have hdescent : baseEnd_3403162 < baseStart_3403162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3403162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3403168 : List Nat := [2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 4]
def baseStart_3403168 : Nat := 118140960795 + 3403168 * 2 ^ 59
def prefixEnd_3403168 : Nat := 4983230072969 + 3 ^ 40 * 3403168 * 2
def baseEnd_3403168 : Nat := 1747460932000246323249121

theorem tailTrace_3403168 : CollatzResearch.WordTrace tailWord_3403168 prefixEnd_3403168 1747460932000246323249121 := by
  unfold tailWord_3403168
  simp only [CollatzResearch.WordTrace]
  refine ⟨62061867067455512833317079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82749156089940683777756105 62061867067455512833317079)
  ·
    refine ⟨93092800601183269249975619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62061867067455512833317079 93092800601183269249975619)
    ·
      refine ⟨139639200901774903874963429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93092800601183269249975619 139639200901774903874963429)
      ·
        refine ⟨26182350169082794476555643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139639200901774903874963429 26182350169082794476555643)
        ·
          refine ⟨39273525253624191714833465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26182350169082794476555643 39273525253624191714833465)
          ·
            refine ⟨29455143940218143786125099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39273525253624191714833465 29455143940218143786125099)
            ·
              refine ⟨44182715910327215679187649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29455143940218143786125099 44182715910327215679187649)
              ·
                refine ⟨33137036932745411759390737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44182715910327215679187649 33137036932745411759390737)
                ·
                  refine ⟨24852777699559058819543053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33137036932745411759390737 24852777699559058819543053)
                  ·
                    refine ⟨9319791637334647057328645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24852777699559058819543053 9319791637334647057328645)
                    ·
                      refine ⟨1747460932000246323249121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9319791637334647057328645 1747460932000246323249121)
                      ·
                        rfl

theorem cell23_3403168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_3403168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3403168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3403168 prefixEnd_3403168 := by exact prefixLift 3403168
  have htrace : WordTrace (prefixWord ++ tailWord_3403168) baseStart_3403168 baseEnd_3403168 := by
    simpa [prefixWord, tailWord_3403168, baseEnd_3403168] using wordTrace_append hprefix tailTrace_3403168
  have hstable : (prefixWord ++ tailWord_3403168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3403168).length < 2 ^ (prefixWord ++ tailWord_3403168).sum := by decide
  have hdescent : baseEnd_3403168 < baseStart_3403168 := by decide
  rcases family_descends (prefixWord ++ tailWord_3403168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3403172 : List Nat := [2, 3, 1, 2, 1, 1, 1, 6, 1, 3, 2]
def baseStart_3403172 : Nat := 118140960795 + 3403172 * 2 ^ 59
def prefixEnd_3403172 : Nat := 4983230072969 + 3 ^ 40 * 3403172 * 2
def baseEnd_3403172 : Nat := 1747462985922864307599103

theorem tailTrace_3403172 : CollatzResearch.WordTrace tailWord_3403172 prefixEnd_3403172 1747462985922864307599103 := by
  unfold tailWord_3403172
  simp only [CollatzResearch.WordTrace]
  refine ⟨62061940013448267174889885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82749253351264356233186513 62061940013448267174889885)
  ·
    refine ⟨23273227505043100190583707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62061940013448267174889885 23273227505043100190583707)
    ·
      refine ⟨34909841257564650285875561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23273227505043100190583707 34909841257564650285875561)
      ·
        refine ⟨26182380943173487714406671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34909841257564650285875561 26182380943173487714406671)
        ·
          refine ⟨39273571414760231571610007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26182380943173487714406671 39273571414760231571610007)
          ·
            refine ⟨58910357122140347357415011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39273571414760231571610007 58910357122140347357415011)
            ·
              refine ⟨88365535683210521036122517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58910357122140347357415011 88365535683210521036122517)
              ·
                refine ⟨4142134485150493173568243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 88365535683210521036122517 4142134485150493173568243)
                ·
                  refine ⟨6213201727725739760352365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4142134485150493173568243 6213201727725739760352365)
                  ·
                    refine ⟨2329950647897152410132137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6213201727725739760352365 2329950647897152410132137)
                    ·
                      refine ⟨1747462985922864307599103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2329950647897152410132137 1747462985922864307599103)
                      ·
                        rfl

theorem cell23_3403172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 6, 1, 3, 2].length) (baseStart_3403172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3403172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3403172 prefixEnd_3403172 := by exact prefixLift 3403172
  have htrace : WordTrace (prefixWord ++ tailWord_3403172) baseStart_3403172 baseEnd_3403172 := by
    simpa [prefixWord, tailWord_3403172, baseEnd_3403172] using wordTrace_append hprefix tailTrace_3403172
  have hstable : (prefixWord ++ tailWord_3403172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3403172).length < 2 ^ (prefixWord ++ tailWord_3403172).sum := by decide
  have hdescent : baseEnd_3403172 < baseStart_3403172 := by decide
  rcases family_descends (prefixWord ++ tailWord_3403172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3403189 : List Nat := [1, 3, 3, 2, 2, 2, 1, 3, 1, 3, 2]
def baseStart_3403189 : Nat := 118140960795 + 3403189 * 2 ^ 59
def prefixEnd_3403189 : Nat := 4983230072969 + 3 ^ 40 * 3403189 * 2
def baseEnd_3403189 : Nat := 1747471715093990741086525

theorem tailTrace_3403189 : CollatzResearch.WordTrace tailWord_3403189 prefixEnd_3403189 1747471715093990741086525 := by
  unfold tailWord_3403189
  simp only [CollatzResearch.WordTrace]
  refine ⟨124124500067834946253148621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82749666711889964168765747 124124500067834946253148621)
  ·
    refine ⟨46546687525438104844930733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124124500067834946253148621 46546687525438104844930733)
    ·
      refine ⟨17455007822039289316849025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46546687525438104844930733 17455007822039289316849025)
      ·
        refine ⟨13091255866529466987636769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17455007822039289316849025 13091255866529466987636769)
        ·
          refine ⟨9818441899897100240727577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13091255866529466987636769 9818441899897100240727577)
          ·
            refine ⟨7363831424922825180545683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9818441899897100240727577 7363831424922825180545683)
            ·
              refine ⟨11045747137384237770818525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7363831424922825180545683 11045747137384237770818525)
              ·
                refine ⟨4142155176519089164056947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11045747137384237770818525 4142155176519089164056947)
                ·
                  refine ⟨6213232764778633746085421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4142155176519089164056947 6213232764778633746085421)
                  ·
                    refine ⟨2329962286791987654782033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6213232764778633746085421 2329962286791987654782033)
                    ·
                      refine ⟨1747471715093990741086525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2329962286791987654782033 1747471715093990741086525)
                      ·
                        rfl

theorem cell23_3403189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 3, 1, 3, 2].length) (baseStart_3403189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3403189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3403189 prefixEnd_3403189 := by exact prefixLift 3403189
  have htrace : WordTrace (prefixWord ++ tailWord_3403189) baseStart_3403189 baseEnd_3403189 := by
    simpa [prefixWord, tailWord_3403189, baseEnd_3403189] using wordTrace_append hprefix tailTrace_3403189
  have hstable : (prefixWord ++ tailWord_3403189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3403189).length < 2 ^ (prefixWord ++ tailWord_3403189).sum := by decide
  have hdescent : baseEnd_3403189 < baseStart_3403189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3403189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3403196 : List Nat := [2, 2, 2, 4, 2, 2, 1, 2, 2, 1, 3]
def baseStart_3403196 : Nat := 118140960795 + 3403196 * 2 ^ 59
def prefixEnd_3403196 : Nat := 4983230072969 + 3 ^ 40 * 3403196 * 2
def baseEnd_3403196 : Nat := 1747475309458572213698993

theorem tailTrace_3403196 : CollatzResearch.WordTrace tailWord_3403196 prefixEnd_3403196 1747475309458572213698993 := by
  unfold tailWord_3403196
  simp only [CollatzResearch.WordTrace]
  refine ⟨62062377689404793224326721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82749836919206390965768961 62062377689404793224326721)
  ·
    refine ⟨46546783267053594918245041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62062377689404793224326721 46546783267053594918245041)
    ·
      refine ⟨34910087450290196188683781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46546783267053594918245041 34910087450290196188683781)
      ·
        refine ⟨6545641396929411785378209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34910087450290196188683781 6545641396929411785378209)
        ·
          refine ⟨4909231047697058839033657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6545641396929411785378209 4909231047697058839033657)
          ·
            refine ⟨3681923285772794129275243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4909231047697058839033657 3681923285772794129275243)
            ·
              refine ⟨5522884928659191193912865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3681923285772794129275243 5522884928659191193912865)
              ·
                refine ⟨4142163696494393395434649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5522884928659191193912865 4142163696494393395434649)
                ·
                  refine ⟨3106622772370795046575987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4142163696494393395434649 3106622772370795046575987)
                  ·
                    refine ⟨4659934158556192569863981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3106622772370795046575987 4659934158556192569863981)
                    ·
                      refine ⟨1747475309458572213698993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4659934158556192569863981 1747475309458572213698993)
                      ·
                        rfl

theorem cell23_3403196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_3403196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3403196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3403196 prefixEnd_3403196 := by exact prefixLift 3403196
  have htrace : WordTrace (prefixWord ++ tailWord_3403196) baseStart_3403196 baseEnd_3403196 := by
    simpa [prefixWord, tailWord_3403196, baseEnd_3403196] using wordTrace_append hprefix tailTrace_3403196
  have hstable : (prefixWord ++ tailWord_3403196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3403196).length < 2 ^ (prefixWord ++ tailWord_3403196).sum := by decide
  have hdescent : baseEnd_3403196 < baseStart_3403196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3403196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3403292 : List Nat := [2, 2, 3, 1, 2, 1, 4, 1, 2, 1, 4]
def baseStart_3403292 : Nat := 118140960795 + 3403292 * 2 ^ 59
def prefixEnd_3403292 : Nat := 4983230072969 + 3 ^ 40 * 3403292 * 2
def baseEnd_3403292 : Nat := 1747524603601403838098551

theorem tailTrace_3403292 : CollatzResearch.WordTrace tailWord_3403292 prefixEnd_3403292 1747524603601403838098551 := by
  unfold tailWord_3403292
  simp only [CollatzResearch.WordTrace]
  refine ⟨62064128393230897422074065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82752171190974529896098753 62064128393230897422074065)
  ·
    refine ⟨46548096294923173066555549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62064128393230897422074065 46548096294923173066555549)
    ·
      refine ⟨17455536110596189899958331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46548096294923173066555549 17455536110596189899958331)
      ·
        refine ⟨26183304165894284849937497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17455536110596189899958331 26183304165894284849937497)
        ·
          refine ⟨19637478124420713637453123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26183304165894284849937497 19637478124420713637453123)
          ·
            refine ⟨29456217186631070456179685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19637478124420713637453123 29456217186631070456179685)
            ·
              refine ⟨5523040722493325710533691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29456217186631070456179685 5523040722493325710533691)
              ·
                refine ⟨8284561083739988565800537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5523040722493325710533691 8284561083739988565800537)
                ·
                  refine ⟨6213420812804991424350403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8284561083739988565800537 6213420812804991424350403)
                  ·
                    refine ⟨9320131219207487136525605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6213420812804991424350403 9320131219207487136525605)
                    ·
                      refine ⟨1747524603601403838098551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9320131219207487136525605 1747524603601403838098551)
                      ·
                        rfl

theorem cell23_3403292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 1, 2, 1, 4].length) (baseStart_3403292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3403292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3403292 prefixEnd_3403292 := by exact prefixLift 3403292
  have htrace : WordTrace (prefixWord ++ tailWord_3403292) baseStart_3403292 baseEnd_3403292 := by
    simpa [prefixWord, tailWord_3403292, baseEnd_3403292] using wordTrace_append hprefix tailTrace_3403292
  have hstable : (prefixWord ++ tailWord_3403292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3403292).length < 2 ^ (prefixWord ++ tailWord_3403292).sum := by decide
  have hdescent : baseEnd_3403292 < baseStart_3403292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3403292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3403295 : List Nat := [1, 1, 2, 4, 1, 1, 2, 3, 1, 4, 3]
def baseStart_3403295 : Nat := 118140960795 + 3403295 * 2 ^ 59
def prefixEnd_3403295 : Nat := 4983230072969 + 3 ^ 40 * 3403295 * 2
def baseEnd_3403295 : Nat := 1747526144043367326361037

theorem tailTrace_3403295 : CollatzResearch.WordTrace tailWord_3403295 prefixEnd_3403295 1747526144043367326361037 := by
  unfold tailWord_3403295
  simp only [CollatzResearch.WordTrace]
  refine ⟨124128366205450926356507339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82752244136967284237671559 124128366205450926356507339)
  ·
    refine ⟨186192549308176389534761009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124128366205450926356507339 186192549308176389534761009)
    ·
      refine ⟨139644411981132292151070757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186192549308176389534761009 139644411981132292151070757)
      ·
        refine ⟨26183327246462304778325767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139644411981132292151070757 26183327246462304778325767)
        ·
          refine ⟨39274990869693457167488651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26183327246462304778325767 39274990869693457167488651)
          ·
            refine ⟨58912486304540185751232977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39274990869693457167488651 58912486304540185751232977)
            ·
              refine ⟨44184364728405139313424733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58912486304540185751232977 44184364728405139313424733)
              ·
                refine ⟨16569136773151927242534275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44184364728405139313424733 16569136773151927242534275)
                ·
                  refine ⟨24853705159727890863801413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16569136773151927242534275 24853705159727890863801413)
                  ·
                    refine ⟨4660069717448979536962765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24853705159727890863801413 4660069717448979536962765)
                    ·
                      refine ⟨1747526144043367326361037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4660069717448979536962765 1747526144043367326361037)
                      ·
                        rfl

theorem cell23_3403295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 3, 1, 4, 3].length) (baseStart_3403295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3403295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3403295 prefixEnd_3403295 := by exact prefixLift 3403295
  have htrace : WordTrace (prefixWord ++ tailWord_3403295) baseStart_3403295 baseEnd_3403295 := by
    simpa [prefixWord, tailWord_3403295, baseEnd_3403295] using wordTrace_append hprefix tailTrace_3403295
  have hstable : (prefixWord ++ tailWord_3403295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3403295).length < 2 ^ (prefixWord ++ tailWord_3403295).sum := by decide
  have hdescent : baseEnd_3403295 < baseStart_3403295 := by decide
  rcases family_descends (prefixWord ++ tailWord_3403295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3403315 : List Nat := [1, 1, 1, 2, 4, 3, 1, 4, 6]
def baseStart_3403315 : Nat := 118140960795 + 3403315 * 2 ^ 59
def prefixEnd_3403315 : Nat := 4983230072969 + 3 ^ 40 * 3403315 * 2
def baseEnd_3403315 : Nat := 194170712628495249790105

theorem tailTrace_3403315 : CollatzResearch.WordTrace tailWord_3403315 prefixEnd_3403315 194170712628495249790105 := by
  unfold tailWord_3403315
  simp only [CollatzResearch.WordTrace]
  refine ⟨124129095665378469772235399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82752730443585646514823599 124129095665378469772235399)
  ·
    refine ⟨186193643498067704658353099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124129095665378469772235399 186193643498067704658353099)
    ·
      refine ⟨279290465247101556987529649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186193643498067704658353099 279290465247101556987529649)
      ·
        refine ⟨209467848935326167740647237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279290465247101556987529649 209467848935326167740647237)
        ·
          refine ⟨39275221675373656451371357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 209467848935326167740647237 39275221675373656451371357)
          ·
            refine ⟨14728208128265121169264259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39275221675373656451371357 14728208128265121169264259)
            ·
              refine ⟨22092312192397681753896389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14728208128265121169264259 22092312192397681753896389)
              ·
                refine ⟨4142308536074565328855573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22092312192397681753896389 4142308536074565328855573)
                ·
                  refine ⟨194170712628495249790105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4142308536074565328855573 194170712628495249790105)
                  ·
                    rfl

theorem cell23_3403315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 4, 6].length) (baseStart_3403315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3403315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3403315 prefixEnd_3403315 := by exact prefixLift 3403315
  have htrace : WordTrace (prefixWord ++ tailWord_3403315) baseStart_3403315 baseEnd_3403315 := by
    simpa [prefixWord, tailWord_3403315, baseEnd_3403315] using wordTrace_append hprefix tailTrace_3403315
  have hstable : (prefixWord ++ tailWord_3403315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3403315).length < 2 ^ (prefixWord ++ tailWord_3403315).sum := by decide
  have hdescent : baseEnd_3403315 < baseStart_3403315 := by decide
  rcases family_descends (prefixWord ++ tailWord_3403315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3403319 : List Nat := [1, 1, 3, 1, 2, 5, 1, 4, 1, 4]
def baseStart_3403319 : Nat := 118140960795 + 3403319 * 2 ^ 59
def prefixEnd_3403319 : Nat := 4983230072969 + 3 ^ 40 * 3403319 * 2
def baseEnd_3403319 : Nat := 582512822526358410820309

theorem tailTrace_3403319 : CollatzResearch.WordTrace tailWord_3403319 prefixEnd_3403319 582512822526358410820309 := by
  unfold tailWord_3403319
  simp only [CollatzResearch.WordTrace]
  refine ⟨124129241557363978455381011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82752827704909318970254007 124129241557363978455381011)
  ·
    refine ⟨186193862336045967683071517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124129241557363978455381011 186193862336045967683071517)
    ·
      refine ⟨69822698376017237881151819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186193862336045967683071517 69822698376017237881151819)
      ·
        refine ⟨104734047564025856821727729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69822698376017237881151819 104734047564025856821727729)
        ·
          refine ⟨78550535673019392616295797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104734047564025856821727729 78550535673019392616295797)
          ·
            refine ⟨7364112719345568057777731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 78550535673019392616295797 7364112719345568057777731)
            ·
              refine ⟨11046169079018352086666597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7364112719345568057777731 11046169079018352086666597)
              ·
                refine ⟨2071156702315941016249987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11046169079018352086666597 2071156702315941016249987)
                ·
                  refine ⟨3106735053473911524374981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2071156702315941016249987 3106735053473911524374981)
                  ·
                    refine ⟨582512822526358410820309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3106735053473911524374981 582512822526358410820309)
                    ·
                      rfl

theorem cell23_3403319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 4, 1, 4].length) (baseStart_3403319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3403319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3403319 prefixEnd_3403319 := by exact prefixLift 3403319
  have htrace : WordTrace (prefixWord ++ tailWord_3403319) baseStart_3403319 baseEnd_3403319 := by
    simpa [prefixWord, tailWord_3403319, baseEnd_3403319] using wordTrace_append hprefix tailTrace_3403319
  have hstable : (prefixWord ++ tailWord_3403319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3403319).length < 2 ^ (prefixWord ++ tailWord_3403319).sum := by decide
  have hdescent : baseEnd_3403319 < baseStart_3403319 := by decide
  rcases family_descends (prefixWord ++ tailWord_3403319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3403345 : List Nat := [1, 2, 2, 1, 3, 2, 1, 3, 3, 5]
def baseStart_3403345 : Nat := 118140960795 + 3403345 * 2 ^ 59
def prefixEnd_3403345 : Nat := 4983230072969 + 3 ^ 40 * 3403345 * 2
def baseEnd_3403345 : Nat := 582517272692030710245269

theorem tailTrace_3403345 : CollatzResearch.WordTrace tailWord_3403345 prefixEnd_3403345 582517272692030710245269 := by
  unfold tailWord_3403345
  simp only [CollatzResearch.WordTrace]
  refine ⟨124130189855269784895827489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82753459903513189930551659 124130189855269784895827489)
  ·
    refine ⟨93097642391452338671870617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124130189855269784895827489 93097642391452338671870617)
    ·
      refine ⟨69823231793589254003902963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93097642391452338671870617 69823231793589254003902963)
      ·
        refine ⟨104734847690383881005854445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69823231793589254003902963 104734847690383881005854445)
        ·
          refine ⟨39275567883893955377195417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104734847690383881005854445 39275567883893955377195417)
          ·
            refine ⟨29456675912920466532896563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39275567883893955377195417 29456675912920466532896563)
            ·
              refine ⟨44185013869380699799344845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29456675912920466532896563 44185013869380699799344845)
              ·
                refine ⟨16569380201017762424754317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44185013869380699799344845 16569380201017762424754317)
                ·
                  refine ⟨6213517575381660909282869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16569380201017762424754317 6213517575381660909282869)
                  ·
                    refine ⟨582517272692030710245269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6213517575381660909282869 582517272692030710245269)
                    ·
                      rfl

theorem cell23_3403345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 3, 3, 5].length) (baseStart_3403345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3403345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3403345 prefixEnd_3403345 := by exact prefixLift 3403345
  have htrace : WordTrace (prefixWord ++ tailWord_3403345) baseStart_3403345 baseEnd_3403345 := by
    simpa [prefixWord, tailWord_3403345, baseEnd_3403345] using wordTrace_append hprefix tailTrace_3403345
  have hstable : (prefixWord ++ tailWord_3403345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3403345).length < 2 ^ (prefixWord ++ tailWord_3403345).sum := by decide
  have hdescent : baseEnd_3403345 < baseStart_3403345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3403345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3403376 : List Nat := [2, 1, 1, 1, 6, 1, 2, 4, 1, 1, 3]
def baseStart_3403376 : Nat := 118140960795 + 3403376 * 2 ^ 59
def prefixEnd_3403376 : Nat := 4983230072969 + 3 ^ 40 * 3403376 * 2
def baseEnd_3403376 : Nat := 1747567735976381509448165

theorem tailTrace_3403376 : CollatzResearch.WordTrace tailWord_3403376 prefixEnd_3403376 1747567735976381509448165 := by
  unfold tailWord_3403376
  simp only [CollatzResearch.WordTrace]
  refine ⟨62065660259078738595102991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82754213678771651460137321 62065660259078738595102991)
  ·
    refine ⟨93098490388618107892654487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62065660259078738595102991 93098490388618107892654487)
    ·
      refine ⟨139647735582927161838981731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93098490388618107892654487 139647735582927161838981731)
      ·
        refine ⟨209471603374390742758472597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139647735582927161838981731 209471603374390742758472597)
        ·
          refine ⟨9818981408174566066803403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 209471603374390742758472597 9818981408174566066803403)
          ·
            refine ⟨14728472112261849100205105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9818981408174566066803403 14728472112261849100205105)
            ·
              refine ⟨11046354084196386825153829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14728472112261849100205105 11046354084196386825153829)
              ·
                refine ⟨2071191390786822529716343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11046354084196386825153829 2071191390786822529716343)
                ·
                  refine ⟨3106787086180233794574515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2071191390786822529716343 3106787086180233794574515)
                  ·
                    refine ⟨4660180629270350691861773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3106787086180233794574515 4660180629270350691861773)
                    ·
                      refine ⟨1747567735976381509448165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4660180629270350691861773 1747567735976381509448165)
                      ·
                        rfl

theorem cell23_3403376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 4, 1, 1, 3].length) (baseStart_3403376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3403376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3403376 prefixEnd_3403376 := by exact prefixLift 3403376
  have htrace : WordTrace (prefixWord ++ tailWord_3403376) baseStart_3403376 baseEnd_3403376 := by
    simpa [prefixWord, tailWord_3403376, baseEnd_3403376] using wordTrace_append hprefix tailTrace_3403376
  have hstable : (prefixWord ++ tailWord_3403376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3403376).length < 2 ^ (prefixWord ++ tailWord_3403376).sum := by decide
  have hdescent : baseEnd_3403376 < baseStart_3403376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3403376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3403399 : List Nat := [1, 1, 4, 2, 1, 4, 2, 2, 1, 1, 4]
def baseStart_3403399 : Nat := 118140960795 + 3403399 * 2 ^ 59
def prefixEnd_3403399 : Nat := 4983230072969 + 3 ^ 40 * 3403399 * 2
def baseEnd_3403399 : Nat := 1747579546031434919460559

theorem tailTrace_3403399 : CollatzResearch.WordTrace tailWord_3403399 prefixEnd_3403399 1747579546031434919460559 := by
  unfold tailWord_3403399
  simp only [CollatzResearch.WordTrace]
  refine ⟨124132159397074152118293251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82754772931382768078862167 124132159397074152118293251)
  ·
    refine ⟨186198239095611228177439877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124132159397074152118293251 186198239095611228177439877)
    ·
      refine ⟨34912169830427105283269977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 186198239095611228177439877 34912169830427105283269977)
      ·
        refine ⟨26184127372820328962452483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34912169830427105283269977 26184127372820328962452483)
        ·
          refine ⟨39276191059230493443678725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26184127372820328962452483 39276191059230493443678725)
          ·
            refine ⟨7364285823605717520689761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39276191059230493443678725 7364285823605717520689761)
            ·
              refine ⟨5523214367704288140517321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7364285823605717520689761 5523214367704288140517321)
              ·
                refine ⟨4142410775778216105387991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5523214367704288140517321 4142410775778216105387991)
                ·
                  refine ⟨6213616163667324158081987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4142410775778216105387991 6213616163667324158081987)
                  ·
                    refine ⟨9320424245500986237122981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6213616163667324158081987 9320424245500986237122981)
                    ·
                      refine ⟨1747579546031434919460559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9320424245500986237122981 1747579546031434919460559)
                      ·
                        rfl

theorem cell23_3403399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 2, 1, 1, 4].length) (baseStart_3403399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3403399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3403399 prefixEnd_3403399 := by exact prefixLift 3403399
  have htrace : WordTrace (prefixWord ++ tailWord_3403399) baseStart_3403399 baseEnd_3403399 := by
    simpa [prefixWord, tailWord_3403399, baseEnd_3403399] using wordTrace_append hprefix tailTrace_3403399
  have hstable : (prefixWord ++ tailWord_3403399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3403399).length < 2 ^ (prefixWord ++ tailWord_3403399).sum := by decide
  have hdescent : baseEnd_3403399 < baseStart_3403399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3403399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3403410 : List Nat := [3, 2, 3, 1, 3, 2, 1, 3, 1, 1, 3]
def baseStart_3403410 : Nat := 118140960795 + 3403410 * 2 ^ 59
def prefixEnd_3403410 : Nat := 4983230072969 + 3 ^ 40 * 3403410 * 2
def baseEnd_3403410 : Nat := 1747585194318634376423009

theorem tailTrace_3403410 : CollatzResearch.WordTrace tailWord_3403410 prefixEnd_3403410 1747585194318634376423009 := by
  unfold tailWord_3403410
  simp only [CollatzResearch.WordTrace]
  refine ⟨31033140150008575249235921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82755040400022867331295789 31033140150008575249235921)
  ·
    refine ⟨23274855112506431436926941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31033140150008575249235921 23274855112506431436926941)
    ·
      refine ⟨8728070667189911788847603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23274855112506431436926941 8728070667189911788847603)
      ·
        refine ⟨13092106000784867683271405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8728070667189911788847603 13092106000784867683271405)
        ·
          refine ⟨4909539750294325381226777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13092106000784867683271405 4909539750294325381226777)
          ·
            refine ⟨3682154812720744035920083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4909539750294325381226777 3682154812720744035920083)
            ·
              refine ⟨5523232219081116053880125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3682154812720744035920083 5523232219081116053880125)
              ·
                refine ⟨2071212082155418520205047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5523232219081116053880125 2071212082155418520205047)
                ·
                  refine ⟨3106818123233127780307571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2071212082155418520205047 3106818123233127780307571)
                  ·
                    refine ⟨4660227184849691670461357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3106818123233127780307571 4660227184849691670461357)
                    ·
                      refine ⟨1747585194318634376423009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4660227184849691670461357 1747585194318634376423009)
                      ·
                        rfl

theorem cell23_3403410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 3, 1, 1, 3].length) (baseStart_3403410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3403410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3403410 prefixEnd_3403410 := by exact prefixLift 3403410
  have htrace : WordTrace (prefixWord ++ tailWord_3403410) baseStart_3403410 baseEnd_3403410 := by
    simpa [prefixWord, tailWord_3403410, baseEnd_3403410] using wordTrace_append hprefix tailTrace_3403410
  have hstable : (prefixWord ++ tailWord_3403410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3403410).length < 2 ^ (prefixWord ++ tailWord_3403410).sum := by decide
  have hdescent : baseEnd_3403410 < baseStart_3403410 := by decide
  rcases family_descends (prefixWord ++ tailWord_3403410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3403422 : List Nat := [4, 3, 1, 1, 1, 2, 11]
def baseStart_3403422 : Nat := 118140960795 + 3403422 * 2 ^ 59
def prefixEnd_3403422 : Nat := 4983230072969 + 3 ^ 40 * 3403422 * 2
def baseEnd_3403422 : Nat := 21575201926993683079913

theorem tailTrace_3403422 : CollatzResearch.WordTrace tailWord_3403422 prefixEnd_3403422 21575201926993683079913 := by
  unfold tailWord_3403422
  simp only [CollatzResearch.WordTrace]
  refine ⟨15516624784498853380797565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82755332183993884697587013 15516624784498853380797565)
  ·
    refine ⟨5818734294187070017799087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15516624784498853380797565 5818734294187070017799087)
    ·
      refine ⟨8728101441280605026698631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5818734294187070017799087 8728101441280605026698631)
      ·
        refine ⟨13092152161920907540047947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8728101441280605026698631 13092152161920907540047947)
        ·
          refine ⟨19638228242881361310071921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13092152161920907540047947 19638228242881361310071921)
          ·
            refine ⟨14728671182161020982553941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19638228242881361310071921 14728671182161020982553941)
            ·
              refine ⟨21575201926993683079913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 14728671182161020982553941 21575201926993683079913)
              ·
                rfl

theorem cell23_3403422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 11].length) (baseStart_3403422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3403422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3403422 prefixEnd_3403422 := by exact prefixLift 3403422
  have htrace : WordTrace (prefixWord ++ tailWord_3403422) baseStart_3403422 baseEnd_3403422 := by
    simpa [prefixWord, tailWord_3403422, baseEnd_3403422] using wordTrace_append hprefix tailTrace_3403422
  have hstable : (prefixWord ++ tailWord_3403422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3403422).length < 2 ^ (prefixWord ++ tailWord_3403422).sum := by decide
  have hdescent : baseEnd_3403422 < baseStart_3403422 := by decide
  rcases family_descends (prefixWord ++ tailWord_3403422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3403475 : List Nat := [1, 1, 1, 2, 1, 1, 1, 2, 5, 3, 5]
def baseStart_3403475 : Nat := 118140960795 + 3403475 * 2 ^ 59
def prefixEnd_3403475 : Nat := 4983230072969 + 3 ^ 40 * 3403475 * 2
def baseEnd_3403475 : Nat := 1747618570561176622110209

theorem tailTrace_3403475 : CollatzResearch.WordTrace tailWord_3403475 prefixEnd_3403475 1747618570561176622110209 := by
  unfold tailWord_3403475
  simp only [CollatzResearch.WordTrace]
  refine ⟨124134931344798817098059879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82756620896532544732039919 124134931344798817098059879)
  ·
    refine ⟨186202397017198225647089819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124134931344798817098059879 186202397017198225647089819)
    ·
      refine ⟨279303595525797338470634729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186202397017198225647089819 279303595525797338470634729)
      ·
        refine ⟨209477696644348003852976047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279303595525797338470634729 209477696644348003852976047)
        ·
          refine ⟨314216544966522005779464071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209477696644348003852976047 314216544966522005779464071)
          ·
            refine ⟨471324817449783008669196107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314216544966522005779464071 471324817449783008669196107)
            ·
              refine ⟨706987226174674513003794161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 471324817449783008669196107 706987226174674513003794161)
              ·
                refine ⟨530240419631005884752845621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 706987226174674513003794161 530240419631005884752845621)
                ·
                  refine ⟨49710039340406801695579277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 530240419631005884752845621 49710039340406801695579277)
                  ·
                    refine ⟨18641264752652550635842229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49710039340406801695579277 18641264752652550635842229)
                    ·
                      refine ⟨1747618570561176622110209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18641264752652550635842229 1747618570561176622110209)
                      ·
                        rfl

theorem cell23_3403475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 3, 5].length) (baseStart_3403475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3403475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3403475 prefixEnd_3403475 := by exact prefixLift 3403475
  have htrace : WordTrace (prefixWord ++ tailWord_3403475) baseStart_3403475 baseEnd_3403475 := by
    simpa [prefixWord, tailWord_3403475, baseEnd_3403475] using wordTrace_append hprefix tailTrace_3403475
  have hstable : (prefixWord ++ tailWord_3403475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3403475).length < 2 ^ (prefixWord ++ tailWord_3403475).sum := by decide
  have hdescent : baseEnd_3403475 < baseStart_3403475 := by decide
  rcases family_descends (prefixWord ++ tailWord_3403475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3403484 : List Nat := [2, 2, 5, 1, 2, 2, 2, 2, 1, 2, 2]
def baseStart_3403484 : Nat := 118140960795 + 3403484 * 2 ^ 59
def prefixEnd_3403484 : Nat := 4983230072969 + 3 ^ 40 * 3403484 * 2
def baseEnd_3403484 : Nat := 1747623191887067086897669

theorem tailTrace_3403484 : CollatzResearch.WordTrace tailWord_3403484 prefixEnd_3403484 1747623191887067086897669 := by
  unfold tailWord_3403484
  simp only [CollatzResearch.WordTrace]
  refine ⟨62067629800883105817568753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82756839734510807756758337 62067629800883105817568753)
  ·
    refine ⟨46550722350662329363176565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62067629800883105817568753 46550722350662329363176565)
    ·
      refine ⟨4364130220374593377797803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46550722350662329363176565 4364130220374593377797803)
      ·
        refine ⟨6546195330561890066696705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4364130220374593377797803 6546195330561890066696705)
        ·
          refine ⟨4909646497921417550022529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6546195330561890066696705 4909646497921417550022529)
          ·
            refine ⟨3682234873441063162516897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4909646497921417550022529 3682234873441063162516897)
            ·
              refine ⟨2761676155080797371887673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3682234873441063162516897 2761676155080797371887673)
              ·
                refine ⟨2071257116310598028915755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2761676155080797371887673 2071257116310598028915755)
                ·
                  refine ⟨3106885674465897043373633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2071257116310598028915755 3106885674465897043373633)
                  ·
                    refine ⟨2330164255849422782530225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3106885674465897043373633 2330164255849422782530225)
                    ·
                      refine ⟨1747623191887067086897669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2330164255849422782530225 1747623191887067086897669)
                      ·
                        rfl

theorem cell23_3403484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_3403484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3403484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3403484 prefixEnd_3403484 := by exact prefixLift 3403484
  have htrace : WordTrace (prefixWord ++ tailWord_3403484) baseStart_3403484 baseEnd_3403484 := by
    simpa [prefixWord, tailWord_3403484, baseEnd_3403484] using wordTrace_append hprefix tailTrace_3403484
  have hstable : (prefixWord ++ tailWord_3403484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3403484).length < 2 ^ (prefixWord ++ tailWord_3403484).sum := by decide
  have hdescent : baseEnd_3403484 < baseStart_3403484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3403484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3403492 : List Nat := [2, 3, 1, 1, 1, 3, 1, 1, 1, 6, 3]
def baseStart_3403492 : Nat := 118140960795 + 3403492 * 2 ^ 59
def prefixEnd_3403492 : Nat := 4983230072969 + 3 ^ 40 * 3403492 * 2
def baseEnd_3403492 : Nat := 1747627299732303055597631

theorem tailTrace_3403492 : CollatzResearch.WordTrace tailWord_3403492 prefixEnd_3403492 1747627299732303055597631 := by
  unfold tailWord_3403492
  simp only [CollatzResearch.WordTrace]
  refine ⟨62067775692868614500714365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82757034257158152667619153 62067775692868614500714365)
  ·
    refine ⟨23275415884825730437767887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62067775692868614500714365 23275415884825730437767887)
    ·
      refine ⟨34913123827238595656651831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23275415884825730437767887 34913123827238595656651831)
      ·
        refine ⟨52369685740857893484977747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34913123827238595656651831 52369685740857893484977747)
        ·
          refine ⟨78554528611286840227466621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52369685740857893484977747 78554528611286840227466621)
          ·
            refine ⟨29457948229232565085299983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78554528611286840227466621 29457948229232565085299983)
            ·
              refine ⟨44186922343848847627949975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29457948229232565085299983 44186922343848847627949975)
              ·
                refine ⟨66280383515773271441924963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44186922343848847627949975 66280383515773271441924963)
                ·
                  refine ⟨99420575273659907162887445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66280383515773271441924963 99420575273659907162887445)
                  ·
                    refine ⟨4660339465952808148260349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 99420575273659907162887445 4660339465952808148260349)
                    ·
                      refine ⟨1747627299732303055597631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4660339465952808148260349 1747627299732303055597631)
                      ·
                        rfl

theorem cell23_3403492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 1, 6, 3].length) (baseStart_3403492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3403492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3403492 prefixEnd_3403492 := by exact prefixLift 3403492
  have htrace : WordTrace (prefixWord ++ tailWord_3403492) baseStart_3403492 baseEnd_3403492 := by
    simpa [prefixWord, tailWord_3403492, baseEnd_3403492] using wordTrace_append hprefix tailTrace_3403492
  have hstable : (prefixWord ++ tailWord_3403492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3403492).length < 2 ^ (prefixWord ++ tailWord_3403492).sum := by decide
  have hdescent : baseEnd_3403492 < baseStart_3403492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3403492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3403506 : List Nat := [3, 2, 1, 3, 1, 1, 4, 1, 1, 4, 2]
def baseStart_3403506 : Nat := 118140960795 + 3403506 * 2 ^ 59
def prefixEnd_3403506 : Nat := 4983230072969 + 3 ^ 40 * 3403506 * 2
def baseEnd_3403506 : Nat := 1747634488461466000822567

theorem tailTrace_3403506 : CollatzResearch.WordTrace tailWord_3403506 prefixEnd_3403506 1747634488461466000822567 := by
  unfold tailWord_3403506
  simp only [CollatzResearch.WordTrace]
  refine ⟨31034015501921627348109593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82757374671791006261625581 31034015501921627348109593)
  ·
    refine ⟨23275511626441220511082195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31034015501921627348109593 23275511626441220511082195)
    ·
      refine ⟨34913267439661830766623293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23275511626441220511082195 34913267439661830766623293)
      ·
        refine ⟨13092475289873186537483735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34913267439661830766623293 13092475289873186537483735)
        ·
          refine ⟨19638712934809779806225603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13092475289873186537483735 19638712934809779806225603)
          ·
            refine ⟨29458069402214669709338405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19638712934809779806225603 29458069402214669709338405)
            ·
              refine ⟨5523388012915250570500951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29458069402214669709338405 5523388012915250570500951)
              ·
                refine ⟨8285082019372875855751427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5523388012915250570500951 8285082019372875855751427)
                ·
                  refine ⟨12427623029059313783627141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8285082019372875855751427 12427623029059313783627141)
                  ·
                    refine ⟨2330179317948621334430089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12427623029059313783627141 2330179317948621334430089)
                    ·
                      refine ⟨1747634488461466000822567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2330179317948621334430089 1747634488461466000822567)
                      ·
                        rfl

theorem cell23_3403506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 1, 1, 4, 2].length) (baseStart_3403506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3403506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3403506 prefixEnd_3403506 := by exact prefixLift 3403506
  have htrace : WordTrace (prefixWord ++ tailWord_3403506) baseStart_3403506 baseEnd_3403506 := by
    simpa [prefixWord, tailWord_3403506, baseEnd_3403506] using wordTrace_append hprefix tailTrace_3403506
  have hstable : (prefixWord ++ tailWord_3403506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3403506).length < 2 ^ (prefixWord ++ tailWord_3403506).sum := by decide
  have hdescent : baseEnd_3403506 < baseStart_3403506 := by decide
  rcases family_descends (prefixWord ++ tailWord_3403506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3403527 : List Nat := [1, 1, 4, 4, 3, 1, 2, 1, 1, 3, 2]
def baseStart_3403527 : Nat := 118140960795 + 3403527 * 2 ^ 59
def prefixEnd_3403527 : Nat := 4983230072969 + 3 ^ 40 * 3403527 * 2
def baseEnd_3403527 : Nat := 1747645271555210418659971

theorem tailTrace_3403527 : CollatzResearch.WordTrace tailWord_3403527 prefixEnd_3403527 1747645271555210418659971 := by
  unfold tailWord_3403527
  simp only [CollatzResearch.WordTrace]
  refine ⟨124136827940610429978952835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82757885293740286652635223 124136827940610429978952835)
  ·
    refine ⟨186205241910915644968429253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124136827940610429978952835 186205241910915644968429253)
    ·
      refine ⟨34913482858296683431580485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 186205241910915644968429253 34913482858296683431580485)
      ·
        refine ⟨6546278035930628143421341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34913482858296683431580485 6546278035930628143421341)
        ·
          refine ⟨2454854263473985553783003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6546278035930628143421341 2454854263473985553783003)
          ·
            refine ⟨3682281395210978330674505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2454854263473985553783003 3682281395210978330674505)
            ·
              refine ⟨2761711046408233748005879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3682281395210978330674505 2761711046408233748005879)
              ·
                refine ⟨4142566569612350622008819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2761711046408233748005879 4142566569612350622008819)
                ·
                  refine ⟨6213849854418525933013229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4142566569612350622008819 6213849854418525933013229)
                  ·
                    refine ⟨2330193695406947224879961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6213849854418525933013229 2330193695406947224879961)
                    ·
                      refine ⟨1747645271555210418659971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2330193695406947224879961 1747645271555210418659971)
                      ·
                        rfl

theorem cell23_3403527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_3403527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3403527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3403527 prefixEnd_3403527 := by exact prefixLift 3403527
  have htrace : WordTrace (prefixWord ++ tailWord_3403527) baseStart_3403527 baseEnd_3403527 := by
    simpa [prefixWord, tailWord_3403527, baseEnd_3403527] using wordTrace_append hprefix tailTrace_3403527
  have hstable : (prefixWord ++ tailWord_3403527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3403527).length < 2 ^ (prefixWord ++ tailWord_3403527).sum := by decide
  have hdescent : baseEnd_3403527 < baseStart_3403527 := by decide
  rcases family_descends (prefixWord ++ tailWord_3403527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3403552 : List Nat := [2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 7]
def baseStart_3403552 : Nat := 118140960795 + 3403552 * 2 ^ 59
def prefixEnd_3403552 : Nat := 4983230072969 + 3 ^ 40 * 3403552 * 2
def baseEnd_3403552 : Nat := 1747658108571572820847355

theorem tailTrace_3403552 : CollatzResearch.WordTrace tailWord_3403552 prefixEnd_3403552 1747658108571572820847355 := by
  unfold tailWord_3403552
  simp only [CollatzResearch.WordTrace]
  refine ⟨62068869882759929624306455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82758493177013239499075273 62068869882759929624306455)
  ·
    refine ⟨93103304824139894436459683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62068869882759929624306455 93103304824139894436459683)
    ·
      refine ⟨139654957236209841654689525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93103304824139894436459683 139654957236209841654689525)
      ·
        refine ⟨13092652240894672655127143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 139654957236209841654689525 13092652240894672655127143)
        ·
          refine ⟨19638978361342008982690715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13092652240894672655127143 19638978361342008982690715)
          ·
            refine ⟨29458467542013013474036073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19638978361342008982690715 29458467542013013474036073)
            ·
              refine ⟨22093850656509760105527055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29458467542013013474036073 22093850656509760105527055)
              ·
                refine ⟨33140775984764640158290583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22093850656509760105527055 33140775984764640158290583)
                ·
                  refine ⟨49711163977146960237435875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33140775984764640158290583 49711163977146960237435875)
                  ·
                    refine ⟨74566745965720440356153813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49711163977146960237435875 74566745965720440356153813)
                    ·
                      refine ⟨1747658108571572820847355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 74566745965720440356153813 1747658108571572820847355)
                      ·
                        rfl

theorem cell23_3403552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_3403552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3403552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3403552 prefixEnd_3403552 := by exact prefixLift 3403552
  have htrace : WordTrace (prefixWord ++ tailWord_3403552) baseStart_3403552 baseEnd_3403552 := by
    simpa [prefixWord, tailWord_3403552, baseEnd_3403552] using wordTrace_append hprefix tailTrace_3403552
  have hstable : (prefixWord ++ tailWord_3403552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3403552).length < 2 ^ (prefixWord ++ tailWord_3403552).sum := by decide
  have hdescent : baseEnd_3403552 < baseStart_3403552 := by decide
  rcases family_descends (prefixWord ++ tailWord_3403552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3403596 : List Nat := [2, 2, 1, 3, 4, 1, 1, 2, 2, 1, 4]
def baseStart_3403596 : Nat := 118140960795 + 3403596 * 2 ^ 59
def prefixEnd_3403596 : Nat := 4983230072969 + 3 ^ 40 * 3403596 * 2
def baseEnd_3403596 : Nat := 1747680701720370648697153

theorem tailTrace_3403596 : CollatzResearch.WordTrace tailWord_3403596 prefixEnd_3403596 1747680701720370648697153 := by
  unfold tailWord_3403596
  simp only [CollatzResearch.WordTrace]
  refine ⟨62069672288680227381607321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82759563051573636508809761 62069672288680227381607321)
  ·
    refine ⟨46552254216510170536205491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62069672288680227381607321 46552254216510170536205491)
    ·
      refine ⟨69828381324765255804308237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46552254216510170536205491 69828381324765255804308237)
      ·
        refine ⟨26185642996786970926615589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69828381324765255804308237 26185642996786970926615589)
        ·
          refine ⟨4909808061897557048740423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26185642996786970926615589 4909808061897557048740423)
          ·
            refine ⟨7364712092846335573110635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4909808061897557048740423 7364712092846335573110635)
            ·
              refine ⟨11047068139269503359665953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7364712092846335573110635 11047068139269503359665953)
              ·
                refine ⟨8285301104452127519749465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11047068139269503359665953 8285301104452127519749465)
                ·
                  refine ⟨6213975828339095639812099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8285301104452127519749465 6213975828339095639812099)
                  ·
                    refine ⟨9320963742508643459718149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6213975828339095639812099 9320963742508643459718149)
                    ·
                      refine ⟨1747680701720370648697153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9320963742508643459718149 1747680701720370648697153)
                      ·
                        rfl

theorem cell23_3403596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 2, 2, 1, 4].length) (baseStart_3403596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3403596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3403596 prefixEnd_3403596 := by exact prefixLift 3403596
  have htrace : WordTrace (prefixWord ++ tailWord_3403596) baseStart_3403596 baseEnd_3403596 := by
    simpa [prefixWord, tailWord_3403596, baseEnd_3403596] using wordTrace_append hprefix tailTrace_3403596
  have hstable : (prefixWord ++ tailWord_3403596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3403596).length < 2 ^ (prefixWord ++ tailWord_3403596).sum := by decide
  have hdescent : baseEnd_3403596 < baseStart_3403596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3403596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3403629 : List Nat := [1, 5, 1, 1, 1, 1, 2, 1, 2, 5, 3]
def baseStart_3403629 : Nat := 118140960795 + 3403629 * 2 ^ 59
def prefixEnd_3403629 : Nat := 4983230072969 + 3 ^ 40 * 3403629 * 2
def baseEnd_3403629 : Nat := 1747697646581969019584501

theorem tailTrace_3403629 : CollatzResearch.WordTrace tailWord_3403629 prefixEnd_3403629 1747697646581969019584501 := by
  unfold tailWord_3403629
  simp only [CollatzResearch.WordTrace]
  refine ⟨124140548186240901399165941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82760365457493934266110627 124140548186240901399165941)
  ·
    refine ⟨11638176392460084506171807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 124140548186240901399165941 11638176392460084506171807)
    ·
      refine ⟨17457264588690126759257711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11638176392460084506171807 17457264588690126759257711)
      ·
        refine ⟨26185896883035190138886567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17457264588690126759257711 26185896883035190138886567)
        ·
          refine ⟨39278845324552785208329851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26185896883035190138886567 39278845324552785208329851)
          ·
            refine ⟨58918267986829177812494777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39278845324552785208329851 58918267986829177812494777)
            ·
              refine ⟨44188700990121883359371083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58918267986829177812494777 44188700990121883359371083)
              ·
                refine ⟨66283051485182825039056625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44188700990121883359371083 66283051485182825039056625)
                ·
                  refine ⟨49712288613887118779292469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66283051485182825039056625 49712288613887118779292469)
                  ·
                    refine ⟨4660527057551917385558669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49712288613887118779292469 4660527057551917385558669)
                    ·
                      refine ⟨1747697646581969019584501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4660527057551917385558669 1747697646581969019584501)
                      ·
                        rfl

theorem cell23_3403629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 5, 3].length) (baseStart_3403629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3403629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3403629 prefixEnd_3403629 := by exact prefixLift 3403629
  have htrace : WordTrace (prefixWord ++ tailWord_3403629) baseStart_3403629 baseEnd_3403629 := by
    simpa [prefixWord, tailWord_3403629, baseEnd_3403629] using wordTrace_append hprefix tailTrace_3403629
  have hstable : (prefixWord ++ tailWord_3403629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3403629).length < 2 ^ (prefixWord ++ tailWord_3403629).sum := by decide
  have hdescent : baseEnd_3403629 < baseStart_3403629 := by decide
  rcases family_descends (prefixWord ++ tailWord_3403629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3403666 : List Nat := [3, 2, 3, 2, 1, 1, 1, 2, 3, 5]
def baseStart_3403666 : Nat := 118140960795 + 3403666 * 2 ^ 59
def prefixEnd_3403666 : Nat := 4983230072969 + 3 ^ 40 * 3403666 * 2
def baseEnd_3403666 : Nat := 582572215122061791607277

theorem tailTrace_3403666 : CollatzResearch.WordTrace tailWord_3403666 prefixEnd_3403666 582572215122061791607277 := by
  unfold tailWord_3403666
  simp only [CollatzResearch.WordTrace]
  refine ⟨31035474421776714179565713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82761265124737904478841901 31035474421776714179565713)
  ·
    refine ⟨23276605816332535634674285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31035474421776714179565713 23276605816332535634674285)
    ·
      refine ⟨8728727181124700863002857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23276605816332535634674285 8728727181124700863002857)
      ·
        refine ⟨6546545385843525647252143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8728727181124700863002857 6546545385843525647252143)
        ·
          refine ⟨9819818078765288470878215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6546545385843525647252143 9819818078765288470878215)
          ·
            refine ⟨14729727118147932706317323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9819818078765288470878215 14729727118147932706317323)
            ·
              refine ⟨22094590677221899059475985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14729727118147932706317323 22094590677221899059475985)
              ·
                refine ⟨16570943007916424294606989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22094590677221899059475985 16570943007916424294606989)
                ·
                  refine ⟨6214103627968659110477621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16570943007916424294606989 6214103627968659110477621)
                  ·
                    refine ⟨582572215122061791607277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6214103627968659110477621 582572215122061791607277)
                    ·
                      rfl

theorem cell23_3403666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_3403666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3403666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3403666 prefixEnd_3403666 := by exact prefixLift 3403666
  have htrace : WordTrace (prefixWord ++ tailWord_3403666) baseStart_3403666 baseEnd_3403666 := by
    simpa [prefixWord, tailWord_3403666, baseEnd_3403666] using wordTrace_append hprefix tailTrace_3403666
  have hstable : (prefixWord ++ tailWord_3403666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3403666).length < 2 ^ (prefixWord ++ tailWord_3403666).sum := by decide
  have hdescent : baseEnd_3403666 < baseStart_3403666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3403666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3403669 : List Nat := [1, 3, 2, 1, 1, 3, 1, 1, 5, 1, 4]
def baseStart_3403669 : Nat := 118140960795 + 3403669 * 2 ^ 59
def prefixEnd_3403669 : Nat := 4983230072969 + 3 ^ 40 * 3403669 * 2
def baseEnd_3403669 : Nat := 1747718185808148863084317

theorem tailTrace_3403669 : CollatzResearch.WordTrace tailWord_3403669 prefixEnd_3403669 1747718185808148863084317 := by
  unfold tailWord_3403669
  simp only [CollatzResearch.WordTrace]
  refine ⟨124142007106095988230622061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82761338070730658820414707 124142007106095988230622061)
  ·
    refine ⟨46553252664785995586483273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124142007106095988230622061 46553252664785995586483273)
    ·
      refine ⟨34914939498589496689862455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46553252664785995586483273 34914939498589496689862455)
      ·
        refine ⟨52372409247884245034793683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34914939498589496689862455 52372409247884245034793683)
        ·
          refine ⟨78558613871826367552190525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52372409247884245034793683 78558613871826367552190525)
          ·
            refine ⟨29459480201934887832071447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78558613871826367552190525 29459480201934887832071447)
            ·
              refine ⟨44189220302902331748107171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29459480201934887832071447 44189220302902331748107171)
              ·
                refine ⟨66283830454353497622160757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44189220302902331748107171 66283830454353497622160757)
                ·
                  refine ⟨6214109105095640402077571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66283830454353497622160757 6214109105095640402077571)
                  ·
                    refine ⟨9321163657643460603116357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6214109105095640402077571 9321163657643460603116357)
                    ·
                      refine ⟨1747718185808148863084317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9321163657643460603116357 1747718185808148863084317)
                      ·
                        rfl

theorem cell23_3403669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 5, 1, 4].length) (baseStart_3403669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3403669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3403669 prefixEnd_3403669 := by exact prefixLift 3403669
  have htrace : WordTrace (prefixWord ++ tailWord_3403669) baseStart_3403669 baseEnd_3403669 := by
    simpa [prefixWord, tailWord_3403669, baseEnd_3403669] using wordTrace_append hprefix tailTrace_3403669
  have hstable : (prefixWord ++ tailWord_3403669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3403669).length < 2 ^ (prefixWord ++ tailWord_3403669).sum := by decide
  have hdescent : baseEnd_3403669 < baseStart_3403669 := by decide
  rcases family_descends (prefixWord ++ tailWord_3403669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3403699 : List Nat := [1, 1, 1, 2, 3, 1, 3, 4, 1, 2, 4]
def baseStart_3403699 : Nat := 118140960795 + 3403699 * 2 ^ 59
def prefixEnd_3403699 : Nat := 4983230072969 + 3 ^ 40 * 3403699 * 2
def baseEnd_3403699 : Nat := 1747733590227783745709179

theorem tailTrace_3403699 : CollatzResearch.WordTrace tailWord_3403699 prefixEnd_3403699 1747733590227783745709179 := by
  unfold tailWord_3403699
  simp only [CollatzResearch.WordTrace]
  refine ⟨124143101295987303354214151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82762067530658202236142767 124143101295987303354214151)
  ·
    refine ⟨186214651943980955031321227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124143101295987303354214151 186214651943980955031321227)
    ·
      refine ⟨279321977915971432546981841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186214651943980955031321227 279321977915971432546981841)
      ·
        refine ⟨209491483436978574410236381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279321977915971432546981841 209491483436978574410236381)
        ·
          refine ⟨78559306288866965403838643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 209491483436978574410236381 78559306288866965403838643)
          ·
            refine ⟨117838959433300448105757965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78559306288866965403838643 117838959433300448105757965)
            ·
              refine ⟨44189609787487668039659237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117838959433300448105757965 44189609787487668039659237)
              ·
                refine ⟨8285551835153937757436107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44189609787487668039659237 8285551835153937757436107)
                ·
                  refine ⟨12428327752730906636154161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8285551835153937757436107 12428327752730906636154161)
                  ·
                    refine ⟨9321245814548179977115621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12428327752730906636154161 9321245814548179977115621)
                    ·
                      refine ⟨1747733590227783745709179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9321245814548179977115621 1747733590227783745709179)
                      ·
                        rfl

theorem cell23_3403699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 4, 1, 2, 4].length) (baseStart_3403699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3403699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3403699 prefixEnd_3403699 := by exact prefixLift 3403699
  have htrace : WordTrace (prefixWord ++ tailWord_3403699) baseStart_3403699 baseEnd_3403699 := by
    simpa [prefixWord, tailWord_3403699, baseEnd_3403699] using wordTrace_append hprefix tailTrace_3403699
  have hstable : (prefixWord ++ tailWord_3403699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3403699).length < 2 ^ (prefixWord ++ tailWord_3403699).sum := by decide
  have hdescent : baseEnd_3403699 < baseStart_3403699 := by decide
  rcases family_descends (prefixWord ++ tailWord_3403699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3403700 : List Nat := [2, 5, 2, 1, 2, 1, 1, 3, 1, 5]
def baseStart_3403700 : Nat := 118140960795 + 3403700 * 2 ^ 59
def prefixEnd_3403700 : Nat := 4983230072969 + 3 ^ 40 * 3403700 * 2
def baseEnd_3403700 : Nat := 582578034569479413932225

theorem tailTrace_3403700 : CollatzResearch.WordTrace tailWord_3403700 prefixEnd_3403700 582578034569479413932225 := by
  unfold tailWord_3403700
  simp only [CollatzResearch.WordTrace]
  refine ⟨62071568884491840262500277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82762091845989120350000369 62071568884491840262500277)
  ·
    refine ⟨5819209582921110024609401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62071568884491840262500277 5819209582921110024609401)
    ·
      refine ⟨4364407187190832518457051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5819209582921110024609401 4364407187190832518457051)
      ·
        refine ⟨6546610780786248777685577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4364407187190832518457051 6546610780786248777685577)
        ·
          refine ⟨4909958085589686583264183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6546610780786248777685577 4909958085589686583264183)
          ·
            refine ⟨7364937128384529874896275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4909958085589686583264183 7364937128384529874896275)
            ·
              refine ⟨11047405692576794812344413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7364937128384529874896275 11047405692576794812344413)
              ·
                refine ⟨4142777134716298054629155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11047405692576794812344413 4142777134716298054629155)
                ·
                  refine ⟨6214165702074447081943733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4142777134716298054629155 6214165702074447081943733)
                  ·
                    refine ⟨582578034569479413932225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6214165702074447081943733 582578034569479413932225)
                    ·
                      rfl

theorem cell23_3403700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_3403700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3403700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3403700 prefixEnd_3403700 := by exact prefixLift 3403700
  have htrace : WordTrace (prefixWord ++ tailWord_3403700) baseStart_3403700 baseEnd_3403700 := by
    simpa [prefixWord, tailWord_3403700, baseEnd_3403700] using wordTrace_append hprefix tailTrace_3403700
  have hstable : (prefixWord ++ tailWord_3403700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3403700).length < 2 ^ (prefixWord ++ tailWord_3403700).sum := by decide
  have hdescent : baseEnd_3403700 < baseStart_3403700 := by decide
  rcases family_descends (prefixWord ++ tailWord_3403700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3403709 : List Nat := [1, 4, 1, 2, 3, 2, 10]
def baseStart_3403709 : Nat := 118140960795 + 3403709 * 2 ^ 59
def prefixEnd_3403709 : Nat := 4983230072969 + 3 ^ 40 * 3403709 * 2
def baseEnd_3403709 : Nat := 21577021296720107488693

theorem tailTrace_3403709 : CollatzResearch.WordTrace tailWord_3403709 prefixEnd_3403709 21577021296720107488693 := by
  unfold tailWord_3403709
  simp only [CollatzResearch.WordTrace]
  refine ⟨124143466025951075062078181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82762310683967383374718787 124143466025951075062078181)
  ·
    refine ⟨23276899879865826574139659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124143466025951075062078181 23276899879865826574139659)
    ·
      refine ⟨34915349819798739861209489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23276899879865826574139659 34915349819798739861209489)
      ·
        refine ⟨26186512364849054895907117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34915349819798739861209489 26186512364849054895907117)
        ·
          refine ⟨9819942136818395585965169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26186512364849054895907117 9819942136818395585965169)
          ·
            refine ⟨7364956602613796689473877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9819942136818395585965169 7364956602613796689473877)
            ·
              refine ⟨21577021296720107488693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7364956602613796689473877 21577021296720107488693)
              ·
                rfl

theorem cell23_3403709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 10].length) (baseStart_3403709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3403709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3403709 prefixEnd_3403709 := by exact prefixLift 3403709
  have htrace : WordTrace (prefixWord ++ tailWord_3403709) baseStart_3403709 baseEnd_3403709 := by
    simpa [prefixWord, tailWord_3403709, baseEnd_3403709] using wordTrace_append hprefix tailTrace_3403709
  have hstable : (prefixWord ++ tailWord_3403709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3403709).length < 2 ^ (prefixWord ++ tailWord_3403709).sum := by decide
  have hdescent : baseEnd_3403709 < baseStart_3403709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3403709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3403720 : List Nat := [2, 1, 3, 1, 4, 2, 2, 1, 3, 2, 2]
def baseStart_3403720 : Nat := 118140960795 + 3403720 * 2 ^ 59
def prefixEnd_3403720 : Nat := 4983230072969 + 3 ^ 40 * 3403720 * 2
def baseEnd_3403720 : Nat := 1747744373321528163546583

theorem tailTrace_3403720 : CollatzResearch.WordTrace tailWord_3403720 prefixEnd_3403720 1747744373321528163546583 := by
  unfold tailWord_3403720
  simp only [CollatzResearch.WordTrace]
  refine ⟨62071933614455611970364307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82762578152607482627152409 62071933614455611970364307)
  ·
    refine ⟨93107900421683417955546461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62071933614455611970364307 93107900421683417955546461)
    ·
      refine ⟨34915462658131281733329923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93107900421683417955546461 34915462658131281733329923)
      ·
        refine ⟨52373193987196922599994885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34915462658131281733329923 52373193987196922599994885)
        ·
          refine ⟨9819973872599422987499041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52373193987196922599994885 9819973872599422987499041)
          ·
            refine ⟨7364980404449567240624281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9819973872599422987499041 7364980404449567240624281)
            ·
              refine ⟨5523735303337175430468211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7364980404449567240624281 5523735303337175430468211)
              ·
                refine ⟨8285602955005763145702317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5523735303337175430468211 8285602955005763145702317)
                ·
                  refine ⟨3107101108127161179638369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8285602955005763145702317 3107101108127161179638369)
                  ·
                    refine ⟨2330325831095370884728777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3107101108127161179638369 2330325831095370884728777)
                    ·
                      refine ⟨1747744373321528163546583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2330325831095370884728777 1747744373321528163546583)
                      ·
                        rfl

theorem cell23_3403720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 1, 3, 2, 2].length) (baseStart_3403720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3403720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3403720 prefixEnd_3403720 := by exact prefixLift 3403720
  have htrace : WordTrace (prefixWord ++ tailWord_3403720) baseStart_3403720 baseEnd_3403720 := by
    simpa [prefixWord, tailWord_3403720, baseEnd_3403720] using wordTrace_append hprefix tailTrace_3403720
  have hstable : (prefixWord ++ tailWord_3403720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3403720).length < 2 ^ (prefixWord ++ tailWord_3403720).sum := by decide
  have hdescent : baseEnd_3403720 < baseStart_3403720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3403720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3403730 : List Nat := [3, 2, 2, 3, 3, 1, 1, 1, 1, 6]
def baseStart_3403730 : Nat := 118140960795 + 3403730 * 2 ^ 59
def prefixEnd_3403730 : Nat := 4983230072969 + 3 ^ 40 * 3403730 * 2
def baseEnd_3403730 : Nat := 582583169376024374807179

theorem tailTrace_3403730 : CollatzResearch.WordTrace tailWord_3403730 prefixEnd_3403730 582583169376024374807179 := by
  unfold tailWord_3403730
  simp only [CollatzResearch.WordTrace]
  refine ⟨31036057989718748912148161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82762821305916663765728429 31036057989718748912148161)
  ·
    refine ⟨23277043492289061684111121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31036057989718748912148161 23277043492289061684111121)
    ·
      refine ⟨17457782619216796263083341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23277043492289061684111121 17457782619216796263083341)
      ·
        refine ⟨6546668482206298598656253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17457782619216796263083341 6546668482206298598656253)
        ·
          refine ⟨2455000680827361974496095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6546668482206298598656253 2455000680827361974496095)
          ·
            refine ⟨3682501021241042961744143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2455000680827361974496095 3682501021241042961744143)
            ·
              refine ⟨5523751531861564442616215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3682501021241042961744143 5523751531861564442616215)
              ·
                refine ⟨8285627297792346663924323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5523751531861564442616215 8285627297792346663924323)
                ·
                  refine ⟨12428440946688519995886485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8285627297792346663924323 12428440946688519995886485)
                  ·
                    refine ⟨582583169376024374807179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12428440946688519995886485 582583169376024374807179)
                    ·
                      rfl

theorem cell23_3403730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 1, 1, 6].length) (baseStart_3403730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3403730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3403730 prefixEnd_3403730 := by exact prefixLift 3403730
  have htrace : WordTrace (prefixWord ++ tailWord_3403730) baseStart_3403730 baseEnd_3403730 := by
    simpa [prefixWord, tailWord_3403730, baseEnd_3403730] using wordTrace_append hprefix tailTrace_3403730
  have hstable : (prefixWord ++ tailWord_3403730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3403730).length < 2 ^ (prefixWord ++ tailWord_3403730).sum := by decide
  have hdescent : baseEnd_3403730 < baseStart_3403730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3403730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3403733 : List Nat := [1, 3, 2, 3, 2, 3, 1, 1, 1, 2, 4]
def baseStart_3403733 : Nat := 118140960795 + 3403733 * 2 ^ 59
def prefixEnd_3403733 : Nat := 4983230072969 + 3 ^ 40 * 3403733 * 2
def baseEnd_3403733 : Nat := 1747751048570036612684023

theorem tailTrace_3403733 : CollatzResearch.WordTrace tailWord_3403733 prefixEnd_3403733 1747751048570036612684023 := by
  unfold tailWord_3403733
  simp only [CollatzResearch.WordTrace]
  refine ⟨124144341377864127160951853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82762894251909418107301235 124144341377864127160951853)
  ·
    refine ⟨46554128016699047685356945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124144341377864127160951853 46554128016699047685356945)
    ·
      refine ⟨34915596012524285764017709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46554128016699047685356945 34915596012524285764017709)
      ·
        refine ⟨13093348504696607161506641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34915596012524285764017709 13093348504696607161506641)
        ·
          refine ⟨9820011378522455371129981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13093348504696607161506641 9820011378522455371129981)
          ·
            refine ⟨3682504266945920764173743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9820011378522455371129981 3682504266945920764173743)
            ·
              refine ⟨5523756400418881146260615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3682504266945920764173743 5523756400418881146260615)
              ·
                refine ⟨8285634600628321719390923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5523756400418881146260615 8285634600628321719390923)
                ·
                  refine ⟨12428451900942482579086385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8285634600628321719390923 12428451900942482579086385)
                  ·
                    refine ⟨9321338925706861934314789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12428451900942482579086385 9321338925706861934314789)
                    ·
                      refine ⟨1747751048570036612684023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9321338925706861934314789 1747751048570036612684023)
                      ·
                        rfl

theorem cell23_3403733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_3403733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3403733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3403733 prefixEnd_3403733 := by exact prefixLift 3403733
  have htrace : WordTrace (prefixWord ++ tailWord_3403733) baseStart_3403733 baseEnd_3403733 := by
    simpa [prefixWord, tailWord_3403733, baseEnd_3403733] using wordTrace_append hprefix tailTrace_3403733
  have hstable : (prefixWord ++ tailWord_3403733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3403733).length < 2 ^ (prefixWord ++ tailWord_3403733).sum := by decide
  have hdescent : baseEnd_3403733 < baseStart_3403733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3403733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3403776 : List Nat := [2, 1, 1, 2, 1, 1, 1, 3, 5, 4, 2]
def baseStart_3403776 : Nat := 118140960795 + 3403776 * 2 ^ 59
def prefixEnd_3403776 : Nat := 4983230072969 + 3 ^ 40 * 3403776 * 2
def baseEnd_3403776 : Nat := 1747773128238179944446325

theorem tailTrace_3403776 : CollatzResearch.WordTrace tailWord_3403776 prefixEnd_3403776 1747773128238179944446325 := by
  unfold tailWord_3403776
  simp only [CollatzResearch.WordTrace]
  refine ⟨62072954858354172752383591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82763939811138897003178121 62072954858354172752383591)
  ·
    refine ⟨93109432287531259128575387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62072954858354172752383591 93109432287531259128575387)
    ·
      refine ⟨139664148431296888692863081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93109432287531259128575387 139664148431296888692863081)
      ·
        refine ⟨104748111323472666519647311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139664148431296888692863081 104748111323472666519647311)
        ·
          refine ⟨157122166985208999779470967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104748111323472666519647311 157122166985208999779470967)
          ·
            refine ⟨235683250477813499669206451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157122166985208999779470967 235683250477813499669206451)
            ·
              refine ⟨353524875716720249503809677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235683250477813499669206451 353524875716720249503809677)
              ·
                refine ⟨132571828393770093563928629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 353524875716720249503809677 132571828393770093563928629)
                ·
                  refine ⟨12428608911915946271618309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 132571828393770093563928629 12428608911915946271618309)
                  ·
                    refine ⟨2330364170984239925928433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12428608911915946271618309 2330364170984239925928433)
                    ·
                      refine ⟨1747773128238179944446325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2330364170984239925928433 1747773128238179944446325)
                      ·
                        rfl

theorem cell23_3403776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 5, 4, 2].length) (baseStart_3403776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3403776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3403776 prefixEnd_3403776 := by exact prefixLift 3403776
  have htrace : WordTrace (prefixWord ++ tailWord_3403776) baseStart_3403776 baseEnd_3403776 := by
    simpa [prefixWord, tailWord_3403776, baseEnd_3403776] using wordTrace_append hprefix tailTrace_3403776
  have hstable : (prefixWord ++ tailWord_3403776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3403776).length < 2 ^ (prefixWord ++ tailWord_3403776).sum := by decide
  have hdescent : baseEnd_3403776 < baseStart_3403776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3403776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3403797 : List Nat := [1, 3, 2, 1, 5, 2, 1, 2, 1, 3, 2]
def baseStart_3403797 : Nat := 118140960795 + 3403797 * 2 ^ 59
def prefixEnd_3403797 : Nat := 4983230072969 + 3 ^ 40 * 3403797 * 2
def baseEnd_3403797 : Nat := 1747783911331924362283729

theorem tailTrace_3403797 : CollatzResearch.WordTrace tailWord_3403797 prefixEnd_3403797 1747783911331924362283729 := by
  unfold tailWord_3403797
  simp only [CollatzResearch.WordTrace]
  refine ⟨124146675649632266091281645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82764450433088177394187763 124146675649632266091281645)
  ·
    refine ⟨46555003368612099784230617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124146675649632266091281645 46555003368612099784230617)
    ·
      refine ⟨34916252526459074838172963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46555003368612099784230617 34916252526459074838172963)
      ·
        refine ⟨52374378789688612257259445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34916252526459074838172963 52374378789688612257259445)
        ·
          refine ⟨4910098011533307399118073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52374378789688612257259445 4910098011533307399118073)
          ·
            refine ⟨3682573508649980549338555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4910098011533307399118073 3682573508649980549338555)
            ·
              refine ⟨5523860262974970824007833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3682573508649980549338555 5523860262974970824007833)
              ·
                refine ⟨4142895197231228118005875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5523860262974970824007833 4142895197231228118005875)
                ·
                  refine ⟨6214342795846842177008813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4142895197231228118005875 6214342795846842177008813)
                  ·
                    refine ⟨2330378548442565816378305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6214342795846842177008813 2330378548442565816378305)
                    ·
                      refine ⟨1747783911331924362283729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2330378548442565816378305 1747783911331924362283729)
                      ·
                        rfl

theorem cell23_3403797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 2, 1, 3, 2].length) (baseStart_3403797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3403797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3403797 prefixEnd_3403797 := by exact prefixLift 3403797
  have htrace : WordTrace (prefixWord ++ tailWord_3403797) baseStart_3403797 baseEnd_3403797 := by
    simpa [prefixWord, tailWord_3403797, baseEnd_3403797] using wordTrace_append hprefix tailTrace_3403797
  have hstable : (prefixWord ++ tailWord_3403797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3403797).length < 2 ^ (prefixWord ++ tailWord_3403797).sum := by decide
  have hdescent : baseEnd_3403797 < baseStart_3403797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3403797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3403866 : List Nat := [3, 1, 1, 2, 1, 1, 5, 1, 1, 3, 4]
def baseStart_3403866 : Nat := 118140960795 + 3403866 * 2 ^ 59
def prefixEnd_3403866 : Nat := 4983230072969 + 3 ^ 40 * 3403866 * 2
def baseEnd_3403866 : Nat := 1747819341497084592320911

theorem tailTrace_3403866 : CollatzResearch.WordTrace tailWord_3403866 prefixEnd_3403866 1747819341497084592320911 := by
  unfold tailWord_3403866
  simp only [CollatzResearch.WordTrace]
  refine ⟨31037298071595572718885863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82766128190921527250362301 31037298071595572718885863)
  ·
    refine ⟨46555947107393359078328795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31037298071595572718885863 46555947107393359078328795)
    ·
      refine ⟨69833920661090038617493193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46555947107393359078328795 69833920661090038617493193)
      ·
        refine ⟨52375440495817528963119895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69833920661090038617493193 52375440495817528963119895)
        ·
          refine ⟨78563160743726293444679843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52375440495817528963119895 78563160743726293444679843)
          ·
            refine ⟨117844741115589440167019765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78563160743726293444679843 117844741115589440167019765)
            ·
              refine ⟨11047944479586510015658103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 117844741115589440167019765 11047944479586510015658103)
              ·
                refine ⟨16571916719379765023487155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11047944479586510015658103 16571916719379765023487155)
                ·
                  refine ⟨24857875079069647535230733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16571916719379765023487155 24857875079069647535230733)
                  ·
                    refine ⟨9321703154651117825711525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24857875079069647535230733 9321703154651117825711525)
                    ·
                      refine ⟨1747819341497084592320911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9321703154651117825711525 1747819341497084592320911)
                      ·
                        rfl

theorem cell23_3403866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 1, 1, 3, 4].length) (baseStart_3403866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3403866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3403866 prefixEnd_3403866 := by exact prefixLift 3403866
  have htrace : WordTrace (prefixWord ++ tailWord_3403866) baseStart_3403866 baseEnd_3403866 := by
    simpa [prefixWord, tailWord_3403866, baseEnd_3403866] using wordTrace_append hprefix tailTrace_3403866
  have hstable : (prefixWord ++ tailWord_3403866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3403866).length < 2 ^ (prefixWord ++ tailWord_3403866).sum := by decide
  have hdescent : baseEnd_3403866 < baseStart_3403866 := by decide
  rcases family_descends (prefixWord ++ tailWord_3403866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3403973 : List Nat := [1, 3, 1, 1, 1, 1, 4, 1, 2, 6, 2]
def baseStart_3403973 : Nat := 118140960795 + 3403973 * 2 ^ 59
def prefixEnd_3403973 : Nat := 4983230072969 + 3 ^ 40 * 3403973 * 2
def baseEnd_3403973 : Nat := 1747874283927115673682919

theorem tailTrace_3403973 : CollatzResearch.WordTrace tailWord_3403973 prefixEnd_3403973 1747874283927115673682919 := by
  unfold tailWord_3403973
  simp only [CollatzResearch.WordTrace]
  refine ⟨124153094896994648149688573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82768729931329765433125715 124153094896994648149688573)
  ·
    refine ⟨46557410586372993056133215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124153094896994648149688573 46557410586372993056133215)
    ·
      refine ⟨69836115879559489584199823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46557410586372993056133215 69836115879559489584199823)
      ·
        refine ⟨104754173819339234376299735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69836115879559489584199823 104754173819339234376299735)
        ·
          refine ⟨157131260729008851564449603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104754173819339234376299735 157131260729008851564449603)
          ·
            refine ⟨235696891093513277346674405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157131260729008851564449603 235696891093513277346674405)
            ·
              refine ⟨44193167080033739502501451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 235696891093513277346674405 44193167080033739502501451)
              ·
                refine ⟨66289750620050609253752177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44193167080033739502501451 66289750620050609253752177)
                ·
                  refine ⟨49717312965037956940314133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66289750620050609253752177 49717312965037956940314133)
                  ·
                    refine ⟨2330499045236154231577225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 49717312965037956940314133 2330499045236154231577225)
                    ·
                      refine ⟨1747874283927115673682919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2330499045236154231577225 1747874283927115673682919)
                      ·
                        rfl

theorem cell23_3403973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 6, 2].length) (baseStart_3403973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3403973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3403973 prefixEnd_3403973 := by exact prefixLift 3403973
  have htrace : WordTrace (prefixWord ++ tailWord_3403973) baseStart_3403973 baseEnd_3403973 := by
    simpa [prefixWord, tailWord_3403973, baseEnd_3403973] using wordTrace_append hprefix tailTrace_3403973
  have hstable : (prefixWord ++ tailWord_3403973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3403973).length < 2 ^ (prefixWord ++ tailWord_3403973).sum := by decide
  have hdescent : baseEnd_3403973 < baseStart_3403973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3403973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3403993 : List Nat := [1, 2, 1, 2, 3, 1, 5, 1, 1, 1, 5]
def baseStart_3403993 : Nat := 118140960795 + 3403993 * 2 ^ 59
def prefixEnd_3403993 : Nat := 4983230072969 + 3 ^ 40 * 3403993 * 2
def baseEnd_3403993 : Nat := 1747884553540205595432827

theorem tailTrace_3403993 : CollatzResearch.WordTrace tailWord_3403993 prefixEnd_3403993 1747884553540205595432827 := by
  unfold tailWord_3403993
  simp only [CollatzResearch.WordTrace]
  refine ⟨124153824356922191565416633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82769216237948127710277755 124153824356922191565416633)
  ·
    refine ⟨93115368267691643674062475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124153824356922191565416633 93115368267691643674062475)
    ·
      refine ⟨139673052401537465511093713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93115368267691643674062475 139673052401537465511093713)
      ·
        refine ⟨104754789301153099133320285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139673052401537465511093713 104754789301153099133320285)
        ·
          refine ⟨39283045987932412174995107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104754789301153099133320285 39283045987932412174995107)
          ·
            refine ⟨58924568981898618262492661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39283045987932412174995107 58924568981898618262492661)
            ·
              refine ⟨5524178342052995462108687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58924568981898618262492661 5524178342052995462108687)
              ·
                refine ⟨8286267513079493193163031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5524178342052995462108687 8286267513079493193163031)
                ·
                  refine ⟨12429401269619239789744547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8286267513079493193163031 12429401269619239789744547)
                  ·
                    refine ⟨18644101904428859684616821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12429401269619239789744547 18644101904428859684616821)
                    ·
                      refine ⟨1747884553540205595432827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18644101904428859684616821 1747884553540205595432827)
                      ·
                        rfl

theorem cell23_3403993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 1, 1, 1, 5].length) (baseStart_3403993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3403993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3403993 prefixEnd_3403993 := by exact prefixLift 3403993
  have htrace : WordTrace (prefixWord ++ tailWord_3403993) baseStart_3403993 baseEnd_3403993 := by
    simpa [prefixWord, tailWord_3403993, baseEnd_3403993] using wordTrace_append hprefix tailTrace_3403993
  have hstable : (prefixWord ++ tailWord_3403993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3403993).length < 2 ^ (prefixWord ++ tailWord_3403993).sum := by decide
  have hdescent : baseEnd_3403993 < baseStart_3403993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3403993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3404000 : List Nat := [2, 1, 1, 3, 1, 3, 4, 2, 2, 4]
def baseStart_3404000 : Nat := 118140960795 + 3404000 * 2 ^ 59
def prefixEnd_3404000 : Nat := 4983230072969 + 3 ^ 40 * 3404000 * 2
def baseEnd_3404000 : Nat := 582629382634929022681765

theorem tailTrace_3404000 : CollatzResearch.WordTrace tailWord_3404000 prefixEnd_3404000 582629382634929022681765 := by
  unfold tailWord_3404000
  simp only [CollatzResearch.WordTrace]
  refine ⟨62077039833948415880460727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82769386445264554507280969 62077039833948415880460727)
  ·
    refine ⟨93115559750922623820691091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62077039833948415880460727 93115559750922623820691091)
    ·
      refine ⟨139673339626383935731036637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93115559750922623820691091 139673339626383935731036637)
      ·
        refine ⟨52377502359893975899138739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139673339626383935731036637 52377502359893975899138739)
        ·
          refine ⟨78566253539840963848708109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52377502359893975899138739 78566253539840963848708109)
          ·
            refine ⟨29462345077440361443265541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78566253539840963848708109 29462345077440361443265541)
            ·
              refine ⟨5524189702020067770612289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29462345077440361443265541 5524189702020067770612289)
              ·
                refine ⟨4143142276515050827959217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5524189702020067770612289 4143142276515050827959217)
                ·
                  refine ⟨3107356707386288120969413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4143142276515050827959217 3107356707386288120969413)
                  ·
                    refine ⟨582629382634929022681765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3107356707386288120969413 582629382634929022681765)
                    ·
                      rfl

theorem cell23_3404000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 2, 2, 4].length) (baseStart_3404000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3404000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3404000 prefixEnd_3404000 := by exact prefixLift 3404000
  have htrace : WordTrace (prefixWord ++ tailWord_3404000) baseStart_3404000 baseEnd_3404000 := by
    simpa [prefixWord, tailWord_3404000, baseEnd_3404000] using wordTrace_append hprefix tailTrace_3404000
  have hstable : (prefixWord ++ tailWord_3404000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3404000).length < 2 ^ (prefixWord ++ tailWord_3404000).sum := by decide
  have hdescent : baseEnd_3404000 < baseStart_3404000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3404000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3404016 : List Nat := [2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 6]
def baseStart_3404016 : Nat := 118140960795 + 3404016 * 2 ^ 59
def prefixEnd_3404016 : Nat := 4983230072969 + 3 ^ 40 * 3404016 * 2
def baseEnd_3404016 : Nat := 1747896363595259005445221

theorem tailTrace_3404016 : CollatzResearch.WordTrace tailWord_3404016 prefixEnd_3404016 1747896363595259005445221 := by
  unfold tailWord_3404016
  simp only [CollatzResearch.WordTrace]
  refine ⟨62077331617919433246751951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82769775490559244329002601 62077331617919433246751951)
  ·
    refine ⟨93115997426879149870127927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62077331617919433246751951 93115997426879149870127927)
    ·
      refine ⟨139673996140318724805191891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93115997426879149870127927 139673996140318724805191891)
      ·
        refine ⟨209510994210478087207787837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139673996140318724805191891 209510994210478087207787837)
        ·
          refine ⟨78566622828929282702920439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 209510994210478087207787837 78566622828929282702920439)
          ·
            refine ⟨117849934243393924054380659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78566622828929282702920439 117849934243393924054380659)
            ·
              refine ⟨176774901365090886081570989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117849934243393924054380659 176774901365090886081570989)
              ·
                refine ⟨66290588011909082280589121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 176774901365090886081570989 66290588011909082280589121)
                ·
                  refine ⟨49717941008931811710441841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66290588011909082280589121 49717941008931811710441841)
                  ·
                    refine ⟨37288455756698858782831381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49717941008931811710441841 37288455756698858782831381)
                    ·
                      refine ⟨1747896363595259005445221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37288455756698858782831381 1747896363595259005445221)
                      ·
                        rfl

theorem cell23_3404016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 6].length) (baseStart_3404016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3404016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3404016 prefixEnd_3404016 := by exact prefixLift 3404016
  have htrace : WordTrace (prefixWord ++ tailWord_3404016) baseStart_3404016 baseEnd_3404016 := by
    simpa [prefixWord, tailWord_3404016, baseEnd_3404016] using wordTrace_append hprefix tailTrace_3404016
  have hstable : (prefixWord ++ tailWord_3404016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3404016).length < 2 ^ (prefixWord ++ tailWord_3404016).sum := by decide
  have hdescent : baseEnd_3404016 < baseStart_3404016 := by decide
  rcases family_descends (prefixWord ++ tailWord_3404016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3404030 : List Nat := [4, 2, 2, 1, 1, 1, 5, 7]
def baseStart_3404030 : Nat := 118140960795 + 3404030 * 2 ^ 59
def prefixEnd_3404030 : Nat := 4983230072969 + 3 ^ 40 * 3404030 * 2
def baseEnd_3404030 : Nat := 64737168604608220395191

theorem tailTrace_3404030 : CollatzResearch.WordTrace tailWord_3404030 prefixEnd_3404030 64737168604608220395191 := by
  unfold tailWord_3404030
  simp only [CollatzResearch.WordTrace]
  refine ⟨15519396732223518360564193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82770115905192097923009029 15519396732223518360564193)
  ·
    refine ⟨11639547549167638770423145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15519396732223518360564193 11639547549167638770423145)
    ·
      refine ⟨8729660661875729077817359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11639547549167638770423145 8729660661875729077817359)
      ·
        refine ⟨13094490992813593616726039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8729660661875729077817359 13094490992813593616726039)
        ·
          refine ⟨19641736489220390425089059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13094490992813593616726039 19641736489220390425089059)
          ·
            refine ⟨29462604733830585637633589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19641736489220390425089059 29462604733830585637633589)
            ·
              refine ⟨2762119193796617403528149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29462604733830585637633589 2762119193796617403528149)
              ·
                refine ⟨64737168604608220395191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2762119193796617403528149 64737168604608220395191)
                ·
                  rfl

theorem cell23_3404030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 5, 7].length) (baseStart_3404030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3404030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3404030 prefixEnd_3404030 := by exact prefixLift 3404030
  have htrace : WordTrace (prefixWord ++ tailWord_3404030) baseStart_3404030 baseEnd_3404030 := by
    simpa [prefixWord, tailWord_3404030, baseEnd_3404030] using wordTrace_append hprefix tailTrace_3404030
  have hstable : (prefixWord ++ tailWord_3404030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3404030).length < 2 ^ (prefixWord ++ tailWord_3404030).sum := by decide
  have hdescent : baseEnd_3404030 < baseStart_3404030 := by decide
  rcases family_descends (prefixWord ++ tailWord_3404030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3404040 : List Nat := [2, 1, 3, 2, 3, 1, 2, 2, 1, 3, 3]
def baseStart_3404040 : Nat := 118140960795 + 3404040 * 2 ^ 59
def prefixEnd_3404040 : Nat := 4983230072969 + 3 ^ 40 * 3404040 * 2
def baseEnd_3404040 : Nat := 1747908687130966911545111

theorem tailTrace_3404040 : CollatzResearch.WordTrace tailWord_3404040 prefixEnd_3404040 1747908687130966911545111 := by
  unfold tailWord_3404040
  simp only [CollatzResearch.WordTrace]
  refine ⟨62077769293875959296188787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82770359058501279061585049 62077769293875959296188787)
  ·
    refine ⟨93116653940813938944283181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62077769293875959296188787 93116653940813938944283181)
    ·
      refine ⟨34918745227805227104106193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93116653940813938944283181 34918745227805227104106193)
      ·
        refine ⟨26189058920853920328079645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34918745227805227104106193 26189058920853920328079645)
        ·
          refine ⟨9820897095320220123029867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26189058920853920328079645 9820897095320220123029867)
          ·
            refine ⟨14731345642980330184544801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9820897095320220123029867 14731345642980330184544801)
            ·
              refine ⟨11048509232235247638408601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14731345642980330184544801 11048509232235247638408601)
              ·
                refine ⟨8286381924176435728806451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11048509232235247638408601 8286381924176435728806451)
                ·
                  refine ⟨12429572886264653593209677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8286381924176435728806451 12429572886264653593209677)
                  ·
                    refine ⟨4661089832349245097453629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12429572886264653593209677 4661089832349245097453629)
                    ·
                      refine ⟨1747908687130966911545111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4661089832349245097453629 1747908687130966911545111)
                      ·
                        rfl

theorem cell23_3404040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 2, 1, 3, 3].length) (baseStart_3404040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3404040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3404040 prefixEnd_3404040 := by exact prefixLift 3404040
  have htrace : WordTrace (prefixWord ++ tailWord_3404040) baseStart_3404040 baseEnd_3404040 := by
    simpa [prefixWord, tailWord_3404040, baseEnd_3404040] using wordTrace_append hprefix tailTrace_3404040
  have hstable : (prefixWord ++ tailWord_3404040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3404040).length < 2 ^ (prefixWord ++ tailWord_3404040).sum := by decide
  have hdescent : baseEnd_3404040 < baseStart_3404040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3404040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3404071 : List Nat := [1, 1, 8, 1, 1, 2, 1, 1, 1, 2, 4]
def baseStart_3404071 : Nat := 118140960795 + 3404071 * 2 ^ 59
def prefixEnd_3404071 : Nat := 4983230072969 + 3 ^ 40 * 3404071 * 2
def baseEnd_3404071 : Nat := 1747924605031256290257469

theorem tailTrace_3404071 : CollatzResearch.WordTrace tailWord_3404071 prefixEnd_3404071 1747924605031256290257469 := by
  unfold tailWord_3404071
  simp only [CollatzResearch.WordTrace]
  refine ⟨124156669250639610886756067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82771112833759740591170711 124156669250639610886756067)
  ·
    refine ⟨186235003875959416330134101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124156669250639610886756067 186235003875959416330134101)
    ·
      refine ⟨2182441451671399410118759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 186235003875959416330134101 2182441451671399410118759)
      ·
        refine ⟨3273662177507099115178139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2182441451671399410118759 3273662177507099115178139)
        ·
          refine ⟨4910493266260648672767209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3273662177507099115178139 4910493266260648672767209)
          ·
            refine ⟨3682869949695486504575407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4910493266260648672767209 3682869949695486504575407)
            ·
              refine ⟨5524304924543229756863111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3682869949695486504575407 5524304924543229756863111)
              ·
                refine ⟨8286457386814844635294667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5524304924543229756863111 8286457386814844635294667)
                ·
                  refine ⟨12429686080222266952942001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8286457386814844635294667 12429686080222266952942001)
                  ·
                    refine ⟨9322264560166700214706501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12429686080222266952942001 9322264560166700214706501)
                    ·
                      refine ⟨1747924605031256290257469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9322264560166700214706501 1747924605031256290257469)
                      ·
                        rfl

theorem cell23_3404071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_3404071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3404071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3404071 prefixEnd_3404071 := by exact prefixLift 3404071
  have htrace : WordTrace (prefixWord ++ tailWord_3404071) baseStart_3404071 baseEnd_3404071 := by
    simpa [prefixWord, tailWord_3404071, baseEnd_3404071] using wordTrace_append hprefix tailTrace_3404071
  have hstable : (prefixWord ++ tailWord_3404071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3404071).length < 2 ^ (prefixWord ++ tailWord_3404071).sum := by decide
  have hdescent : baseEnd_3404071 < baseStart_3404071 := by decide
  rcases family_descends (prefixWord ++ tailWord_3404071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3404074 : List Nat := [3, 1, 4, 2, 2, 2, 1, 1, 1, 3, 3]
def baseStart_3404074 : Nat := 118140960795 + 3404074 * 2 ^ 59
def prefixEnd_3404074 : Nat := 4983230072969 + 3 ^ 40 * 3404074 * 2
def baseEnd_3404074 : Nat := 1747926145473219778519955

theorem tailTrace_3404074 : CollatzResearch.WordTrace tailWord_3404074 prefixEnd_3404074 1747926145473219778519955 := by
  unfold tailWord_3404074
  simp only [CollatzResearch.WordTrace]
  refine ⟨31039194667407185599778819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82771185779752494932743517 31039194667407185599778819)
  ·
    refine ⟨46558792001110778399668229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31039194667407185599778819 46558792001110778399668229)
    ·
      refine ⟨8729773500208270949937793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46558792001110778399668229 8729773500208270949937793)
      ·
        refine ⟨6547330125156203212453345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8729773500208270949937793 6547330125156203212453345)
        ·
          refine ⟨4910497593867152409340009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6547330125156203212453345 4910497593867152409340009)
          ·
            refine ⟨3682873195400364307005007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4910497593867152409340009 3682873195400364307005007)
            ·
              refine ⟨5524309793100546460507511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3682873195400364307005007 5524309793100546460507511)
              ·
                refine ⟨8286464689650819690761267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5524309793100546460507511 8286464689650819690761267)
                ·
                  refine ⟨12429697034476229536141901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8286464689650819690761267 12429697034476229536141901)
                  ·
                    refine ⟨4661136387928586076053213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12429697034476229536141901 4661136387928586076053213)
                    ·
                      refine ⟨1747926145473219778519955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4661136387928586076053213 1747926145473219778519955)
                      ·
                        rfl

theorem cell23_3404074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_3404074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3404074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3404074 prefixEnd_3404074 := by exact prefixLift 3404074
  have htrace : WordTrace (prefixWord ++ tailWord_3404074) baseStart_3404074 baseEnd_3404074 := by
    simpa [prefixWord, tailWord_3404074, baseEnd_3404074] using wordTrace_append hprefix tailTrace_3404074
  have hstable : (prefixWord ++ tailWord_3404074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3404074).length < 2 ^ (prefixWord ++ tailWord_3404074).sum := by decide
  have hdescent : baseEnd_3404074 < baseStart_3404074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3404074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3404080 : List Nat := [2, 1, 1, 1, 2, 2, 2, 5, 1, 4, 2]
def baseStart_3404080 : Nat := 118140960795 + 3404080 * 2 ^ 59
def prefixEnd_3404080 : Nat := 4983230072969 + 3 ^ 40 * 3404080 * 2
def baseEnd_3404080 : Nat := 1747929226357146755044927

theorem tailTrace_3404080 : CollatzResearch.WordTrace tailWord_3404080 prefixEnd_3404080 1747929226357146755044927 := by
  unfold tailWord_3404080
  simp only [CollatzResearch.WordTrace]
  refine ⟨62078498753803502711916847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82771331671738003615889129 62078498753803502711916847)
  ·
    refine ⟨93117748130705254067875271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62078498753803502711916847 93117748130705254067875271)
    ·
      refine ⟨139676622196057881101812907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93117748130705254067875271 139676622196057881101812907)
      ·
        refine ⟨209514933294086821652719361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139676622196057881101812907 209514933294086821652719361)
        ·
          refine ⟨157136199970565116239539521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209514933294086821652719361 157136199970565116239539521)
          ·
            refine ⟨117852149977923837179654641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157136199970565116239539521 117852149977923837179654641)
            ·
              refine ⟨88389112483442877884740981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117852149977923837179654641 88389112483442877884740981)
              ·
                refine ⟨8286479295322769801694467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 88389112483442877884740981 8286479295322769801694467)
                ·
                  refine ⟨12429718942984154702541701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8286479295322769801694467 12429718942984154702541701)
                  ·
                    refine ⟨2330572301809529006726569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12429718942984154702541701 2330572301809529006726569)
                    ·
                      refine ⟨1747929226357146755044927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2330572301809529006726569 1747929226357146755044927)
                      ·
                        rfl

theorem cell23_3404080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 5, 1, 4, 2].length) (baseStart_3404080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3404080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3404080 prefixEnd_3404080 := by exact prefixLift 3404080
  have htrace : WordTrace (prefixWord ++ tailWord_3404080) baseStart_3404080 baseEnd_3404080 := by
    simpa [prefixWord, tailWord_3404080, baseEnd_3404080] using wordTrace_append hprefix tailTrace_3404080
  have hstable : (prefixWord ++ tailWord_3404080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3404080).length < 2 ^ (prefixWord ++ tailWord_3404080).sum := by decide
  have hdescent : baseEnd_3404080 < baseStart_3404080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3404080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3404083 : List Nat := [1, 1, 1, 2, 5, 1, 2, 2, 2, 1, 5]
def baseStart_3404083 : Nat := 118140960795 + 3404083 * 2 ^ 59
def prefixEnd_3404083 : Nat := 4983230072969 + 3 ^ 40 * 3404083 * 2
def baseEnd_3404083 : Nat := 1747930766799110243307413

theorem tailTrace_3404083 : CollatzResearch.WordTrace tailWord_3404083 prefixEnd_3404083 1747930766799110243307413 := by
  unfold tailWord_3404083
  simp only [CollatzResearch.WordTrace]
  refine ⟨124157106926596136936192903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82771404617730757957461935 124157106926596136936192903)
  ·
    refine ⟨186235660389894205404289355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124157106926596136936192903 186235660389894205404289355)
    ·
      refine ⟨279353490584841308106434033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186235660389894205404289355 279353490584841308106434033)
      ·
        refine ⟨209515117938630981079825525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279353490584841308106434033 209515117938630981079825525)
        ·
          refine ⟨19642042306746654476233643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 209515117938630981079825525 19642042306746654476233643)
          ·
            refine ⟨29463063460119981714350465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19642042306746654476233643 29463063460119981714350465)
            ·
              refine ⟨22097297595089986285762849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29463063460119981714350465 22097297595089986285762849)
              ·
                refine ⟨16572973196317489714322137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22097297595089986285762849 16572973196317489714322137)
                ·
                  refine ⟨12429729897238117285741603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16572973196317489714322137 12429729897238117285741603)
                  ·
                    refine ⟨18644594845857175928612405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12429729897238117285741603 18644594845857175928612405)
                    ·
                      refine ⟨1747930766799110243307413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18644594845857175928612405 1747930766799110243307413)
                      ·
                        rfl

theorem cell23_3404083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 2, 2, 1, 5].length) (baseStart_3404083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3404083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3404083 prefixEnd_3404083 := by exact prefixLift 3404083
  have htrace : WordTrace (prefixWord ++ tailWord_3404083) baseStart_3404083 baseEnd_3404083 := by
    simpa [prefixWord, tailWord_3404083, baseEnd_3404083] using wordTrace_append hprefix tailTrace_3404083
  have hstable : (prefixWord ++ tailWord_3404083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3404083).length < 2 ^ (prefixWord ++ tailWord_3404083).sum := by decide
  have hdescent : baseEnd_3404083 < baseStart_3404083 := by decide
  rcases family_descends (prefixWord ++ tailWord_3404083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3404084 : List Nat := [2, 5, 1, 1, 1, 2, 1, 4, 1, 3, 2]
def baseStart_3404084 : Nat := 118140960795 + 3404084 * 2 ^ 59
def prefixEnd_3404084 : Nat := 4983230072969 + 3 ^ 40 * 3404084 * 2
def baseEnd_3404084 : Nat := 1747931280279764739394909

theorem tailTrace_3404084 : CollatzResearch.WordTrace tailWord_3404084 prefixEnd_3404084 1747931280279764739394909 := by
  unfold tailWord_3404084
  simp only [CollatzResearch.WordTrace]
  refine ⟨62078571699796257053489653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82771428933061676071319537 62078571699796257053489653)
  ·
    refine ⟨5819866096855899098764655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62078571699796257053489653 5819866096855899098764655)
    ·
      refine ⟨8729799145283848648146983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5819866096855899098764655 8729799145283848648146983)
      ·
        refine ⟨13094698717925772972220475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8729799145283848648146983 13094698717925772972220475)
        ·
          refine ⟨19642048076888659458330713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13094698717925772972220475 19642048076888659458330713)
          ·
            refine ⟨14731536057666494593748035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19642048076888659458330713 14731536057666494593748035)
            ·
              refine ⟨22097304086499741890622053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14731536057666494593748035 22097304086499741890622053)
              ·
                refine ⟨4143244516218701604491635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22097304086499741890622053 4143244516218701604491635)
                ·
                  refine ⟨6214866774328052406737453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4143244516218701604491635 6214866774328052406737453)
                  ·
                    refine ⟨2330575040373019652526545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6214866774328052406737453 2330575040373019652526545)
                    ·
                      refine ⟨1747931280279764739394909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2330575040373019652526545 1747931280279764739394909)
                      ·
                        rfl

theorem cell23_3404084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 4, 1, 3, 2].length) (baseStart_3404084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3404084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3404084 prefixEnd_3404084 := by exact prefixLift 3404084
  have htrace : WordTrace (prefixWord ++ tailWord_3404084) baseStart_3404084 baseEnd_3404084 := by
    simpa [prefixWord, tailWord_3404084, baseEnd_3404084] using wordTrace_append hprefix tailTrace_3404084
  have hstable : (prefixWord ++ tailWord_3404084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3404084).length < 2 ^ (prefixWord ++ tailWord_3404084).sum := by decide
  have hdescent : baseEnd_3404084 < baseStart_3404084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3404084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3404244 : List Nat := [2, 4, 1, 2, 2, 2, 3, 1, 6]
def baseStart_3404244 : Nat := 118140960795 + 3404244 * 2 ^ 59
def prefixEnd_3404244 : Nat := 4983230072969 + 3 ^ 40 * 3404244 * 2
def baseEnd_3404244 : Nat := 194223715242720457043797

theorem tailTrace_3404244 : CollatzResearch.WordTrace tailWord_3404244 prefixEnd_3404244 194223715242720457043797 := by
  unfold tailWord_3404244
  simp only [CollatzResearch.WordTrace]
  refine ⟨62081489539506430716401893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82775319386008574288535857 62081489539506430716401893)
  ·
    refine ⟨11640279288657455759325355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62081489539506430716401893 11640279288657455759325355)
    ·
      refine ⟨17460418932986183638988033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11640279288657455759325355 17460418932986183638988033)
      ·
        refine ⟨13095314199739637729241025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17460418932986183638988033 13095314199739637729241025)
        ·
          refine ⟨9821485649804728296930769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13095314199739637729241025 9821485649804728296930769)
          ·
            refine ⟨7366114237353546222698077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9821485649804728296930769 7366114237353546222698077)
            ·
              refine ⟨2762292839007579833511779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7366114237353546222698077 2762292839007579833511779)
              ·
                refine ⟨4143439258511369750267669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2762292839007579833511779 4143439258511369750267669)
                ·
                  refine ⟨194223715242720457043797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4143439258511369750267669 194223715242720457043797)
                  ·
                    rfl

theorem cell23_3404244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 3, 1, 6].length) (baseStart_3404244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3404244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3404244 prefixEnd_3404244 := by exact prefixLift 3404244
  have htrace : WordTrace (prefixWord ++ tailWord_3404244) baseStart_3404244 baseEnd_3404244 := by
    simpa [prefixWord, tailWord_3404244, baseEnd_3404244] using wordTrace_append hprefix tailTrace_3404244
  have hstable : (prefixWord ++ tailWord_3404244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3404244).length < 2 ^ (prefixWord ++ tailWord_3404244).sum := by decide
  have hdescent : baseEnd_3404244 < baseStart_3404244 := by decide
  rcases family_descends (prefixWord ++ tailWord_3404244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3404257 : List Nat := [1, 2, 3, 1, 2, 2, 4, 2, 1, 5]
def baseStart_3404257 : Nat := 118140960795 + 3404257 * 2 ^ 59
def prefixEnd_3404257 : Nat := 4983230072969 + 3 ^ 40 * 3404257 * 2
def baseEnd_3404257 : Nat := 582673370810997520843871

theorem tailTrace_3404257 : CollatzResearch.WordTrace tailWord_3404257 prefixEnd_3404257 582673370810997520843871 := by
  unfold tailWord_3404257
  simp only [CollatzResearch.WordTrace]
  refine ⟨124163453227965764653027025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82775635485310509768684683 124163453227965764653027025)
  ·
    refine ⟨93122589920974323489770269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124163453227965764653027025 93122589920974323489770269)
    ·
      refine ⟨34920971220365371308663851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93122589920974323489770269 34920971220365371308663851)
      ·
        refine ⟨52381456830548056962995777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34920971220365371308663851 52381456830548056962995777)
        ·
          refine ⟨39286092622911042722246833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52381456830548056962995777 39286092622911042722246833)
          ·
            refine ⟨29464569467183282041685125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39286092622911042722246833 29464569467183282041685125)
            ·
              refine ⟨5524606775096865382815961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29464569467183282041685125 5524606775096865382815961)
              ·
                refine ⟨4143455081322649037111971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5524606775096865382815961 4143455081322649037111971)
                ·
                  refine ⟨6215182621983973555667957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4143455081322649037111971 6215182621983973555667957)
                  ·
                    refine ⟨582673370810997520843871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6215182621983973555667957 582673370810997520843871)
                    ·
                      rfl

theorem cell23_3404257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 2, 1, 5].length) (baseStart_3404257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3404257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3404257 prefixEnd_3404257 := by exact prefixLift 3404257
  have htrace : WordTrace (prefixWord ++ tailWord_3404257) baseStart_3404257 baseEnd_3404257 := by
    simpa [prefixWord, tailWord_3404257, baseEnd_3404257] using wordTrace_append hprefix tailTrace_3404257
  have hstable : (prefixWord ++ tailWord_3404257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3404257).length < 2 ^ (prefixWord ++ tailWord_3404257).sum := by decide
  have hdescent : baseEnd_3404257 < baseStart_3404257 := by decide
  rcases family_descends (prefixWord ++ tailWord_3404257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3404287 : List Nat := [1, 1, 2, 2, 1, 2, 4, 4, 2, 4]
def baseStart_3404287 : Nat := 118140960795 + 3404287 * 2 ^ 59
def prefixEnd_3404287 : Nat := 4983230072969 + 3 ^ 40 * 3404287 * 2
def baseEnd_3404287 : Nat := 582678505617542481718825

theorem tailTrace_3404287 : CollatzResearch.WordTrace tailWord_3404287 prefixEnd_3404287 582678505617542481718825 := by
  unfold tailWord_3404287
  simp only [CollatzResearch.WordTrace]
  refine ⟨124164547417857079776619115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82776364945238053184412743 124164547417857079776619115)
  ·
    refine ⟨186246821126785619664928673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124164547417857079776619115 186246821126785619664928673)
    ·
      refine ⟨139685115845089214748696505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186246821126785619664928673 139685115845089214748696505)
      ·
        refine ⟨104763836883816911061522379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139685115845089214748696505 104763836883816911061522379)
        ·
          refine ⟨157145755325725366592283569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104763836883816911061522379 157145755325725366592283569)
          ·
            refine ⟨117859316494294024944212677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157145755325725366592283569 117859316494294024944212677)
            ·
              refine ⟨22098621842680129677039877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 117859316494294024944212677 22098621842680129677039877)
              ·
                refine ⟨4143491595502524314444977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22098621842680129677039877 4143491595502524314444977)
                ·
                  refine ⟨3107618696626893235833733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4143491595502524314444977 3107618696626893235833733)
                  ·
                    refine ⟨582678505617542481718825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3107618696626893235833733 582678505617542481718825)
                    ·
                      rfl

theorem cell23_3404287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 4, 2, 4].length) (baseStart_3404287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3404287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3404287 prefixEnd_3404287 := by exact prefixLift 3404287
  have htrace : WordTrace (prefixWord ++ tailWord_3404287) baseStart_3404287 baseEnd_3404287 := by
    simpa [prefixWord, tailWord_3404287, baseEnd_3404287] using wordTrace_append hprefix tailTrace_3404287
  have hstable : (prefixWord ++ tailWord_3404287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3404287).length < 2 ^ (prefixWord ++ tailWord_3404287).sum := by decide
  have hdescent : baseEnd_3404287 < baseStart_3404287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3404287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3404300 : List Nat := [2, 2, 1, 2, 4, 1, 1, 10]
def baseStart_3404300 : Nat := 118140960795 + 3404300 * 2 ^ 59
def prefixEnd_3404300 : Nat := 4983230072969 + 3 ^ 40 * 3404300 * 2
def baseEnd_3404300 : Nat := 64742303411153181270145

theorem tailTrace_3404300 : CollatzResearch.WordTrace tailWord_3404300 prefixEnd_3404300 64742303411153181270145 := by
  unfold tailWord_3404300
  simp only [CollatzResearch.WordTrace]
  refine ⟨62082510783404991498421177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82776681044539988664561569 62082510783404991498421177)
  ·
    refine ⟨46561883087553743623815883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62082510783404991498421177 46561883087553743623815883)
    ·
      refine ⟨69842824631330615435723825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46561883087553743623815883 69842824631330615435723825)
      ·
        refine ⟨52382118473497961576792869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69842824631330615435723825 52382118473497961576792869)
        ·
          refine ⟨9821647213780867795648663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52382118473497961576792869 9821647213780867795648663)
          ·
            refine ⟨14732470820671301693472995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9821647213780867795648663 14732470820671301693472995)
            ·
              refine ⟨22098706231006952540209493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14732470820671301693472995 22098706231006952540209493)
              ·
                refine ⟨64742303411153181270145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 22098706231006952540209493 64742303411153181270145)
                ·
                  rfl

theorem cell23_3404300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 10].length) (baseStart_3404300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3404300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3404300 prefixEnd_3404300 := by exact prefixLift 3404300
  have htrace : WordTrace (prefixWord ++ tailWord_3404300) baseStart_3404300 baseEnd_3404300 := by
    simpa [prefixWord, tailWord_3404300, baseEnd_3404300] using wordTrace_append hprefix tailTrace_3404300
  have hstable : (prefixWord ++ tailWord_3404300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3404300).length < 2 ^ (prefixWord ++ tailWord_3404300).sum := by decide
  have hdescent : baseEnd_3404300 < baseStart_3404300 := by decide
  rcases family_descends (prefixWord ++ tailWord_3404300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3404314 : List Nat := [3, 1, 1, 3, 1, 1, 5, 2, 1, 2, 3]
def baseStart_3404314 : Nat := 118140960795 + 3404314 * 2 ^ 59
def prefixEnd_3404314 : Nat := 4983230072969 + 3 ^ 40 * 3404314 * 2
def baseEnd_3404314 : Nat := 1748049380830298839518851

theorem tailTrace_3404314 : CollatzResearch.WordTrace tailWord_3404314 prefixEnd_3404314 1748049380830298839518851 := by
  unfold tailWord_3404314
  simp only [CollatzResearch.WordTrace]
  refine ⟨31041383047189815846962999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82777021459172842258567997 31041383047189815846962999)
  ·
    refine ⟨46562074570784723770444499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31041383047189815846962999 46562074570784723770444499)
    ·
      refine ⟨69843111856177085655666749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46562074570784723770444499 69843111856177085655666749)
      ·
        refine ⟨26191166946066407120875031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69843111856177085655666749 26191166946066407120875031)
        ·
          refine ⟨39286750419099610681312547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26191166946066407120875031 39286750419099610681312547)
          ·
            refine ⟨58930125628649416021968821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39286750419099610681312547 58930125628649416021968821)
            ·
              refine ⟨5524699277685882752059577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58930125628649416021968821 5524699277685882752059577)
              ·
                refine ⟨4143524458264412064044683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5524699277685882752059577 4143524458264412064044683)
                ·
                  refine ⟨6215286687396618096067025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4143524458264412064044683 6215286687396618096067025)
                  ·
                    refine ⟨4661465015547463572050269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6215286687396618096067025 4661465015547463572050269)
                    ·
                      refine ⟨1748049380830298839518851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4661465015547463572050269 1748049380830298839518851)
                      ·
                        rfl

theorem cell23_3404314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 2, 1, 2, 3].length) (baseStart_3404314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3404314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3404314 prefixEnd_3404314 := by exact prefixLift 3404314
  have htrace : WordTrace (prefixWord ++ tailWord_3404314) baseStart_3404314 baseEnd_3404314 := by
    simpa [prefixWord, tailWord_3404314, baseEnd_3404314] using wordTrace_append hprefix tailTrace_3404314
  have hstable : (prefixWord ++ tailWord_3404314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3404314).length < 2 ^ (prefixWord ++ tailWord_3404314).sum := by decide
  have hdescent : baseEnd_3404314 < baseStart_3404314 := by decide
  rcases family_descends (prefixWord ++ tailWord_3404314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3404384 : List Nat := [2, 1, 1, 3, 2, 1, 4, 2, 1, 4, 2]
def baseStart_3404384 : Nat := 118140960795 + 3404384 * 2 ^ 59
def prefixEnd_3404384 : Nat := 4983230072969 + 3 ^ 40 * 3404384 * 2
def baseEnd_3404384 : Nat := 1748085324476113565643529

theorem tailTrace_3404384 : CollatzResearch.WordTrace tailWord_3404384 prefixEnd_3404384 1748085324476113565643529 := by
  unfold tailWord_3404384
  simp only [CollatzResearch.WordTrace]
  refine ⟨62084042649252832671450103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82778723532337110228600137 62084042649252832671450103)
  ·
    refine ⟨93126063973879249007175155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62084042649252832671450103 93126063973879249007175155)
    ·
      refine ⟨139689095960818873510762733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93126063973879249007175155 139689095960818873510762733)
      ·
        refine ⟨52383410985307077566536025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139689095960818873510762733 52383410985307077566536025)
        ·
          refine ⟨39287558238980308174902019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52383410985307077566536025 39287558238980308174902019)
          ·
            refine ⟨58931337358470462262353029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39287558238980308174902019 58931337358470462262353029)
            ·
              refine ⟨11049625754713211674191193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58931337358470462262353029 11049625754713211674191193)
              ·
                refine ⟨8287219316034908755643395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11049625754713211674191193 8287219316034908755643395)
                ·
                  refine ⟨12430828974052363133465093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8287219316034908755643395 12430828974052363133465093)
                  ·
                    refine ⟨2330780432634818087524705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12430828974052363133465093 2330780432634818087524705)
                    ·
                      refine ⟨1748085324476113565643529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2330780432634818087524705 1748085324476113565643529)
                      ·
                        rfl

theorem cell23_3404384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 2, 1, 4, 2].length) (baseStart_3404384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3404384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3404384 prefixEnd_3404384 := by exact prefixLift 3404384
  have htrace : WordTrace (prefixWord ++ tailWord_3404384) baseStart_3404384 baseEnd_3404384 := by
    simpa [prefixWord, tailWord_3404384, baseEnd_3404384] using wordTrace_append hprefix tailTrace_3404384
  have hstable : (prefixWord ++ tailWord_3404384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3404384).length < 2 ^ (prefixWord ++ tailWord_3404384).sum := by decide
  have hdescent : baseEnd_3404384 < baseStart_3404384 := by decide
  rcases family_descends (prefixWord ++ tailWord_3404384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3404457 : List Nat := [1, 2, 1, 1, 1, 1, 2, 5, 4, 1, 4]
def baseStart_3404457 : Nat := 118140960795 + 3404457 * 2 ^ 59
def prefixEnd_3404457 : Nat := 4983230072969 + 3 ^ 40 * 3404457 * 2
def baseEnd_3404457 : Nat := 1748122808563891780030693

theorem tailTrace_3404457 : CollatzResearch.WordTrace tailWord_3404457 prefixEnd_3404457 1748122808563891780030693 := by
  unfold tailWord_3404457
  simp only [CollatzResearch.WordTrace]
  refine ⟨124170747827241198810307625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82780498551494132540205083 124170747827241198810307625)
  ·
    refine ⟨93128060870430899107730719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124170747827241198810307625 93128060870430899107730719)
    ·
      refine ⟨139692091305646348661596079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93128060870430899107730719 139692091305646348661596079)
      ·
        refine ⟨209538136958469522992394119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139692091305646348661596079 209538136958469522992394119)
        ·
          refine ⟨314307205437704284488591179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209538136958469522992394119 314307205437704284488591179)
          ·
            refine ⟨471460808156556426732886769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314307205437704284488591179 471460808156556426732886769)
            ·
              refine ⟨353595606117417320049665077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 471460808156556426732886769 353595606117417320049665077)
              ·
                refine ⟨33149588073507873754656101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 353595606117417320049665077 33149588073507873754656101)
                ·
                  refine ⟨6215547763782726328998019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33149588073507873754656101 6215547763782726328998019)
                  ·
                    refine ⟨9323321645674089493497029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6215547763782726328998019 9323321645674089493497029)
                    ·
                      refine ⟨1748122808563891780030693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9323321645674089493497029 1748122808563891780030693)
                      ·
                        rfl

theorem cell23_3404457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 4, 1, 4].length) (baseStart_3404457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3404457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3404457 prefixEnd_3404457 := by exact prefixLift 3404457
  have htrace : WordTrace (prefixWord ++ tailWord_3404457) baseStart_3404457 baseEnd_3404457 := by
    simpa [prefixWord, tailWord_3404457, baseEnd_3404457] using wordTrace_append hprefix tailTrace_3404457
  have hstable : (prefixWord ++ tailWord_3404457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3404457).length < 2 ^ (prefixWord ++ tailWord_3404457).sum := by decide
  have hdescent : baseEnd_3404457 < baseStart_3404457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3404457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3404458 : List Nat := [3, 1, 5, 2, 1, 2, 1, 1, 7]
def baseStart_3404458 : Nat := 118140960795 + 3404458 * 2 ^ 59
def prefixEnd_3404458 : Nat := 4983230072969 + 3 ^ 40 * 3404458 * 2
def baseEnd_3404458 : Nat := 194235924671616252902021

theorem tailTrace_3404458 : CollatzResearch.WordTrace tailWord_3404458 prefixEnd_3404458 194235924671616252902021 := by
  unfold tailWord_3404458
  simp only [CollatzResearch.WordTrace]
  refine ⟨31042696075059393995273507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82780522866825050654062685 31042696075059393995273507)
  ·
    refine ⟨46564044112589090992910261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31042696075059393995273507 46564044112589090992910261)
    ·
      refine ⟨4365379135555227280585337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46564044112589090992910261 4365379135555227280585337)
      ·
        refine ⟨3274034351666420460439003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4365379135555227280585337 3274034351666420460439003)
        ·
          refine ⟨4911051527499630690658505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3274034351666420460439003 4911051527499630690658505)
          ·
            refine ⟨3683288645624723017993879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4911051527499630690658505 3683288645624723017993879)
            ·
              refine ⟨5524932968437084526990819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3683288645624723017993879 5524932968437084526990819)
              ·
                refine ⟨8287399452655626790486229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5524932968437084526990819 8287399452655626790486229)
                ·
                  refine ⟨194235924671616252902021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8287399452655626790486229 194235924671616252902021)
                  ·
                    rfl

theorem cell23_3404458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 1, 7].length) (baseStart_3404458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3404458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3404458 prefixEnd_3404458 := by exact prefixLift 3404458
  have htrace : WordTrace (prefixWord ++ tailWord_3404458) baseStart_3404458 baseEnd_3404458 := by
    simpa [prefixWord, tailWord_3404458, baseEnd_3404458] using wordTrace_append hprefix tailTrace_3404458
  have hstable : (prefixWord ++ tailWord_3404458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3404458).length < 2 ^ (prefixWord ++ tailWord_3404458).sum := by decide
  have hdescent : baseEnd_3404458 < baseStart_3404458 := by decide
  rcases family_descends (prefixWord ++ tailWord_3404458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3404474 : List Nat := [3, 1, 1, 1, 2, 3, 2, 1, 1, 6, 2]
def baseStart_3404474 : Nat := 118140960795 + 3404474 * 2 ^ 59
def prefixEnd_3404474 : Nat := 4983230072969 + 3 ^ 40 * 3404474 * 2
def baseEnd_3404474 : Nat := 1748131537735018213518115

theorem tailTrace_3404474 : CollatzResearch.WordTrace tailWord_3404474 prefixEnd_3404474 1748131537735018213518115 := by
  unfold tailWord_3404474
  simp only [CollatzResearch.WordTrace]
  refine ⟨31042841967044902678419119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82780911912119740475784317 31042841967044902678419119)
  ·
    refine ⟨46564262950567354017628679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31042841967044902678419119 46564262950567354017628679)
    ·
      refine ⟨69846394425851031026443019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46564262950567354017628679 69846394425851031026443019)
      ·
        refine ⟨104769591638776546539664529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69846394425851031026443019 104769591638776546539664529)
        ·
          refine ⟨78577193729082409904748397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104769591638776546539664529 78577193729082409904748397)
          ·
            refine ⟨29466447648405903714280649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78577193729082409904748397 29466447648405903714280649)
            ·
              refine ⟨22099835736304427785710487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29466447648405903714280649 22099835736304427785710487)
              ·
                refine ⟨33149753604456641678565731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22099835736304427785710487 33149753604456641678565731)
                ·
                  refine ⟨49724630406684962517848597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33149753604456641678565731 49724630406684962517848597)
                  ·
                    refine ⟨2330842050313357618024153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 49724630406684962517848597 2330842050313357618024153)
                    ·
                      refine ⟨1748131537735018213518115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2330842050313357618024153 1748131537735018213518115)
                      ·
                        rfl

theorem cell23_3404474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 1, 6, 2].length) (baseStart_3404474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3404474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3404474 prefixEnd_3404474 := by exact prefixLift 3404474
  have htrace : WordTrace (prefixWord ++ tailWord_3404474) baseStart_3404474 baseEnd_3404474 := by
    simpa [prefixWord, tailWord_3404474, baseEnd_3404474] using wordTrace_append hprefix tailTrace_3404474
  have hstable : (prefixWord ++ tailWord_3404474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3404474).length < 2 ^ (prefixWord ++ tailWord_3404474).sum := by decide
  have hdescent : baseEnd_3404474 < baseStart_3404474 := by decide
  rcases family_descends (prefixWord ++ tailWord_3404474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3404507 : List Nat := [1, 1, 1, 1, 1, 1, 1, 3, 3, 7, 3]
def baseStart_3404507 : Nat := 118140960795 + 3404507 * 2 ^ 59
def prefixEnd_3404507 : Nat := 4983230072969 + 3 ^ 40 * 3404507 * 2
def baseEnd_3404507 : Nat := 1748148482596616584405463

theorem tailTrace_3404507 : CollatzResearch.WordTrace tailWord_3404507 prefixEnd_3404507 1748148482596616584405463 := by
  unfold tailWord_3404507
  simp only [CollatzResearch.WordTrace]
  refine ⟨124172571477060057349627775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82781714318040038233085183 124172571477060057349627775)
  ·
    refine ⟨186258857215590086024441663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124172571477060057349627775 186258857215590086024441663)
    ·
      refine ⟨279388285823385129036662495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186258857215590086024441663 279388285823385129036662495)
      ·
        refine ⟨419082428735077693554993743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279388285823385129036662495 419082428735077693554993743)
        ·
          refine ⟨628623643102616540332490615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 419082428735077693554993743 628623643102616540332490615)
          ·
            refine ⟨942935464653924810498735923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 628623643102616540332490615 942935464653924810498735923)
            ·
              refine ⟨1414403196980887215748103885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 942935464653924810498735923 1414403196980887215748103885)
              ·
                refine ⟨530401198867832705905538957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1414403196980887215748103885 530401198867832705905538957)
                ·
                  refine ⟨198900449575437264714577109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 530401198867832705905538957 198900449575437264714577109)
                  ·
                    refine ⟨4661729286924310891747901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 198900449575437264714577109 4661729286924310891747901)
                    ·
                      refine ⟨1748148482596616584405463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4661729286924310891747901 1748148482596616584405463)
                      ·
                        rfl

theorem cell23_3404507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 7, 3].length) (baseStart_3404507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3404507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3404507 prefixEnd_3404507 := by exact prefixLift 3404507
  have htrace : WordTrace (prefixWord ++ tailWord_3404507) baseStart_3404507 baseEnd_3404507 := by
    simpa [prefixWord, tailWord_3404507, baseEnd_3404507] using wordTrace_append hprefix tailTrace_3404507
  have hstable : (prefixWord ++ tailWord_3404507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3404507).length < 2 ^ (prefixWord ++ tailWord_3404507).sum := by decide
  have hdescent : baseEnd_3404507 < baseStart_3404507 := by decide
  rcases family_descends (prefixWord ++ tailWord_3404507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3404541 : List Nat := [1, 4, 1, 1, 1, 1, 5, 2, 3, 1, 3]
def baseStart_3404541 : Nat := 118140960795 + 3404541 * 2 ^ 59
def prefixEnd_3404541 : Nat := 4983230072969 + 3 ^ 40 * 3404541 * 2
def baseEnd_3404541 : Nat := 1748165940938869451380307

theorem tailTrace_3404541 : CollatzResearch.WordTrace tailWord_3404541 prefixEnd_3404541 1748165940938869451380307 := by
  unfold tailWord_3404541
  simp only [CollatzResearch.WordTrace]
  refine ⟨124173811558936881156365477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82782541039291254104243651 124173811558936881156365477)
  ·
    refine ⟨23282589667300665216818527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124173811558936881156365477 23282589667300665216818527)
    ·
      refine ⟨34923884500950997825227791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23282589667300665216818527 34923884500950997825227791)
      ·
        refine ⟨52385826751426496737841687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34923884500950997825227791 52385826751426496737841687)
        ·
          refine ⟨78578740127139745106762531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52385826751426496737841687 78578740127139745106762531)
          ·
            refine ⟨117868110190709617660143797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78578740127139745106762531 117868110190709617660143797)
            ·
              refine ⟨11050135330379026655638481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 117868110190709617660143797 11050135330379026655638481)
              ·
                refine ⟨8287601497784269991728861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11050135330379026655638481 8287601497784269991728861)
                ·
                  refine ⟨3107850561669101246898323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8287601497784269991728861 3107850561669101246898323)
                  ·
                    refine ⟨4661775842503651870347485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3107850561669101246898323 4661775842503651870347485)
                    ·
                      refine ⟨1748165940938869451380307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4661775842503651870347485 1748165940938869451380307)
                      ·
                        rfl

theorem cell23_3404541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 2, 3, 1, 3].length) (baseStart_3404541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3404541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3404541 prefixEnd_3404541 := by exact prefixLift 3404541
  have htrace : WordTrace (prefixWord ++ tailWord_3404541) baseStart_3404541 baseEnd_3404541 := by
    simpa [prefixWord, tailWord_3404541, baseEnd_3404541] using wordTrace_append hprefix tailTrace_3404541
  have hstable : (prefixWord ++ tailWord_3404541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3404541).length < 2 ^ (prefixWord ++ tailWord_3404541).sum := by decide
  have hdescent : baseEnd_3404541 < baseStart_3404541 := by decide
  rcases family_descends (prefixWord ++ tailWord_3404541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3404561 : List Nat := [1, 2, 2, 1, 1, 3, 6, 1, 1, 5]
def baseStart_3404561 : Nat := 118140960795 + 3404561 * 2 ^ 59
def prefixEnd_3404561 : Nat := 4983230072969 + 3 ^ 40 * 3404561 * 2
def baseEnd_3404561 : Nat := 582725403517319791043405

theorem tailTrace_3404561 : CollatzResearch.WordTrace tailWord_3404561 prefixEnd_3404561 582725403517319791043405 := by
  unfold tailWord_3404561
  simp only [CollatzResearch.WordTrace]
  refine ⟨124174541018864424572093537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82783027345909616381395691 124174541018864424572093537)
  ·
    refine ⟨93130905764148318429070153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124174541018864424572093537 93130905764148318429070153)
    ·
      refine ⟨69848179323111238821802615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93130905764148318429070153 69848179323111238821802615)
      ·
        refine ⟨104772268984666858232703923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69848179323111238821802615 104772268984666858232703923)
        ·
          refine ⟨157158403477000287349055885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104772268984666858232703923 157158403477000287349055885)
          ·
            refine ⟨58934401303875107755895957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157158403477000287349055885 58934401303875107755895957)
            ·
              refine ⟨2762550061119145676057623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 58934401303875107755895957 2762550061119145676057623)
              ·
                refine ⟨4143825091678718514086435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2762550061119145676057623 4143825091678718514086435)
                ·
                  refine ⟨6215737637518077771129653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4143825091678718514086435 6215737637518077771129653)
                  ·
                    refine ⟨582725403517319791043405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6215737637518077771129653 582725403517319791043405)
                    ·
                      rfl

theorem cell23_3404561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 6, 1, 1, 5].length) (baseStart_3404561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3404561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3404561 prefixEnd_3404561 := by exact prefixLift 3404561
  have htrace : WordTrace (prefixWord ++ tailWord_3404561) baseStart_3404561 baseEnd_3404561 := by
    simpa [prefixWord, tailWord_3404561, baseEnd_3404561] using wordTrace_append hprefix tailTrace_3404561
  have hstable : (prefixWord ++ tailWord_3404561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3404561).length < 2 ^ (prefixWord ++ tailWord_3404561).sum := by decide
  have hdescent : baseEnd_3404561 < baseStart_3404561 := by decide
  rcases family_descends (prefixWord ++ tailWord_3404561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3404594 : List Nat := [3, 2, 1, 1, 3, 1, 3, 1, 1, 1, 6]
def baseStart_3404594 : Nat := 118140960795 + 3404594 * 2 ^ 59
def prefixEnd_3404594 : Nat := 4983230072969 + 3 ^ 40 * 3404594 * 2
def baseEnd_3404594 : Nat := 1748193155413557744017563

theorem tailTrace_3404594 : CollatzResearch.WordTrace tailWord_3404594 prefixEnd_3404594 1748193155413557744017563 := by
  unfold tailWord_3404594
  simp only [CollatzResearch.WordTrace]
  refine ⟨31043936156936217802011209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82783829751829914138696557 31043936156936217802011209)
  ·
    refine ⟨23282952117702163351508407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31043936156936217802011209 23282952117702163351508407)
    ·
      refine ⟨34924428176553245027262611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23282952117702163351508407 34924428176553245027262611)
      ·
        refine ⟨52386642264829867540893917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34924428176553245027262611 52386642264829867540893917)
        ·
          refine ⟨19644990849311200327835219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52386642264829867540893917 19644990849311200327835219)
          ·
            refine ⟨29467486273966800491752829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19644990849311200327835219 29467486273966800491752829)
            ·
              refine ⟨11050307352737550184407311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29467486273966800491752829 11050307352737550184407311)
              ·
                refine ⟨16575461029106325276610967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11050307352737550184407311 16575461029106325276610967)
                ·
                  refine ⟨24863191543659487914916451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16575461029106325276610967 24863191543659487914916451)
                  ·
                    refine ⟨37294787315489231872374677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24863191543659487914916451 37294787315489231872374677)
                    ·
                      refine ⟨1748193155413557744017563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37294787315489231872374677 1748193155413557744017563)
                      ·
                        rfl

theorem cell23_3404594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 1, 1, 1, 6].length) (baseStart_3404594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3404594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3404594 prefixEnd_3404594 := by exact prefixLift 3404594
  have htrace : WordTrace (prefixWord ++ tailWord_3404594) baseStart_3404594 baseEnd_3404594 := by
    simpa [prefixWord, tailWord_3404594, baseEnd_3404594] using wordTrace_append hprefix tailTrace_3404594
  have hstable : (prefixWord ++ tailWord_3404594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3404594).length < 2 ^ (prefixWord ++ tailWord_3404594).sum := by decide
  have hdescent : baseEnd_3404594 < baseStart_3404594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3404594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3404609 : List Nat := [1, 2, 5, 3, 1, 2, 1, 3, 1, 1, 3]
def baseStart_3404609 : Nat := 118140960795 + 3404609 * 2 ^ 59
def prefixEnd_3404609 : Nat := 4983230072969 + 3 ^ 40 * 3404609 * 2
def baseEnd_3404609 : Nat := 1748200857623375185329995

theorem tailTrace_3404609 : CollatzResearch.WordTrace tailWord_3404609 prefixEnd_3404609 1748200857623375185329995 := by
  unfold tailWord_3404609
  simp only [CollatzResearch.WordTrace]
  refine ⟨124176291722690528769840881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82784194481793685846560587 124176291722690528769840881)
  ·
    refine ⟨93132218792017896577380661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124176291722690528769840881 93132218792017896577380661)
    ·
      refine ⟨8731145511751677804129437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 93132218792017896577380661 8731145511751677804129437)
      ·
        refine ⟨3274179566906879176548539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8731145511751677804129437 3274179566906879176548539)
        ·
          refine ⟨4911269350360318764822809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3274179566906879176548539 4911269350360318764822809)
          ·
            refine ⟨3683452012770239073617107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4911269350360318764822809 3683452012770239073617107)
            ·
              refine ⟨5525178019155358610425661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3683452012770239073617107 5525178019155358610425661)
              ·
                refine ⟨2071941757183259478909623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5525178019155358610425661 2071941757183259478909623)
                ·
                  refine ⟨3107912635774889218364435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2071941757183259478909623 3107912635774889218364435)
                  ·
                    refine ⟨4661868953662333827546653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3107912635774889218364435 4661868953662333827546653)
                    ·
                      refine ⟨1748200857623375185329995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4661868953662333827546653 1748200857623375185329995)
                      ·
                        rfl

theorem cell23_3404609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_3404609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3404609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3404609 prefixEnd_3404609 := by exact prefixLift 3404609
  have htrace : WordTrace (prefixWord ++ tailWord_3404609) baseStart_3404609 baseEnd_3404609 := by
    simpa [prefixWord, tailWord_3404609, baseEnd_3404609] using wordTrace_append hprefix tailTrace_3404609
  have hstable : (prefixWord ++ tailWord_3404609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3404609).length < 2 ^ (prefixWord ++ tailWord_3404609).sum := by decide
  have hdescent : baseEnd_3404609 < baseStart_3404609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3404609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3404642 : List Nat := [3, 3, 2, 1, 3, 2, 2, 1, 2, 4]
def baseStart_3404642 : Nat := 118140960795 + 3404642 * 2 ^ 59
def prefixEnd_3404642 : Nat := 4983230072969 + 3 ^ 40 * 3404642 * 2
def baseEnd_3404642 : Nat := 582739267494991185405781

theorem tailTrace_3404642 : CollatzResearch.WordTrace tailWord_3404642 prefixEnd_3404642 582739267494991185405781 := by
  unfold tailWord_3404642
  simp only [CollatzResearch.WordTrace]
  refine ⟨31044373832892743851448045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82784996887713983603861453 31044373832892743851448045)
  ·
    refine ⟨11641640187334778944293017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31044373832892743851448045 11641640187334778944293017)
    ·
      refine ⟨8731230140501084208219763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11641640187334778944293017 8731230140501084208219763)
      ·
        refine ⟨13096845210751626312329645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8731230140501084208219763 13096845210751626312329645)
        ·
          refine ⟨4911316954031859867123617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13096845210751626312329645 4911316954031859867123617)
          ·
            refine ⟨3683487715523894900342713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4911316954031859867123617 3683487715523894900342713)
            ·
              refine ⟨2762615786642921175257035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3683487715523894900342713 2762615786642921175257035)
              ·
                refine ⟨4143923679964381762885553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2762615786642921175257035 4143923679964381762885553)
                ·
                  refine ⟨3107942759973286322164165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4143923679964381762885553 3107942759973286322164165)
                  ·
                    refine ⟨582739267494991185405781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3107942759973286322164165 582739267494991185405781)
                    ·
                      rfl

theorem cell23_3404642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_3404642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3404642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3404642 prefixEnd_3404642 := by exact prefixLift 3404642
  have htrace : WordTrace (prefixWord ++ tailWord_3404642) baseStart_3404642 baseEnd_3404642 := by
    simpa [prefixWord, tailWord_3404642, baseEnd_3404642] using wordTrace_append hprefix tailTrace_3404642
  have hstable : (prefixWord ++ tailWord_3404642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3404642).length < 2 ^ (prefixWord ++ tailWord_3404642).sum := by decide
  have hdescent : baseEnd_3404642 < baseStart_3404642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3404642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3404671 : List Nat := [1, 1, 2, 2, 1, 1, 5, 1, 3, 4, 2]
def baseStart_3404671 : Nat := 118140960795 + 3404671 * 2 ^ 59
def prefixEnd_3404671 : Nat := 4983230072969 + 3 ^ 40 * 3404671 * 2
def baseEnd_3404671 : Nat := 1748232693423953942754709

theorem tailTrace_3404671 : CollatzResearch.WordTrace tailWord_3404671 prefixEnd_3404671 1748232693423953942754709 := by
  unfold tailWord_3404671
  simp only [CollatzResearch.WordTrace]
  refine ⟨124178553048465913358597867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82785702032310608905731911 124178553048465913358597867)
  ·
    refine ⟨186267829572698870037896801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124178553048465913358597867 186267829572698870037896801)
    ·
      refine ⟨139700872179524152528422601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186267829572698870037896801 139700872179524152528422601)
      ·
        refine ⟨104775654134643114396316951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139700872179524152528422601 104775654134643114396316951)
        ·
          refine ⟨157163481201964671594475427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104775654134643114396316951 157163481201964671594475427)
          ·
            refine ⟨235745221802947007391713141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157163481201964671594475427 235745221802947007391713141)
            ·
              refine ⟨22101114544026281942973107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 235745221802947007391713141 22101114544026281942973107)
              ·
                refine ⟨33151671816039422914459661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22101114544026281942973107 33151671816039422914459661)
                ·
                  refine ⟨12431876931014783592922373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33151671816039422914459661 12431876931014783592922373)
                  ·
                    refine ⟨2330976924565271923672945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12431876931014783592922373 2330976924565271923672945)
                    ·
                      refine ⟨1748232693423953942754709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2330976924565271923672945 1748232693423953942754709)
                      ·
                        rfl

theorem cell23_3404671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 3, 4, 2].length) (baseStart_3404671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3404671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3404671 prefixEnd_3404671 := by exact prefixLift 3404671
  have htrace : WordTrace (prefixWord ++ tailWord_3404671) baseStart_3404671 baseEnd_3404671 := by
    simpa [prefixWord, tailWord_3404671, baseEnd_3404671] using wordTrace_append hprefix tailTrace_3404671
  have hstable : (prefixWord ++ tailWord_3404671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3404671).length < 2 ^ (prefixWord ++ tailWord_3404671).sum := by decide
  have hdescent : baseEnd_3404671 < baseStart_3404671 := by decide
  rcases family_descends (prefixWord ++ tailWord_3404671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3404675 : List Nat := [1, 1, 1, 3, 4, 1, 5, 1, 1, 3, 2]
def baseStart_3404675 : Nat := 118140960795 + 3404675 * 2 ^ 59
def prefixEnd_3404675 : Nat := 4983230072969 + 3 ^ 40 * 3404675 * 2
def baseEnd_3404675 : Nat := 1748234747346571927104691

theorem tailTrace_3404675 : CollatzResearch.WordTrace tailWord_3404675 prefixEnd_3404675 1748234747346571927104691 := by
  unfold tailWord_3404675
  simp only [CollatzResearch.WordTrace]
  refine ⟨124178698940451422041743479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82785799293634281361162319 124178698940451422041743479)
  ·
    refine ⟨186268048410677133062615219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124178698940451422041743479 186268048410677133062615219)
    ·
      refine ⟨279402072616015699593922829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186268048410677133062615219 279402072616015699593922829)
      ·
        refine ⟨104775777231005887347721061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 279402072616015699593922829 104775777231005887347721061)
        ·
          refine ⟨19645458230813603877697699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104775777231005887347721061 19645458230813603877697699)
          ·
            refine ⟨29468187346220405816546549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19645458230813603877697699 29468187346220405816546549)
            ·
              refine ⟨2762642563708163045301239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29468187346220405816546549 2762642563708163045301239)
              ·
                refine ⟨4143963845562244567951859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2762642563708163045301239 4143963845562244567951859)
                ·
                  refine ⟨6215945768343366851927789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4143963845562244567951859 6215945768343366851927789)
                  ·
                    refine ⟨2330979663128762569472921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6215945768343366851927789 2330979663128762569472921)
                    ·
                      refine ⟨1748234747346571927104691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2330979663128762569472921 1748234747346571927104691)
                      ·
                        rfl

theorem cell23_3404675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 5, 1, 1, 3, 2].length) (baseStart_3404675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3404675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3404675 prefixEnd_3404675 := by exact prefixLift 3404675
  have htrace : WordTrace (prefixWord ++ tailWord_3404675) baseStart_3404675 baseEnd_3404675 := by
    simpa [prefixWord, tailWord_3404675, baseEnd_3404675] using wordTrace_append hprefix tailTrace_3404675
  have hstable : (prefixWord ++ tailWord_3404675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3404675).length < 2 ^ (prefixWord ++ tailWord_3404675).sum := by decide
  have hdescent : baseEnd_3404675 < baseStart_3404675 := by decide
  rcases family_descends (prefixWord ++ tailWord_3404675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3404701 : List Nat := [1, 4, 2, 1, 2, 1, 3, 1, 2, 2, 4]
def baseStart_3404701 : Nat := 118140960795 + 3404701 * 2 ^ 59
def prefixEnd_3404701 : Nat := 4983230072969 + 3 ^ 40 * 3404701 * 2
def baseEnd_3404701 : Nat := 1748248097843588825379571

theorem tailTrace_3404701 : CollatzResearch.WordTrace tailWord_3404701 prefixEnd_3404701 1748248097843588825379571 := by
  unfold tailWord_3404701
  simp only [CollatzResearch.WordTrace]
  refine ⟨124179647238357228482189957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82786431492238152321459971 124179647238357228482189957)
  ·
    refine ⟨23283683857191980340410617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124179647238357228482189957 23283683857191980340410617)
    ·
      refine ⟨17462762892893985255307963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23283683857191980340410617 17462762892893985255307963)
      ·
        refine ⟨26194144339340977882961945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17462762892893985255307963 26194144339340977882961945)
        ·
          refine ⟨19645608254505733412221459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26194144339340977882961945 19645608254505733412221459)
          ·
            refine ⟨29468412381758600118332189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19645608254505733412221459 29468412381758600118332189)
            ·
              refine ⟨11050654643159475044374571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29468412381758600118332189 11050654643159475044374571)
              ·
                refine ⟨16575981964739212566561857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11050654643159475044374571 16575981964739212566561857)
                ·
                  refine ⟨12431986473554409424921393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16575981964739212566561857 12431986473554409424921393)
                  ·
                    refine ⟨9323989855165807068691045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12431986473554409424921393 9323989855165807068691045)
                    ·
                      refine ⟨1748248097843588825379571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9323989855165807068691045 1748248097843588825379571)
                      ·
                        rfl

theorem cell23_3404701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_3404701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3404701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3404701 prefixEnd_3404701 := by exact prefixLift 3404701
  have htrace : WordTrace (prefixWord ++ tailWord_3404701) baseStart_3404701 baseEnd_3404701 := by
    simpa [prefixWord, tailWord_3404701, baseEnd_3404701] using wordTrace_append hprefix tailTrace_3404701
  have hstable : (prefixWord ++ tailWord_3404701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3404701).length < 2 ^ (prefixWord ++ tailWord_3404701).sum := by decide
  have hdescent : baseEnd_3404701 < baseStart_3404701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3404701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3404705 : List Nat := [1, 2, 3, 4, 1, 2, 2, 1, 1, 4, 2]
def baseStart_3404705 : Nat := 118140960795 + 3404705 * 2 ^ 59
def prefixEnd_3404705 : Nat := 4983230072969 + 3 ^ 40 * 3404705 * 2
def baseEnd_3404705 : Nat := 1748250151766206809729553

theorem tailTrace_3404705 : CollatzResearch.WordTrace tailWord_3404705 prefixEnd_3404705 1748250151766206809729553 := by
  unfold tailWord_3404705
  simp only [CollatzResearch.WordTrace]
  refine ⟨124179793130342737165335569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82786528753561824776890379 124179793130342737165335569)
  ·
    refine ⟨93134844847757052874001677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124179793130342737165335569 93134844847757052874001677)
    ·
      refine ⟨34925566817908894827750629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93134844847757052874001677 34925566817908894827750629)
      ·
        refine ⟨6548543778357917780203243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34925566817908894827750629 6548543778357917780203243)
        ·
          refine ⟨9822815667536876670304865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6548543778357917780203243 9822815667536876670304865)
          ·
            refine ⟨7367111750652657502728649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9822815667536876670304865 7367111750652657502728649)
            ·
              refine ⟨5525333812989493127046487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7367111750652657502728649 5525333812989493127046487)
              ·
                refine ⟨8288000719484239690569731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5525333812989493127046487 8288000719484239690569731)
                ·
                  refine ⟨12432001079226359535854597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8288000719484239690569731 12432001079226359535854597)
                  ·
                    refine ⟨2331000202354942412972737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12432001079226359535854597 2331000202354942412972737)
                    ·
                      refine ⟨1748250151766206809729553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2331000202354942412972737 1748250151766206809729553)
                      ·
                        rfl

theorem cell23_3404705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_3404705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3404705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3404705 prefixEnd_3404705 := by exact prefixLift 3404705
  have htrace : WordTrace (prefixWord ++ tailWord_3404705) baseStart_3404705 baseEnd_3404705 := by
    simpa [prefixWord, tailWord_3404705, baseEnd_3404705] using wordTrace_append hprefix tailTrace_3404705
  have hstable : (prefixWord ++ tailWord_3404705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3404705).length < 2 ^ (prefixWord ++ tailWord_3404705).sum := by decide
  have hdescent : baseEnd_3404705 < baseStart_3404705 := by decide
  rcases family_descends (prefixWord ++ tailWord_3404705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3404726 : List Nat := [5, 1, 4, 1, 1, 1, 1, 3, 1, 3, 2]
def baseStart_3404726 : Nat := 118140960795 + 3404726 * 2 ^ 59
def prefixEnd_3404726 : Nat := 4983230072969 + 3 ^ 40 * 3404726 * 2
def baseEnd_3404726 : Nat := 1748260934859951227566957

theorem tailTrace_3404726 : CollatzResearch.WordTrace tailWord_3404726 prefixEnd_3404726 1748260934859951227566957 := by
  unfold tailWord_3404726
  simp only [CollatzResearch.WordTrace]
  refine ⟨7761284941454166109490627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 82787039375511105167900021 7761284941454166109490627)
  ·
    refine ⟨11641927412181249164235941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7761284941454166109490627 11641927412181249164235941)
    ·
      refine ⟨2182861389783984218294239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11641927412181249164235941 2182861389783984218294239)
      ·
        refine ⟨3274292084675976327441359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2182861389783984218294239 3274292084675976327441359)
        ·
          refine ⟨4911438127013964491162039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3274292084675976327441359 4911438127013964491162039)
          ·
            refine ⟨7367157190520946736743059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4911438127013964491162039 7367157190520946736743059)
            ·
              refine ⟨11050735785781420105114589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7367157190520946736743059 11050735785781420105114589)
              ·
                refine ⟨4144025919668032539417971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11050735785781420105114589 4144025919668032539417971)
                ·
                  refine ⟨6216038879502048809126957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4144025919668032539417971 6216038879502048809126957)
                  ·
                    refine ⟨2331014579813268303422609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6216038879502048809126957 2331014579813268303422609)
                    ·
                      refine ⟨1748260934859951227566957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2331014579813268303422609 1748260934859951227566957)
                      ·
                        rfl

theorem cell23_3404726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_3404726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3404726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3404726 prefixEnd_3404726 := by exact prefixLift 3404726
  have htrace : WordTrace (prefixWord ++ tailWord_3404726) baseStart_3404726 baseEnd_3404726 := by
    simpa [prefixWord, tailWord_3404726, baseEnd_3404726] using wordTrace_append hprefix tailTrace_3404726
  have hstable : (prefixWord ++ tailWord_3404726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3404726).length < 2 ^ (prefixWord ++ tailWord_3404726).sum := by decide
  have hdescent : baseEnd_3404726 < baseStart_3404726 := by decide
  rcases family_descends (prefixWord ++ tailWord_3404726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3404728 : List Nat := [2, 1, 2, 1, 2, 5, 2, 3, 5]
def baseStart_3404728 : Nat := 118140960795 + 3404728 * 2 ^ 59
def prefixEnd_3404728 : Nat := 4983230072969 + 3 ^ 40 * 3404728 * 2
def baseEnd_3404728 : Nat := 194251329091251135526883

theorem tailTrace_3404728 : CollatzResearch.WordTrace tailWord_3404728 prefixEnd_3404728 194251329091251135526883 := by
  unfold tailWord_3404728
  simp only [CollatzResearch.WordTrace]
  refine ⟨62090316004629706046711419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82787088006172941395615225 62090316004629706046711419)
  ·
    refine ⟨93135474006944559070067129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62090316004629706046711419 93135474006944559070067129)
    ·
      refine ⟨69851605505208419302550347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93135474006944559070067129 69851605505208419302550347)
      ·
        refine ⟨104777408257812628953825521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69851605505208419302550347 104777408257812628953825521)
        ·
          refine ⟨78583056193359471715369141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104777408257812628953825521 78583056193359471715369141)
          ·
            refine ⟨7367161518127450473315857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 78583056193359471715369141 7367161518127450473315857)
            ·
              refine ⟨5525371138595587854986893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7367161518127450473315857 5525371138595587854986893)
              ·
                refine ⟨2072014176973345445620085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5525371138595587854986893 2072014176973345445620085)
                ·
                  refine ⟨194251329091251135526883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2072014176973345445620085 194251329091251135526883)
                  ·
                    rfl

theorem cell23_3404728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 3, 5].length) (baseStart_3404728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3404728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3404728 prefixEnd_3404728 := by exact prefixLift 3404728
  have htrace : WordTrace (prefixWord ++ tailWord_3404728) baseStart_3404728 baseEnd_3404728 := by
    simpa [prefixWord, tailWord_3404728, baseEnd_3404728] using wordTrace_append hprefix tailTrace_3404728
  have hstable : (prefixWord ++ tailWord_3404728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3404728).length < 2 ^ (prefixWord ++ tailWord_3404728).sum := by decide
  have hdescent : baseEnd_3404728 < baseStart_3404728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3404728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3404758 : List Nat := [5, 2, 1, 1, 2, 1, 1, 2, 1, 7]
def baseStart_3404758 : Nat := 118140960795 + 3404758 * 2 ^ 59
def prefixEnd_3404758 : Nat := 4983230072969 + 3 ^ 40 * 3404758 * 2
def baseEnd_3404758 : Nat := 582759122080298367455603

theorem tailTrace_3404758 : CollatzResearch.WordTrace tailWord_3404758 prefixEnd_3404758 582759122080298367455603 := by
  unfold tailWord_3404758
  simp only [CollatzResearch.WordTrace]
  refine ⟨7761357887446920451063433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 82787817466100484811343285 7761357887446920451063433)
  ·
    refine ⟨5821018415585190338297575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7761357887446920451063433 5821018415585190338297575)
    ·
      refine ⟨8731527623377785507446363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5821018415585190338297575 8731527623377785507446363)
      ·
        refine ⟨13097291435066678261169545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8731527623377785507446363 13097291435066678261169545)
        ·
          refine ⟨9822968576300008695877159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13097291435066678261169545 9822968576300008695877159)
          ·
            refine ⟨14734452864450013043815739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9822968576300008695877159 14734452864450013043815739)
            ·
              refine ⟨22101679296675019565723609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14734452864450013043815739 22101679296675019565723609)
              ·
                refine ⟨16576259472506264674292707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22101679296675019565723609 16576259472506264674292707)
                ·
                  refine ⟨24864389208759397011439061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16576259472506264674292707 24864389208759397011439061)
                  ·
                    refine ⟨582759122080298367455603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24864389208759397011439061 582759122080298367455603)
                    ·
                      rfl

theorem cell23_3404758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_3404758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3404758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3404758 prefixEnd_3404758 := by exact prefixLift 3404758
  have htrace : WordTrace (prefixWord ++ tailWord_3404758) baseStart_3404758 baseEnd_3404758 := by
    simpa [prefixWord, tailWord_3404758, baseEnd_3404758] using wordTrace_append hprefix tailTrace_3404758
  have hstable : (prefixWord ++ tailWord_3404758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3404758).length < 2 ^ (prefixWord ++ tailWord_3404758).sum := by decide
  have hdescent : baseEnd_3404758 < baseStart_3404758 := by decide
  rcases family_descends (prefixWord ++ tailWord_3404758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3404761 : List Nat := [1, 2, 1, 2, 5, 1, 1, 2, 1, 3, 4]
def baseStart_3404761 : Nat := 118140960795 + 3404761 * 2 ^ 59
def prefixEnd_3404761 : Nat := 4983230072969 + 3 ^ 40 * 3404761 * 2
def baseEnd_3404761 : Nat := 1748278906682858590629295

theorem tailTrace_3404761 : CollatzResearch.WordTrace tailWord_3404761 prefixEnd_3404761 1748278906682858590629295 := by
  unfold tailWord_3404761
  simp only [CollatzResearch.WordTrace]
  refine ⟨124181835618139858729374137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82787890412093239152916091 124181835618139858729374137)
  ·
    refine ⟨93136376713604894047030603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124181835618139858729374137 93136376713604894047030603)
    ·
      refine ⟨139704565070407341070545905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93136376713604894047030603 139704565070407341070545905)
      ·
        refine ⟨104778423802805505802909429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139704565070407341070545905 104778423802805505802909429)
        ·
          refine ⟨9822977231513016169022759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 104778423802805505802909429 9822977231513016169022759)
          ·
            refine ⟨14734465847269524253534139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9822977231513016169022759 14734465847269524253534139)
            ·
              refine ⟨22101698770904286380301209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14734465847269524253534139 22101698770904286380301209)
              ·
                refine ⟨16576274078178214785225907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22101698770904286380301209 16576274078178214785225907)
                ·
                  refine ⟨24864411117267322177838861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16576274078178214785225907 24864411117267322177838861)
                  ·
                    refine ⟨9324154168975245816689573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24864411117267322177838861 9324154168975245816689573)
                    ·
                      refine ⟨1748278906682858590629295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9324154168975245816689573 1748278906682858590629295)
                      ·
                        rfl

theorem cell23_3404761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 2, 1, 3, 4].length) (baseStart_3404761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3404761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3404761 prefixEnd_3404761 := by exact prefixLift 3404761
  have htrace : WordTrace (prefixWord ++ tailWord_3404761) baseStart_3404761 baseEnd_3404761 := by
    simpa [prefixWord, tailWord_3404761, baseEnd_3404761] using wordTrace_append hprefix tailTrace_3404761
  have hstable : (prefixWord ++ tailWord_3404761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3404761).length < 2 ^ (prefixWord ++ tailWord_3404761).sum := by decide
  have hdescent : baseEnd_3404761 < baseStart_3404761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3404761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3404801 : List Nat := [1, 2, 4, 1, 2, 2, 2, 1, 8]
def baseStart_3404801 : Nat := 118140960795 + 3404801 * 2 ^ 59
def prefixEnd_3404801 : Nat := 4983230072969 + 3 ^ 40 * 3404801 * 2
def baseEnd_3404801 : Nat := 194255493989893159347679

theorem tailTrace_3404801 : CollatzResearch.WordTrace tailWord_3404801 prefixEnd_3404801 194255493989893159347679 := by
  unfold tailWord_3404801
  simp only [CollatzResearch.WordTrace]
  refine ⟨124183294537994945560830257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82788863025329963707220171 124183294537994945560830257)
  ·
    refine ⟨93137470903496209170622693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124183294537994945560830257 93137470903496209170622693)
    ·
      refine ⟨17463275794405539219491755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93137470903496209170622693 17463275794405539219491755)
      ·
        refine ⟨26194913691608308829237633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17463275794405539219491755 26194913691608308829237633)
        ·
          refine ⟨19646185268706231621928225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26194913691608308829237633 19646185268706231621928225)
          ·
            refine ⟨14734638951529673716446169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19646185268706231621928225 14734638951529673716446169)
            ·
              refine ⟨11050979213647255287334627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14734638951529673716446169 11050979213647255287334627)
              ·
                refine ⟨16576468820470882931001941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11050979213647255287334627 16576468820470882931001941)
                ·
                  refine ⟨194255493989893159347679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16576468820470882931001941 194255493989893159347679)
                  ·
                    rfl

theorem cell23_3404801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 1, 8].length) (baseStart_3404801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3404801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3404801 prefixEnd_3404801 := by exact prefixLift 3404801
  have htrace : WordTrace (prefixWord ++ tailWord_3404801) baseStart_3404801 baseEnd_3404801 := by
    simpa [prefixWord, tailWord_3404801, baseEnd_3404801] using wordTrace_append hprefix tailTrace_3404801
  have hstable : (prefixWord ++ tailWord_3404801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3404801).length < 2 ^ (prefixWord ++ tailWord_3404801).sum := by decide
  have hdescent : baseEnd_3404801 < baseStart_3404801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3404801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3404832 : List Nat := [2, 1, 1, 7, 1, 1, 2, 1, 2, 2, 3]
def baseStart_3404832 : Nat := 118140960795 + 3404832 * 2 ^ 59
def prefixEnd_3404832 : Nat := 4983230072969 + 3 ^ 40 * 3404832 * 2
def baseEnd_3404832 : Nat := 1748315363809327812841469

theorem tailTrace_3404832 : CollatzResearch.WordTrace tailWord_3404832 prefixEnd_3404832 1748315363809327812841469 := by
  unfold tailWord_3404832
  simp only [CollatzResearch.WordTrace]
  refine ⟨62092212600441318927604375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82789616800588425236805833 62092212600441318927604375)
  ·
    refine ⟨93138318900661978391406563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62092212600441318927604375 93138318900661978391406563)
    ·
      refine ⟨139707478350992967587109845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93138318900661978391406563 139707478350992967587109845)
      ·
        refine ⟨3274394023851397677822887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 139707478350992967587109845 3274394023851397677822887)
        ·
          refine ⟨4911591035777096516734331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3274394023851397677822887 4911591035777096516734331)
          ·
            refine ⟨7367386553665644775101497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4911591035777096516734331 7367386553665644775101497)
            ·
              refine ⟨5525539915249233581326123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7367386553665644775101497 5525539915249233581326123)
              ·
                refine ⟨8288309872873850371989185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5525539915249233581326123 8288309872873850371989185)
                ·
                  refine ⟨6216232404655387778991889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8288309872873850371989185 6216232404655387778991889)
                  ·
                    refine ⟨4662174303491540834243917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6216232404655387778991889 4662174303491540834243917)
                    ·
                      refine ⟨1748315363809327812841469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4662174303491540834243917 1748315363809327812841469)
                      ·
                        rfl

theorem cell23_3404832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_3404832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3404832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3404832 prefixEnd_3404832 := by exact prefixLift 3404832
  have htrace : WordTrace (prefixWord ++ tailWord_3404832) baseStart_3404832 baseEnd_3404832 := by
    simpa [prefixWord, tailWord_3404832, baseEnd_3404832] using wordTrace_append hprefix tailTrace_3404832
  have hstable : (prefixWord ++ tailWord_3404832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3404832).length < 2 ^ (prefixWord ++ tailWord_3404832).sum := by decide
  have hdescent : baseEnd_3404832 < baseStart_3404832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3404832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3404878 : List Nat := [4, 1, 1, 1, 1, 3, 4, 1, 1, 6]
def baseStart_3404878 : Nat := 118140960795 + 3404878 * 2 ^ 59
def prefixEnd_3404878 : Nat := 4983230072969 + 3 ^ 40 * 3404878 * 2
def baseEnd_3404878 : Nat := 582779661306478210955419

theorem tailTrace_3404878 : CollatzResearch.WordTrace tailWord_3404878 prefixEnd_3404878 582779661306478210955419 := by
  unfold tailWord_3404878
  simp only [CollatzResearch.WordTrace]
  refine ⟨15523262869839498463922911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82790735305810658474255525 15523262869839498463922911)
  ·
    refine ⟨23284894304759247695884367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15523262869839498463922911 23284894304759247695884367)
    ·
      refine ⟨34927341457138871543826551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23284894304759247695884367 34927341457138871543826551)
      ·
        refine ⟨52391012185708307315739827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34927341457138871543826551 52391012185708307315739827)
        ·
          refine ⟨78586518278562460973609741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52391012185708307315739827 78586518278562460973609741)
          ·
            refine ⟨29469944354460922865103653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78586518278562460973609741 29469944354460922865103653)
            ·
              refine ⟨5525614566461423037206935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29469944354460922865103653 5525614566461423037206935)
              ·
                refine ⟨8288421849692134555810403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5525614566461423037206935 8288421849692134555810403)
                ·
                  refine ⟨12432632774538201833715605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8288421849692134555810403 12432632774538201833715605)
                  ·
                    refine ⟨582779661306478210955419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12432632774538201833715605 582779661306478210955419)
                    ·
                      rfl

theorem cell23_3404878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 1, 1, 6].length) (baseStart_3404878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3404878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3404878 prefixEnd_3404878 := by exact prefixLift 3404878
  have htrace : WordTrace (prefixWord ++ tailWord_3404878) baseStart_3404878 baseEnd_3404878 := by
    simpa [prefixWord, tailWord_3404878, baseEnd_3404878] using wordTrace_append hprefix tailTrace_3404878
  have hstable : (prefixWord ++ tailWord_3404878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3404878).length < 2 ^ (prefixWord ++ tailWord_3404878).sum := by decide
  have hdescent : baseEnd_3404878 < baseStart_3404878 := by decide
  rcases family_descends (prefixWord ++ tailWord_3404878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3404881 : List Nat := [1, 2, 2, 1, 3, 1, 2, 3, 1, 1, 6]
def baseStart_3404881 : Nat := 118140960795 + 3404881 * 2 ^ 59
def prefixEnd_3404881 : Nat := 4983230072969 + 3 ^ 40 * 3404881 * 2
def baseEnd_3404881 : Nat := 1748340524361398121128743

theorem tailTrace_3404881 : CollatzResearch.WordTrace tailWord_3404881 prefixEnd_3404881 1748340524361398121128743 := by
  unfold tailWord_3404881
  simp only [CollatzResearch.WordTrace]
  refine ⟨124186212377705119223742497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82790808251803412815828331 124186212377705119223742497)
  ·
    refine ⟨93139659283278839417806873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124186212377705119223742497 93139659283278839417806873)
    ·
      refine ⟨69854744462459129563355155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93139659283278839417806873 69854744462459129563355155)
      ·
        refine ⟨104782116693688694345032733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69854744462459129563355155 104782116693688694345032733)
        ·
          refine ⟨39293293760133260379387275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104782116693688694345032733 39293293760133260379387275)
          ·
            refine ⟨58939940640199890569080913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39293293760133260379387275 58939940640199890569080913)
            ·
              refine ⟨44204955480149917926810685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58939940640199890569080913 44204955480149917926810685)
              ·
                refine ⟨16576858305056219222554007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44204955480149917926810685 16576858305056219222554007)
                ·
                  refine ⟨24865287457584328833831011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16576858305056219222554007 24865287457584328833831011)
                  ·
                    refine ⟨37297931186376493250746517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24865287457584328833831011 37297931186376493250746517)
                    ·
                      refine ⟨1748340524361398121128743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37297931186376493250746517 1748340524361398121128743)
                      ·
                        rfl

theorem cell23_3404881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 3, 1, 1, 6].length) (baseStart_3404881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3404881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3404881 prefixEnd_3404881 := by exact prefixLift 3404881
  have htrace : WordTrace (prefixWord ++ tailWord_3404881) baseStart_3404881 baseEnd_3404881 := by
    simpa [prefixWord, tailWord_3404881, baseEnd_3404881] using wordTrace_append hprefix tailTrace_3404881
  have hstable : (prefixWord ++ tailWord_3404881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3404881).length < 2 ^ (prefixWord ++ tailWord_3404881).sum := by decide
  have hdescent : baseEnd_3404881 < baseStart_3404881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3404881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3404888 : List Nat := [2, 1, 2, 2, 1, 3, 1, 3, 3, 2, 3]
def baseStart_3404888 : Nat := 118140960795 + 3404888 * 2 ^ 59
def prefixEnd_3404888 : Nat := 4983230072969 + 3 ^ 40 * 3404888 * 2
def baseEnd_3404888 : Nat := 1748344118725979593741211

theorem tailTrace_3404888 : CollatzResearch.WordTrace tailWord_3404888 prefixEnd_3404888 1748344118725979593741211 := by
  unfold tailWord_3404888
  simp only [CollatzResearch.WordTrace]
  refine ⟨62093233844339879709623659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82790978459119839612831545 62093233844339879709623659)
  ·
    refine ⟨93139850766509819564435489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62093233844339879709623659 93139850766509819564435489)
    ·
      refine ⟨69854888074882364673326617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93139850766509819564435489 69854888074882364673326617)
      ·
        refine ⟨52391166056161773504994963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69854888074882364673326617 52391166056161773504994963)
        ·
          refine ⟨78586749084242660257492445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52391166056161773504994963 78586749084242660257492445)
          ·
            refine ⟨29470030906590997596559667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78586749084242660257492445 29470030906590997596559667)
            ·
              refine ⟨44205046359886496394839501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29470030906590997596559667 44205046359886496394839501)
              ·
                refine ⟨16576892384957436148064813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44205046359886496394839501 16576892384957436148064813)
                ·
                  refine ⟨6216334644359038555524305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16576892384957436148064813 6216334644359038555524305)
                  ·
                    refine ⟨4662250983269278916643229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6216334644359038555524305 4662250983269278916643229)
                    ·
                      refine ⟨1748344118725979593741211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4662250983269278916643229 1748344118725979593741211)
                      ·
                        rfl

theorem cell23_3404888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 3, 3, 2, 3].length) (baseStart_3404888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3404888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3404888 prefixEnd_3404888 := by exact prefixLift 3404888
  have htrace : WordTrace (prefixWord ++ tailWord_3404888) baseStart_3404888 baseEnd_3404888 := by
    simpa [prefixWord, tailWord_3404888, baseEnd_3404888] using wordTrace_append hprefix tailTrace_3404888
  have hstable : (prefixWord ++ tailWord_3404888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3404888).length < 2 ^ (prefixWord ++ tailWord_3404888).sum := by decide
  have hdescent : baseEnd_3404888 < baseStart_3404888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3404888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3404905 : List Nat := [1, 2, 1, 1, 1, 7, 1, 3, 1, 2, 3]
def baseStart_3404905 : Nat := 118140960795 + 3404905 * 2 ^ 59
def prefixEnd_3404905 : Nat := 4983230072969 + 3 ^ 40 * 3404905 * 2
def baseEnd_3404905 : Nat := 1748352847897106027228633

theorem tailTrace_3404905 : CollatzResearch.WordTrace tailWord_3404905 prefixEnd_3404905 1748352847897106027228633 := by
  unfold tailWord_3404905
  simp only [CollatzResearch.WordTrace]
  refine ⟨124187087729618171322616169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82791391819745447548410779 124187087729618171322616169)
  ·
    refine ⟨93140315797213628491962127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124187087729618171322616169 93140315797213628491962127)
    ·
      refine ⟨139710473695820442737943191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93140315797213628491962127 139710473695820442737943191)
      ·
        refine ⟨209565710543730664106914787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139710473695820442737943191 209565710543730664106914787)
        ·
          refine ⟨314348565815595996160372181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209565710543730664106914787 314348565815595996160372181)
          ·
            refine ⟨7367544511303031160008723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 314348565815595996160372181 7367544511303031160008723)
            ·
              refine ⟨11051316766954546740013085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7367544511303031160008723 11051316766954546740013085)
              ·
                refine ⟨4144243787607955027504907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11051316766954546740013085 4144243787607955027504907)
                ·
                  refine ⟨6216365681411932541257361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4144243787607955027504907 6216365681411932541257361)
                  ·
                    refine ⟨4662274261058949405943021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6216365681411932541257361 4662274261058949405943021)
                    ·
                      refine ⟨1748352847897106027228633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4662274261058949405943021 1748352847897106027228633)
                      ·
                        rfl

theorem cell23_3404905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 3, 1, 2, 3].length) (baseStart_3404905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3404905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3404905 prefixEnd_3404905 := by exact prefixLift 3404905
  have htrace : WordTrace (prefixWord ++ tailWord_3404905) baseStart_3404905 baseEnd_3404905 := by
    simpa [prefixWord, tailWord_3404905, baseEnd_3404905] using wordTrace_append hprefix tailTrace_3404905
  have hstable : (prefixWord ++ tailWord_3404905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3404905).length < 2 ^ (prefixWord ++ tailWord_3404905).sum := by decide
  have hdescent : baseEnd_3404905 < baseStart_3404905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3404905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3404996 : List Nat := [2, 3, 3, 1, 3, 2, 1, 2, 1, 3, 2]
def baseStart_3404996 : Nat := 118140960795 + 3404996 * 2 ^ 59
def prefixEnd_3404996 : Nat := 4983230072969 + 3 ^ 40 * 3404996 * 2
def baseEnd_3404996 : Nat := 1748399574636665171190715

theorem tailTrace_3404996 : CollatzResearch.WordTrace tailWord_3404996 prefixEnd_3404996 1748399574636665171190715 := by
  unfold tailWord_3404996
  simp only [CollatzResearch.WordTrace]
  refine ⟨62095203386144246932089421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82793604514858995909452561 62095203386144246932089421)
  ·
    refine ⟨23285701269804092599533533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62095203386144246932089421 23285701269804092599533533)
    ·
      refine ⟨8732137976176534724825075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23285701269804092599533533 8732137976176534724825075)
      ·
        refine ⟨13098206964264802087237613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8732137976176534724825075 13098206964264802087237613)
        ·
          refine ⟨4911827611599300782714105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13098206964264802087237613 4911827611599300782714105)
          ·
            refine ⟨3683870708699475587035579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4911827611599300782714105 3683870708699475587035579)
            ·
              refine ⟨5525806063049213380553369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3683870708699475587035579 5525806063049213380553369)
              ·
                refine ⟨4144354547286910035415027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5525806063049213380553369 4144354547286910035415027)
                ·
                  refine ⟨6216531820930365053122541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4144354547286910035415027 6216531820930365053122541)
                  ·
                    refine ⟨2331199432848886894920953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6216531820930365053122541 2331199432848886894920953)
                    ·
                      refine ⟨1748399574636665171190715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2331199432848886894920953 1748399574636665171190715)
                      ·
                        rfl

theorem cell23_3404996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 2, 1, 3, 2].length) (baseStart_3404996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3404996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3404996 prefixEnd_3404996 := by exact prefixLift 3404996
  have htrace : WordTrace (prefixWord ++ tailWord_3404996) baseStart_3404996 baseEnd_3404996 := by
    simpa [prefixWord, tailWord_3404996, baseEnd_3404996] using wordTrace_append hprefix tailTrace_3404996
  have hstable : (prefixWord ++ tailWord_3404996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3404996).length < 2 ^ (prefixWord ++ tailWord_3404996).sum := by decide
  have hdescent : baseEnd_3404996 < baseStart_3404996 := by decide
  rcases family_descends (prefixWord ++ tailWord_3404996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3405035 : List Nat := [1, 1, 1, 1, 2, 6, 1, 1, 2, 5, 2]
def baseStart_3405035 : Nat := 118140960795 + 3405035 * 2 ^ 59
def prefixEnd_3405035 : Nat := 4983230072969 + 3 ^ 40 * 3405035 * 2
def baseEnd_3405035 : Nat := 1748419600382190518603035

theorem tailTrace_3405035 : CollatzResearch.WordTrace tailWord_3405035 prefixEnd_3405035 1748419600382190518603035 := by
  unfold tailWord_3405035
  simp only [CollatzResearch.WordTrace]
  refine ⟨124191829219147203524848559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82794552812764802349899039 124191829219147203524848559)
  ·
    refine ⟨186287743828720805287272839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124191829219147203524848559 186287743828720805287272839)
    ·
      refine ⟨279431615743081207930909259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186287743828720805287272839 279431615743081207930909259)
      ·
        refine ⟨419147423614621811896363889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279431615743081207930909259 419147423614621811896363889)
        ·
          refine ⟨314360567710966358922272917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 419147423614621811896363889 314360567710966358922272917)
          ·
            refine ⟨14735651611451548074481543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 314360567710966358922272917 14735651611451548074481543)
            ·
              refine ⟨22103477417177322111722315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14735651611451548074481543 22103477417177322111722315)
              ·
                refine ⟨33155216125765983167583473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22103477417177322111722315 33155216125765983167583473)
                ·
                  refine ⟨24866412094324487375687605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33155216125765983167583473 24866412094324487375687605)
                  ·
                    refine ⟨2331226133842920691470713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24866412094324487375687605 2331226133842920691470713)
                    ·
                      refine ⟨1748419600382190518603035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2331226133842920691470713 1748419600382190518603035)
                      ·
                        rfl

theorem cell23_3405035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 2, 5, 2].length) (baseStart_3405035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3405035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3405035 prefixEnd_3405035 := by exact prefixLift 3405035
  have htrace : WordTrace (prefixWord ++ tailWord_3405035) baseStart_3405035 baseEnd_3405035 := by
    simpa [prefixWord, tailWord_3405035, baseEnd_3405035] using wordTrace_append hprefix tailTrace_3405035
  have hstable : (prefixWord ++ tailWord_3405035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3405035).length < 2 ^ (prefixWord ++ tailWord_3405035).sum := by decide
  have hdescent : baseEnd_3405035 < baseStart_3405035 := by decide
  rcases family_descends (prefixWord ++ tailWord_3405035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3405042 : List Nat := [3, 2, 1, 3, 3, 1, 1, 1, 2, 3, 3]
def baseStart_3405042 : Nat := 118140960795 + 3405042 * 2 ^ 59
def prefixEnd_3405042 : Nat := 4983230072969 + 3 ^ 40 * 3405042 * 2
def baseEnd_3405042 : Nat := 1748423194746771991215503

theorem tailTrace_3405042 : CollatzResearch.WordTrace tailWord_3405042 prefixEnd_3405042 1748423194746771991215503 := by
  unfold tailWord_3405042
  simp only [CollatzResearch.WordTrace]
  refine ⟨31048021132530460930088345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82794723020081229146902253 31048021132530460930088345)
  ·
    refine ⟨23286015849397845697566259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31048021132530460930088345 23286015849397845697566259)
    ·
      refine ⟨34929023774096768546349389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23286015849397845697566259 34929023774096768546349389)
      ·
        refine ⟨13098383915286288204881021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34929023774096768546349389 13098383915286288204881021)
        ·
          refine ⟨4911893968232358076830383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13098383915286288204881021 4911893968232358076830383)
          ·
            refine ⟨7367840952348537115245575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4911893968232358076830383 7367840952348537115245575)
            ·
              refine ⟨11051761428522805672868363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7367840952348537115245575 11051761428522805672868363)
              ·
                refine ⟨16577642142784208509302545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11051761428522805672868363 16577642142784208509302545)
                ·
                  refine ⟨12433231607088156381976909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16577642142784208509302545 12433231607088156381976909)
                  ·
                    refine ⟨4662461852658058643241341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12433231607088156381976909 4662461852658058643241341)
                    ·
                      refine ⟨1748423194746771991215503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4662461852658058643241341 1748423194746771991215503)
                      ·
                        rfl

theorem cell23_3405042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_3405042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3405042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3405042 prefixEnd_3405042 := by exact prefixLift 3405042
  have htrace : WordTrace (prefixWord ++ tailWord_3405042) baseStart_3405042 baseEnd_3405042 := by
    simpa [prefixWord, tailWord_3405042, baseEnd_3405042] using wordTrace_append hprefix tailTrace_3405042
  have hstable : (prefixWord ++ tailWord_3405042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3405042).length < 2 ^ (prefixWord ++ tailWord_3405042).sum := by decide
  have hdescent : baseEnd_3405042 < baseStart_3405042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3405042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3405065 : List Nat := [1, 2, 1, 1, 3, 3, 1, 2, 1, 6, 2]
def baseStart_3405065 : Nat := 118140960795 + 3405065 * 2 ^ 59
def prefixEnd_3405065 : Nat := 4983230072969 + 3 ^ 40 * 3405065 * 2
def baseEnd_3405065 : Nat := 1748435004801825401227897

theorem tailTrace_3405065 : CollatzResearch.WordTrace tailWord_3405065 prefixEnd_3405065 1748435004801825401227897 := by
  unfold tailWord_3405065
  simp only [CollatzResearch.WordTrace]
  refine ⟨124192923409038518648440649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82795282272692345765627099 124192923409038518648440649)
  ·
    refine ⟨93144692556778888986330487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124192923409038518648440649 93144692556778888986330487)
    ·
      refine ⟨139717038835168333479495731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93144692556778888986330487 139717038835168333479495731)
      ·
        refine ⟨209575558252752500219243597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139717038835168333479495731 209575558252752500219243597)
        ·
          refine ⟨78590834344782187582216349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 209575558252752500219243597 78590834344782187582216349)
          ·
            refine ⟨29471562879293320343331131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78590834344782187582216349 29471562879293320343331131)
            ·
              refine ⟨44207344318939980514996697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29471562879293320343331131 44207344318939980514996697)
              ·
                refine ⟨33155508239204985386247523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44207344318939980514996697 33155508239204985386247523)
                ·
                  refine ⟨49733262358807478079371285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33155508239204985386247523 49733262358807478079371285)
                  ·
                    refine ⟨2331246673069100534970529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 49733262358807478079371285 2331246673069100534970529)
                    ·
                      refine ⟨1748435004801825401227897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2331246673069100534970529 1748435004801825401227897)
                      ·
                        rfl

theorem cell23_3405065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 6, 2].length) (baseStart_3405065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3405065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3405065 prefixEnd_3405065 := by exact prefixLift 3405065
  have htrace : WordTrace (prefixWord ++ tailWord_3405065) baseStart_3405065 baseEnd_3405065 := by
    simpa [prefixWord, tailWord_3405065, baseEnd_3405065] using wordTrace_append hprefix tailTrace_3405065
  have hstable : (prefixWord ++ tailWord_3405065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3405065).length < 2 ^ (prefixWord ++ tailWord_3405065).sum := by decide
  have hdescent : baseEnd_3405065 < baseStart_3405065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3405065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3405082 : List Nat := [3, 1, 1, 3, 3, 1, 1, 2, 2, 4, 2]
def baseStart_3405082 : Nat := 118140960795 + 3405082 * 2 ^ 59
def prefixEnd_3405082 : Nat := 4983230072969 + 3 ^ 40 * 3405082 * 2
def baseEnd_3405082 : Nat := 1748443733972951834715319

theorem tailTrace_3405082 : CollatzResearch.WordTrace tailWord_3405082 prefixEnd_3405082 1748443733972951834715319 := by
  unfold tailWord_3405082
  simp only [CollatzResearch.WordTrace]
  refine ⟨31048385862494232637952375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82795695633317953701206333 31048385862494232637952375)
  ·
    refine ⟨46572578793741348956928563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31048385862494232637952375 46572578793741348956928563)
    ·
      refine ⟨69858868190612023435392845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46572578793741348956928563 69858868190612023435392845)
      ·
        refine ⟨26197075571479508788272317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69858868190612023435392845 26197075571479508788272317)
        ·
          refine ⟨9823903339304815795602119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26197075571479508788272317 9823903339304815795602119)
          ·
            refine ⟨14735855008957223693403179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9823903339304815795602119 14735855008957223693403179)
            ·
              refine ⟨22103782513435835540104769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14735855008957223693403179 22103782513435835540104769)
              ·
                refine ⟨16577836885076876655078577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22103782513435835540104769 16577836885076876655078577)
                ·
                  refine ⟨12433377663807657491308933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16577836885076876655078577 12433377663807657491308933)
                  ·
                    refine ⟨2331258311963935779620425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12433377663807657491308933 2331258311963935779620425)
                    ·
                      refine ⟨1748443733972951834715319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2331258311963935779620425 1748443733972951834715319)
                      ·
                        rfl

theorem cell23_3405082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 2, 2, 4, 2].length) (baseStart_3405082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3405082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3405082 prefixEnd_3405082 := by exact prefixLift 3405082
  have htrace : WordTrace (prefixWord ++ tailWord_3405082) baseStart_3405082 baseEnd_3405082 := by
    simpa [prefixWord, tailWord_3405082, baseEnd_3405082] using wordTrace_append hprefix tailTrace_3405082
  have hstable : (prefixWord ++ tailWord_3405082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3405082).length < 2 ^ (prefixWord ++ tailWord_3405082).sum := by decide
  have hdescent : baseEnd_3405082 < baseStart_3405082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3405082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3405092 : List Nat := [2, 3, 1, 3, 1, 1, 4, 1, 3, 4]
def baseStart_3405092 : Nat := 118140960795 + 3405092 * 2 ^ 59
def prefixEnd_3405092 : Nat := 4983230072969 + 3 ^ 40 * 3405092 * 2
def baseEnd_3405092 : Nat := 582816289593165598530091

theorem tailTrace_3405092 : CollatzResearch.WordTrace tailWord_3405092 prefixEnd_3405092 582816289593165598530091 := by
  unfold tailWord_3405092
  simp only [CollatzResearch.WordTrace]
  refine ⟨62096954089970351129836765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82795938786627134839782353 62096954089970351129836765)
  ·
    refine ⟨23286357783738881673688787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62096954089970351129836765 23286357783738881673688787)
    ·
      refine ⟨34929536675608322510533181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23286357783738881673688787 34929536675608322510533181)
      ·
        refine ⟨13098576253353120941449943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34929536675608322510533181 13098576253353120941449943)
        ·
          refine ⟨19647864380029681412174915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13098576253353120941449943 19647864380029681412174915)
          ·
            refine ⟨29471796570044522118262373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19647864380029681412174915 29471796570044522118262373)
            ·
              refine ⟨5525961856883347897174195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29471796570044522118262373 5525961856883347897174195)
              ·
                refine ⟨8288942785325021845761293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5525961856883347897174195 8288942785325021845761293)
                ·
                  refine ⟨3108353544496883192160485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8288942785325021845761293 3108353544496883192160485)
                  ·
                    refine ⟨582816289593165598530091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3108353544496883192160485 582816289593165598530091)
                    ·
                      rfl

theorem cell23_3405092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 1, 3, 4].length) (baseStart_3405092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3405092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3405092 prefixEnd_3405092 := by exact prefixLift 3405092
  have htrace : WordTrace (prefixWord ++ tailWord_3405092) baseStart_3405092 baseEnd_3405092 := by
    simpa [prefixWord, tailWord_3405092, baseEnd_3405092] using wordTrace_append hprefix tailTrace_3405092
  have hstable : (prefixWord ++ tailWord_3405092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3405092).length < 2 ^ (prefixWord ++ tailWord_3405092).sum := by decide
  have hdescent : baseEnd_3405092 < baseStart_3405092 := by decide
  rcases family_descends (prefixWord ++ tailWord_3405092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3405192 : List Nat := [2, 1, 3, 3, 1, 2, 3, 1, 1, 1, 5]
def baseStart_3405192 : Nat := 118140960795 + 3405192 * 2 ^ 59
def prefixEnd_3405192 : Nat := 4983230072969 + 3 ^ 40 * 3405192 * 2
def baseEnd_3405192 : Nat := 1748500216844946404339813

theorem tailTrace_3405192 : CollatzResearch.WordTrace tailWord_3405192 prefixEnd_3405192 1748500216844946404339813 := by
  unfold tailWord_3405192
  simp only [CollatzResearch.WordTrace]
  refine ⟨62098777739789209669156915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82798370319718946225542553 62098777739789209669156915)
  ·
    refine ⟨93148166609683814503735373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62098777739789209669156915 93148166609683814503735373)
    ·
      refine ⟨34930562478631430438900765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93148166609683814503735373 34930562478631430438900765)
      ·
        refine ⟨13098960929486786414587787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34930562478631430438900765 13098960929486786414587787)
        ·
          refine ⟨19648441394230179621881681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13098960929486786414587787 19648441394230179621881681)
          ·
            refine ⟨14736331045672634716411261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19648441394230179621881681 14736331045672634716411261)
            ·
              refine ⟨5526124142127238018654223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14736331045672634716411261 5526124142127238018654223)
              ·
                refine ⟨8289186213190857027981335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5526124142127238018654223 8289186213190857027981335)
                ·
                  refine ⟨12433779319786285541972003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8289186213190857027981335 12433779319786285541972003)
                  ·
                    refine ⟨18650668979679428312958005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12433779319786285541972003 18650668979679428312958005)
                    ·
                      refine ⟨1748500216844946404339813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18650668979679428312958005 1748500216844946404339813)
                      ·
                        rfl

theorem cell23_3405192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_3405192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3405192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3405192 prefixEnd_3405192 := by exact prefixLift 3405192
  have htrace : WordTrace (prefixWord ++ tailWord_3405192) baseStart_3405192 baseEnd_3405192 := by
    simpa [prefixWord, tailWord_3405192, baseEnd_3405192] using wordTrace_append hprefix tailTrace_3405192
  have hstable : (prefixWord ++ tailWord_3405192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3405192).length < 2 ^ (prefixWord ++ tailWord_3405192).sum := by decide
  have hdescent : baseEnd_3405192 < baseStart_3405192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3405192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3405229 : List Nat := [1, 5, 2, 2, 1, 2, 3, 7]
def baseStart_3405229 : Nat := 118140960795 + 3405229 * 2 ^ 59
def prefixEnd_3405229 : Nat := 4983230072969 + 3 ^ 40 * 3405229 * 2
def baseEnd_3405229 : Nat := 64759970949228250354709

theorem tailTrace_3405229 : CollatzResearch.WordTrace tailWord_3405229 prefixEnd_3405229 64759970949228250354709 := by
  unfold tailWord_3405229
  simp only [CollatzResearch.WordTrace]
  refine ⟨124198904980444374657410741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82799269986962916438273827 124198904980444374657410741)
  ·
    refine ⟨11643647341916660124132257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 124198904980444374657410741 11643647341916660124132257)
    ·
      refine ⟨8732735506437495093099193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11643647341916660124132257 8732735506437495093099193)
      ·
        refine ⟨6549551629828121319824395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8732735506437495093099193 6549551629828121319824395)
        ·
          refine ⟨9824327444742181979736593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6549551629828121319824395 9824327444742181979736593)
          ·
            refine ⟨7368245583556636484802445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9824327444742181979736593 7368245583556636484802445)
            ·
              refine ⟨2763092093833738681800917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7368245583556636484802445 2763092093833738681800917)
              ·
                refine ⟨64759970949228250354709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2763092093833738681800917 64759970949228250354709)
                ·
                  rfl

theorem cell23_3405229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 3, 7].length) (baseStart_3405229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3405229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3405229 prefixEnd_3405229 := by exact prefixLift 3405229
  have htrace : WordTrace (prefixWord ++ tailWord_3405229) baseStart_3405229 baseEnd_3405229 := by
    simpa [prefixWord, tailWord_3405229, baseEnd_3405229] using wordTrace_append hprefix tailTrace_3405229
  have hstable : (prefixWord ++ tailWord_3405229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3405229).length < 2 ^ (prefixWord ++ tailWord_3405229).sum := by decide
  have hdescent : baseEnd_3405229 < baseStart_3405229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3405229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3405250 : List Nat := [3, 5, 2, 1, 1, 1, 1, 1, 4, 4]
def baseStart_3405250 : Nat := 118140960795 + 3405250 * 2 ^ 59
def prefixEnd_3405250 : Nat := 4983230072969 + 3 ^ 40 * 3405250 * 2
def baseEnd_3405250 : Nat := 582843332907635725804849

theorem tailTrace_3405250 : CollatzResearch.WordTrace tailWord_3405250 prefixEnd_3405250 582843332907635725804849 := by
  unfold tailWord_3405250
  simp only [CollatzResearch.WordTrace]
  refine ⟨31049917728342073810981301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82799780608912196829283469 31049917728342073810981301)
  ·
    refine ⟨2910929787032069419779497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31049917728342073810981301 2910929787032069419779497)
    ·
      refine ⟨2183197340274052064834623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2910929787032069419779497 2183197340274052064834623)
      ·
        refine ⟨3274796010411078097251935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2183197340274052064834623 3274796010411078097251935)
        ·
          refine ⟨4912194015616617145877903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3274796010411078097251935 4912194015616617145877903)
          ·
            refine ⟨7368291023424925718816855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4912194015616617145877903 7368291023424925718816855)
            ·
              refine ⟨11052436535137388578225283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7368291023424925718816855 11052436535137388578225283)
              ·
                refine ⟨16578654802706082867337925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11052436535137388578225283 16578654802706082867337925)
                ·
                  refine ⟨3108497775507390537625861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16578654802706082867337925 3108497775507390537625861)
                  ·
                    refine ⟨582843332907635725804849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3108497775507390537625861 582843332907635725804849)
                    ·
                      rfl

theorem cell23_3405250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_3405250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3405250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3405250 prefixEnd_3405250 := by exact prefixLift 3405250
  have htrace : WordTrace (prefixWord ++ tailWord_3405250) baseStart_3405250 baseEnd_3405250 := by
    simpa [prefixWord, tailWord_3405250, baseEnd_3405250] using wordTrace_append hprefix tailTrace_3405250
  have hstable : (prefixWord ++ tailWord_3405250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3405250).length < 2 ^ (prefixWord ++ tailWord_3405250).sum := by decide
  have hdescent : baseEnd_3405250 < baseStart_3405250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3405250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3405255 : List Nat := [1, 1, 4, 1, 1, 3, 1, 1, 4, 6]
def baseStart_3405255 : Nat := 118140960795 + 3405255 * 2 ^ 59
def prefixEnd_3405255 : Nat := 4983230072969 + 3 ^ 40 * 3405255 * 2
def baseEnd_3405255 : Nat := 582844188708726552617341

theorem tailTrace_3405255 : CollatzResearch.WordTrace tailWord_3405255 prefixEnd_3405255 582844188708726552617341 := by
  unfold tailWord_3405255
  simp only [CollatzResearch.WordTrace]
  refine ⟨124199853278350181097857219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82799902185566787398571479 124199853278350181097857219)
  ·
    refine ⟨186299779917525271646785829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124199853278350181097857219 186299779917525271646785829)
    ·
      refine ⟨34931208734535988433772343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 186299779917525271646785829 34931208734535988433772343)
      ·
        refine ⟨52396813101803982650658515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34931208734535988433772343 52396813101803982650658515)
        ·
          refine ⟨78595219652705973975987773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52396813101803982650658515 78595219652705973975987773)
          ·
            refine ⟨29473207369764740240995415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78595219652705973975987773 29473207369764740240995415)
            ·
              refine ⟨44209811054647110361493123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29473207369764740240995415 44209811054647110361493123)
              ·
                refine ⟨66314716581970665542239685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44209811054647110361493123 66314716581970665542239685)
                ·
                  refine ⟨12434009359119499789169941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66314716581970665542239685 12434009359119499789169941)
                  ·
                    refine ⟨582844188708726552617341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12434009359119499789169941 582844188708726552617341)
                    ·
                      rfl

theorem cell23_3405255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 4, 6].length) (baseStart_3405255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3405255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3405255 prefixEnd_3405255 := by exact prefixLift 3405255
  have htrace : WordTrace (prefixWord ++ tailWord_3405255) baseStart_3405255 baseEnd_3405255 := by
    simpa [prefixWord, tailWord_3405255, baseEnd_3405255] using wordTrace_append hprefix tailTrace_3405255
  have hstable : (prefixWord ++ tailWord_3405255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3405255).length < 2 ^ (prefixWord ++ tailWord_3405255).sum := by decide
  have hdescent : baseEnd_3405255 < baseStart_3405255 := by decide
  rcases family_descends (prefixWord ++ tailWord_3405255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3405265 : List Nat := [1, 2, 2, 1, 2, 1, 1, 1, 6, 1, 5]
def baseStart_3405265 : Nat := 118140960795 + 3405265 * 2 ^ 59
def prefixEnd_3405265 : Nat := 4983230072969 + 3 ^ 40 * 3405265 * 2
def baseEnd_3405265 : Nat := 1748537700932724618726977

theorem tailTrace_3405265 : CollatzResearch.WordTrace tailWord_3405265 prefixEnd_3405265 1748537700932724618726977 := by
  unfold tailWord_3405265
  simp only [CollatzResearch.WordTrace]
  refine ⟨124200218008313952805721249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82800145338875968537147499 124200218008313952805721249)
  ·
    refine ⟨93150163506235464604290937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124200218008313952805721249 93150163506235464604290937)
    ·
      refine ⟨69862622629676598453218203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93150163506235464604290937 69862622629676598453218203)
      ·
        refine ⟨104793933944514897679827305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69862622629676598453218203 104793933944514897679827305)
        ·
          refine ⟨78595450458386173259870479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104793933944514897679827305 78595450458386173259870479)
          ·
            refine ⟨117893175687579259889805719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78595450458386173259870479 117893175687579259889805719)
            ·
              refine ⟨176839763531368889834708579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117893175687579259889805719 176839763531368889834708579)
              ·
                refine ⟨265259645297053334752062869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 176839763531368889834708579 265259645297053334752062869)
                ·
                  refine ⟨12434045873299375066502947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 265259645297053334752062869 12434045873299375066502947)
                  ·
                    refine ⟨18651068809949062599754421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12434045873299375066502947 18651068809949062599754421)
                    ·
                      refine ⟨1748537700932724618726977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18651068809949062599754421 1748537700932724618726977)
                      ·
                        rfl

theorem cell23_3405265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 6, 1, 5].length) (baseStart_3405265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3405265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3405265 prefixEnd_3405265 := by exact prefixLift 3405265
  have htrace : WordTrace (prefixWord ++ tailWord_3405265) baseStart_3405265 baseEnd_3405265 := by
    simpa [prefixWord, tailWord_3405265, baseEnd_3405265] using wordTrace_append hprefix tailTrace_3405265
  have hstable : (prefixWord ++ tailWord_3405265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3405265).length < 2 ^ (prefixWord ++ tailWord_3405265).sum := by decide
  have hdescent : baseEnd_3405265 < baseStart_3405265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3405265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3405315 : List Nat := [1, 1, 1, 3, 2, 1, 2, 2, 3, 7]
def baseStart_3405315 : Nat := 118140960795 + 3405315 * 2 ^ 59
def prefixEnd_3405315 : Nat := 4983230072969 + 3 ^ 40 * 3405315 * 2
def baseEnd_3405315 : Nat := 582854458321816474367249

theorem tailTrace_3405315 : CollatzResearch.WordTrace tailWord_3405315 prefixEnd_3405315 582854458321816474367249 := by
  unfold tailWord_3405315
  simp only [CollatzResearch.WordTrace]
  refine ⟨124202041658132811345041399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82801361105421874230027599 124202041658132811345041399)
  ·
    refine ⟨186303062487199217017562099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124202041658132811345041399 186303062487199217017562099)
    ·
      refine ⟨279454593730798825526343149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186303062487199217017562099 279454593730798825526343149)
      ·
        refine ⟨104795472649049559572378681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 279454593730798825526343149 104795472649049559572378681)
        ·
          refine ⟨78596604486787169679284011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104795472649049559572378681 78596604486787169679284011)
          ·
            refine ⟨117894906730180754518926017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78596604486787169679284011 117894906730180754518926017)
            ·
              refine ⟨88421180047635565889194513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117894906730180754518926017 88421180047635565889194513)
              ·
                refine ⟨66315885035726674416895885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88421180047635565889194513 66315885035726674416895885)
                ·
                  refine ⟨24868456888397502906335957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66315885035726674416895885 24868456888397502906335957)
                  ·
                    refine ⟨582854458321816474367249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24868456888397502906335957 582854458321816474367249)
                    ·
                      rfl

theorem cell23_3405315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 3, 7].length) (baseStart_3405315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3405315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3405315 prefixEnd_3405315 := by exact prefixLift 3405315
  have htrace : WordTrace (prefixWord ++ tailWord_3405315) baseStart_3405315 baseEnd_3405315 := by
    simpa [prefixWord, tailWord_3405315, baseEnd_3405315] using wordTrace_append hprefix tailTrace_3405315
  have hstable : (prefixWord ++ tailWord_3405315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3405315).length < 2 ^ (prefixWord ++ tailWord_3405315).sum := by decide
  have hdescent : baseEnd_3405315 < baseStart_3405315 := by decide
  rcases family_descends (prefixWord ++ tailWord_3405315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3405319 : List Nat := [1, 1, 4, 3, 2, 3, 1, 1, 7]
def baseStart_3405319 : Nat := 118140960795 + 3405319 * 2 ^ 59
def prefixEnd_3405319 : Nat := 4983230072969 + 3 ^ 40 * 3405319 * 2
def baseEnd_3405319 : Nat := 194285047654229711939081

theorem tailTrace_3405319 : CollatzResearch.WordTrace tailWord_3405319 prefixEnd_3405319 194285047654229711939081 := by
  unfold tailWord_3405319
  simp only [CollatzResearch.WordTrace]
  refine ⟨124202187550118320028187011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82801458366745546685458007 124202187550118320028187011)
  ·
    refine ⟨186303281325177480042280517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124202187550118320028187011 186303281325177480042280517)
    ·
      refine ⟨34931865248470777507927597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 186303281325177480042280517 34931865248470777507927597)
      ·
        refine ⟨13099449468176541565472849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34931865248470777507927597 13099449468176541565472849)
        ·
          refine ⟨9824587101132406174104637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13099449468176541565472849 9824587101132406174104637)
          ·
            refine ⟨3684220162924652315289239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9824587101132406174104637 3684220162924652315289239)
            ·
              refine ⟨5526330244386978472933859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3684220162924652315289239 5526330244386978472933859)
              ·
                refine ⟨8289495366580467709400789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5526330244386978472933859 8289495366580467709400789)
                ·
                  refine ⟨194285047654229711939081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8289495366580467709400789 194285047654229711939081)
                  ·
                    rfl

theorem cell23_3405319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 1, 7].length) (baseStart_3405319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3405319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3405319 prefixEnd_3405319 := by exact prefixLift 3405319
  have htrace : WordTrace (prefixWord ++ tailWord_3405319) baseStart_3405319 baseEnd_3405319 := by
    simpa [prefixWord, tailWord_3405319, baseEnd_3405319] using wordTrace_append hprefix tailTrace_3405319
  have hstable : (prefixWord ++ tailWord_3405319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3405319).length < 2 ^ (prefixWord ++ tailWord_3405319).sum := by decide
  have hdescent : baseEnd_3405319 < baseStart_3405319 := by decide
  rcases family_descends (prefixWord ++ tailWord_3405319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3405355 : List Nat := [1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 9]
def baseStart_3405355 : Nat := 118140960795 + 3405355 * 2 ^ 59
def prefixEnd_3405355 : Nat := 4983230072969 + 3 ^ 40 * 3405355 * 2
def baseEnd_3405355 : Nat := 1748583914191629266601563

theorem tailTrace_3405355 : CollatzResearch.WordTrace tailWord_3405355 prefixEnd_3405355 1748583914191629266601563 := by
  unfold tailWord_3405355
  simp only [CollatzResearch.WordTrace]
  refine ⟨124203500577987898176497519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82802333718658598784331679 124203500577987898176497519)
  ·
    refine ⟨186305250866981847264746279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124203500577987898176497519 186305250866981847264746279)
    ·
      refine ⟨279457876300472770897119419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186305250866981847264746279 279457876300472770897119419)
      ·
        refine ⟨419186814450709156345679129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279457876300472770897119419 419186814450709156345679129)
        ·
          refine ⟨314390110838031867259259347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 419186814450709156345679129 314390110838031867259259347)
          ·
            refine ⟨471585166257047800888889021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314390110838031867259259347 471585166257047800888889021)
            ·
              refine ⟨176844437346392925333333383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 471585166257047800888889021 176844437346392925333333383)
              ·
                refine ⟨265266656019589388000000075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 176844437346392925333333383 265266656019589388000000075)
                ·
                  refine ⟨397899984029384082000000113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 265266656019589388000000075 397899984029384082000000113)
                  ·
                    refine ⟨298424988022038061500000085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 397899984029384082000000113 298424988022038061500000085)
                    ·
                      refine ⟨1748583914191629266601563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 298424988022038061500000085 1748583914191629266601563)
                      ·
                        rfl

theorem cell23_3405355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 9].length) (baseStart_3405355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3405355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3405355 prefixEnd_3405355 := by exact prefixLift 3405355
  have htrace : WordTrace (prefixWord ++ tailWord_3405355) baseStart_3405355 baseEnd_3405355 := by
    simpa [prefixWord, tailWord_3405355, baseEnd_3405355] using wordTrace_append hprefix tailTrace_3405355
  have hstable : (prefixWord ++ tailWord_3405355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3405355).length < 2 ^ (prefixWord ++ tailWord_3405355).sum := by decide
  have hdescent : baseEnd_3405355 < baseStart_3405355 := by decide
  rcases family_descends (prefixWord ++ tailWord_3405355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3405369 : List Nat := [1, 2, 1, 5, 1, 2, 2, 2, 2, 1, 4]
def baseStart_3405369 : Nat := 118140960795 + 3405369 * 2 ^ 59
def prefixEnd_3405369 : Nat := 4983230072969 + 3 ^ 40 * 3405369 * 2
def baseEnd_3405369 : Nat := 1748591102920792211826499

theorem tailTrace_3405369 : CollatzResearch.WordTrace tailWord_3405369 prefixEnd_3405369 1748591102920792211826499 := by
  unfold tailWord_3405369
  simp only [CollatzResearch.WordTrace]
  refine ⟨124204011199937178567507161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82802674133291452378338107 124204011199937178567507161)
  ·
    refine ⟨93153008399952883925630371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124204011199937178567507161 93153008399952883925630371)
    ·
      refine ⟨139729512599929325888445557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93153008399952883925630371 139729512599929325888445557)
      ·
        refine ⟨13099641806243374302041771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 139729512599929325888445557 13099641806243374302041771)
        ·
          refine ⟨19649462709365061453062657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13099641806243374302041771 19649462709365061453062657)
          ·
            refine ⟨14737097032023796089796993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19649462709365061453062657 14737097032023796089796993)
            ·
              refine ⟨11052822774017847067347745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14737097032023796089796993 11052822774017847067347745)
              ·
                refine ⟨8289617080513385300510809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11052822774017847067347745 8289617080513385300510809)
                ·
                  refine ⟨6217212810385038975383107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8289617080513385300510809 6217212810385038975383107)
                  ·
                    refine ⟨9325819215577558463074661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6217212810385038975383107 9325819215577558463074661)
                    ·
                      refine ⟨1748591102920792211826499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9325819215577558463074661 1748591102920792211826499)
                      ·
                        rfl

theorem cell23_3405369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_3405369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3405369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3405369 prefixEnd_3405369 := by exact prefixLift 3405369
  have htrace : WordTrace (prefixWord ++ tailWord_3405369) baseStart_3405369 baseEnd_3405369 := by
    simpa [prefixWord, tailWord_3405369, baseEnd_3405369] using wordTrace_append hprefix tailTrace_3405369
  have hstable : (prefixWord ++ tailWord_3405369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3405369).length < 2 ^ (prefixWord ++ tailWord_3405369).sum := by decide
  have hdescent : baseEnd_3405369 < baseStart_3405369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3405369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3405392 : List Nat := [2, 1, 1, 1, 1, 3, 3, 5, 6]
def baseStart_3405392 : Nat := 118140960795 + 3405392 * 2 ^ 59
def prefixEnd_3405392 : Nat := 4983230072969 + 3 ^ 40 * 3405392 * 2
def baseEnd_3405392 : Nat := 194289212552871735759877

theorem tailTrace_3405392 : CollatzResearch.WordTrace tailWord_3405392 prefixEnd_3405392 194289212552871735759877 := by
  unfold tailWord_3405392
  simp only [CollatzResearch.WordTrace]
  refine ⟨62102425039426926747797215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82803233385902568997062953 62102425039426926747797215)
  ·
    refine ⟨93153637559140390121695823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62102425039426926747797215 93153637559140390121695823)
    ·
      refine ⟨139730456338710585182543735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93153637559140390121695823 139730456338710585182543735)
      ·
        refine ⟨209595684508065877773815603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139730456338710585182543735 209595684508065877773815603)
        ·
          refine ⟨314393526762098816660723405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209595684508065877773815603 314393526762098816660723405)
          ·
            refine ⟨117897572535787056247771277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 314393526762098816660723405 117897572535787056247771277)
            ·
              refine ⟨44211589700920146092914229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117897572535787056247771277 44211589700920146092914229)
              ·
                refine ⟨4144836534461263696210709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44211589700920146092914229 4144836534461263696210709)
                ·
                  refine ⟨194289212552871735759877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4144836534461263696210709 194289212552871735759877)
                  ·
                    rfl

theorem cell23_3405392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 5, 6].length) (baseStart_3405392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3405392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3405392 prefixEnd_3405392 := by exact prefixLift 3405392
  have htrace : WordTrace (prefixWord ++ tailWord_3405392) baseStart_3405392 baseEnd_3405392 := by
    simpa [prefixWord, tailWord_3405392, baseEnd_3405392] using wordTrace_append hprefix tailTrace_3405392
  have hstable : (prefixWord ++ tailWord_3405392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3405392).length < 2 ^ (prefixWord ++ tailWord_3405392).sum := by decide
  have hdescent : baseEnd_3405392 < baseStart_3405392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3405392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3405413 : List Nat := [1, 3, 1, 3, 3, 2, 2, 3, 1, 4]
def baseStart_3405413 : Nat := 118140960795 + 3405413 * 2 ^ 59
def prefixEnd_3405413 : Nat := 4983230072969 + 3 ^ 40 * 3405413 * 2
def baseEnd_3405413 : Nat := 582871232023196679892099

theorem tailTrace_3405413 : CollatzResearch.WordTrace tailWord_3405413 prefixEnd_3405413 582871232023196679892099 := by
  unfold tailWord_3405413
  simp only [CollatzResearch.WordTrace]
  refine ⟨124205616011777774082108893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82803744007851849388072595 124205616011777774082108893)
  ·
    refine ⟨46577106004416665280790835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124205616011777774082108893 46577106004416665280790835)
    ·
      refine ⟨69865659006624997921186253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46577106004416665280790835 69865659006624997921186253)
      ·
        refine ⟨26199622127484374220444845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69865659006624997921186253 26199622127484374220444845)
        ·
          refine ⟨9824858297806640332666817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26199622127484374220444845 9824858297806640332666817)
          ·
            refine ⟨7368643723354980249500113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9824858297806640332666817 7368643723354980249500113)
            ·
              refine ⟨5526482792516235187125085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7368643723354980249500113 5526482792516235187125085)
              ·
                refine ⟨2072431047193588195171907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5526482792516235187125085 2072431047193588195171907)
                ·
                  refine ⟨3108646570790382292757861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2072431047193588195171907 3108646570790382292757861)
                  ·
                    refine ⟨582871232023196679892099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3108646570790382292757861 582871232023196679892099)
                    ·
                      rfl

theorem cell23_3405413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 3, 1, 4].length) (baseStart_3405413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3405413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3405413 prefixEnd_3405413 := by exact prefixLift 3405413
  have htrace : WordTrace (prefixWord ++ tailWord_3405413) baseStart_3405413 baseEnd_3405413 := by
    simpa [prefixWord, tailWord_3405413, baseEnd_3405413] using wordTrace_append hprefix tailTrace_3405413
  have hstable : (prefixWord ++ tailWord_3405413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3405413).length < 2 ^ (prefixWord ++ tailWord_3405413).sum := by decide
  have hdescent : baseEnd_3405413 < baseStart_3405413 := by decide
  rcases family_descends (prefixWord ++ tailWord_3405413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3405426 : List Nat := [3, 2, 1, 2, 3, 3, 1, 2, 6]
def baseStart_3405426 : Nat := 118140960795 + 3405426 * 2 ^ 59
def prefixEnd_3405426 : Nat := 4983230072969 + 3 ^ 40 * 3405426 * 2
def baseEnd_3405426 : Nat := 194291152368677609868193

theorem tailTrace_3405426 : CollatzResearch.WordTrace tailWord_3405426 prefixEnd_3405426 194291152368677609868193 := by
  unfold tailWord_3405426
  simp only [CollatzResearch.WordTrace]
  refine ⟨31051522540182669325583033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82804060107153784868221421 31051522540182669325583033)
  ·
    refine ⟨23288641905137001994187275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31051522540182669325583033 23288641905137001994187275)
    ·
      refine ⟨34932962857705502991280913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23288641905137001994187275 34932962857705502991280913)
      ·
        refine ⟨26199722143279127243460685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34932962857705502991280913 26199722143279127243460685)
        ·
          refine ⟨9824895803729672716297757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26199722143279127243460685 9824895803729672716297757)
          ·
            refine ⟨3684335926398627268611659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9824895803729672716297757 3684335926398627268611659)
            ·
              refine ⟨5526503889597940902917489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3684335926398627268611659 5526503889597940902917489)
              ·
                refine ⟨4144877917198455677188117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5526503889597940902917489 4144877917198455677188117)
                ·
                  refine ⟨194291152368677609868193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4144877917198455677188117 194291152368677609868193)
                  ·
                    rfl

theorem cell23_3405426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 2, 6].length) (baseStart_3405426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3405426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3405426 prefixEnd_3405426 := by exact prefixLift 3405426
  have htrace : WordTrace (prefixWord ++ tailWord_3405426) baseStart_3405426 baseEnd_3405426 := by
    simpa [prefixWord, tailWord_3405426, baseEnd_3405426] using wordTrace_append hprefix tailTrace_3405426
  have hstable : (prefixWord ++ tailWord_3405426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3405426).length < 2 ^ (prefixWord ++ tailWord_3405426).sum := by decide
  have hdescent : baseEnd_3405426 < baseStart_3405426 := by decide
  rcases family_descends (prefixWord ++ tailWord_3405426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3405429 : List Nat := [1, 3, 4, 2, 1, 1, 1, 1, 1, 2, 6]
def baseStart_3405429 : Nat := 118140960795 + 3405429 * 2 ^ 59
def prefixEnd_3405429 : Nat := 4983230072969 + 3 ^ 40 * 3405429 * 2
def baseEnd_3405429 : Nat := 1748621911760061977076223

theorem tailTrace_3405429 : CollatzResearch.WordTrace tailWord_3405429 prefixEnd_3405429 1748621911760061977076223 := by
  unfold tailWord_3405429
  simp only [CollatzResearch.WordTrace]
  refine ⟨124206199579719808814691341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82804133053146539209794227 124206199579719808814691341)
  ·
    refine ⟨46577324842394928305509253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124206199579719808814691341 46577324842394928305509253)
    ·
      refine ⟨8733248407949049057282985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46577324842394928305509253 8733248407949049057282985)
      ·
        refine ⟨6549936305961786792962239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8733248407949049057282985 6549936305961786792962239)
        ·
          refine ⟨9824904458942680189443359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6549936305961786792962239 9824904458942680189443359)
          ·
            refine ⟨14737356688414020284165039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9824904458942680189443359 14737356688414020284165039)
            ·
              refine ⟨22106035032621030426247559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14737356688414020284165039 22106035032621030426247559)
              ·
                refine ⟨33159052548931545639371339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22106035032621030426247559 33159052548931545639371339)
                ·
                  refine ⟨49738578823397318459057009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33159052548931545639371339 49738578823397318459057009)
                  ·
                    refine ⟨37303934117547988844292757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49738578823397318459057009 37303934117547988844292757)
                    ·
                      refine ⟨1748621911760061977076223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37303934117547988844292757 1748621911760061977076223)
                      ·
                        rfl

theorem cell23_3405429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_3405429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3405429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3405429 prefixEnd_3405429 := by exact prefixLift 3405429
  have htrace : WordTrace (prefixWord ++ tailWord_3405429) baseStart_3405429 baseEnd_3405429 := by
    simpa [prefixWord, tailWord_3405429, baseEnd_3405429] using wordTrace_append hprefix tailTrace_3405429
  have hstable : (prefixWord ++ tailWord_3405429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3405429).length < 2 ^ (prefixWord ++ tailWord_3405429).sum := by decide
  have hdescent : baseEnd_3405429 < baseStart_3405429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3405429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3405476 : List Nat := [2, 3, 1, 2, 2, 2, 2, 3, 1, 1, 4]
def baseStart_3405476 : Nat := 118140960795 + 3405476 * 2 ^ 59
def prefixEnd_3405476 : Nat := 4983230072969 + 3 ^ 40 * 3405476 * 2
def baseEnd_3405476 : Nat := 1748646045350823293188507

theorem tailTrace_3405476 : CollatzResearch.WordTrace tailWord_3405476 prefixEnd_3405476 1748646045350823293188507 := by
  unfold tailWord_3405476
  simp only [CollatzResearch.WordTrace]
  refine ⟨62103956905274767920826141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82805275873699690561101521 62103956905274767920826141)
  ·
    refine ⟨23288983839478037970309803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62103956905274767920826141 23288983839478037970309803)
    ·
      refine ⟨34933475759217056955464705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23288983839478037970309803 34933475759217056955464705)
      ·
        refine ⟨26200106819412792716598529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34933475759217056955464705 26200106819412792716598529)
        ·
          refine ⟨19650080114559594537448897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26200106819412792716598529 19650080114559594537448897)
          ·
            refine ⟨14737560085919695903086673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19650080114559594537448897 14737560085919695903086673)
            ·
              refine ⟨11053170064439771927315005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14737560085919695903086673 11053170064439771927315005)
              ·
                refine ⟨4144938774164914472743127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11053170064439771927315005 4144938774164914472743127)
                ·
                  refine ⟨6217408161247371709114691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4144938774164914472743127 6217408161247371709114691)
                  ·
                    refine ⟨9326112241871057563672037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6217408161247371709114691 9326112241871057563672037)
                    ·
                      refine ⟨1748646045350823293188507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9326112241871057563672037 1748646045350823293188507)
                      ·
                        rfl

theorem cell23_3405476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 3, 1, 1, 4].length) (baseStart_3405476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3405476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3405476 prefixEnd_3405476 := by exact prefixLift 3405476
  have htrace : WordTrace (prefixWord ++ tailWord_3405476) baseStart_3405476 baseEnd_3405476 := by
    simpa [prefixWord, tailWord_3405476, baseEnd_3405476] using wordTrace_append hprefix tailTrace_3405476
  have hstable : (prefixWord ++ tailWord_3405476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3405476).length < 2 ^ (prefixWord ++ tailWord_3405476).sum := by decide
  have hdescent : baseEnd_3405476 < baseStart_3405476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3405476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3405510 : List Nat := [6, 1, 2, 1, 1, 2, 1, 1, 3, 1, 4]
def baseStart_3405510 : Nat := 118140960795 + 3405510 * 2 ^ 59
def prefixEnd_3405510 : Nat := 4983230072969 + 3 ^ 40 * 3405510 * 2
def baseEnd_3405510 : Nat := 1748663503693076160163351

theorem tailTrace_3405510 : CollatzResearch.WordTrace tailWord_3405510 prefixEnd_3405510 1748663503693076160163351 := by
  unfold tailWord_3405510
  simp only [CollatzResearch.WordTrace]
  refine ⟨3881536059138323739012187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 82806102594950906432259989 3881536059138323739012187)
  ·
    refine ⟨5822304088707485608518281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3881536059138323739012187 5822304088707485608518281)
    ·
      refine ⟨4366728066530614206388711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5822304088707485608518281 4366728066530614206388711)
      ·
        refine ⟨6550092099795921309583067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4366728066530614206388711 6550092099795921309583067)
        ·
          refine ⟨9825138149693881964374601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6550092099795921309583067 9825138149693881964374601)
          ·
            refine ⟨7368853612270411473280951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9825138149693881964374601 7368853612270411473280951)
            ·
              refine ⟨11053280418405617209921427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7368853612270411473280951 11053280418405617209921427)
              ·
                refine ⟨16579920627608425814882141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11053280418405617209921427 16579920627608425814882141)
                ·
                  refine ⟨6217470235353159680580803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16579920627608425814882141 6217470235353159680580803)
                  ·
                    refine ⟨9326205353029739520871205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6217470235353159680580803 9326205353029739520871205)
                    ·
                      refine ⟨1748663503693076160163351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9326205353029739520871205 1748663503693076160163351)
                      ·
                        rfl

theorem cell23_3405510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_3405510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3405510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3405510 prefixEnd_3405510 := by exact prefixLift 3405510
  have htrace : WordTrace (prefixWord ++ tailWord_3405510) baseStart_3405510 baseEnd_3405510 := by
    simpa [prefixWord, tailWord_3405510, baseEnd_3405510] using wordTrace_append hprefix tailTrace_3405510
  have hstable : (prefixWord ++ tailWord_3405510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3405510).length < 2 ^ (prefixWord ++ tailWord_3405510).sum := by decide
  have hdescent : baseEnd_3405510 < baseStart_3405510 := by decide
  rcases family_descends (prefixWord ++ tailWord_3405510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3405544 : List Nat := [2, 1, 4, 1, 3, 3, 2, 2, 1, 2, 2]
def baseStart_3405544 : Nat := 118140960795 + 3405544 * 2 ^ 59
def prefixEnd_3405544 : Nat := 4983230072969 + 3 ^ 40 * 3405544 * 2
def baseEnd_3405544 : Nat := 1748680962035329027138195

theorem tailTrace_3405544 : CollatzResearch.WordTrace tailWord_3405544 prefixEnd_3405544 1748680962035329027138195 := by
  unfold tailWord_3405544
  simp only [CollatzResearch.WordTrace]
  refine ⟨62105196987151591727563843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82806929316202122303418457 62105196987151591727563843)
  ·
    refine ⟨93157795480727387591345765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62105196987151591727563843 93157795480727387591345765)
    ·
      refine ⟨17467086652636385173377331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93157795480727387591345765 17467086652636385173377331)
      ·
        refine ⟨26200629978954577760065997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17467086652636385173377331 26200629978954577760065997)
        ·
          refine ⟨9825236242107966660024749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26200629978954577760065997 9825236242107966660024749)
          ·
            refine ⟨3684463590790487497509281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9825236242107966660024749 3684463590790487497509281)
            ·
              refine ⟨2763347693092865623131961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3684463590790487497509281 2763347693092865623131961)
              ·
                refine ⟨2072510769819649217348971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2763347693092865623131961 2072510769819649217348971)
                ·
                  refine ⟨3108766154729473826023457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2072510769819649217348971 3108766154729473826023457)
                  ·
                    refine ⟨2331574616047105369517593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3108766154729473826023457 2331574616047105369517593)
                    ·
                      refine ⟨1748680962035329027138195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2331574616047105369517593 1748680962035329027138195)
                      ·
                        rfl

theorem cell23_3405544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 2, 2, 1, 2, 2].length) (baseStart_3405544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3405544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3405544 prefixEnd_3405544 := by exact prefixLift 3405544
  have htrace : WordTrace (prefixWord ++ tailWord_3405544) baseStart_3405544 baseEnd_3405544 := by
    simpa [prefixWord, tailWord_3405544, baseEnd_3405544] using wordTrace_append hprefix tailTrace_3405544
  have hstable : (prefixWord ++ tailWord_3405544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3405544).length < 2 ^ (prefixWord ++ tailWord_3405544).sum := by decide
  have hdescent : baseEnd_3405544 < baseStart_3405544 := by decide
  rcases family_descends (prefixWord ++ tailWord_3405544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3405569 : List Nat := [1, 2, 4, 1, 1, 1, 2, 1, 4, 1, 5]
def baseStart_3405569 : Nat := 118140960795 + 3405569 * 2 ^ 59
def prefixEnd_3405569 : Nat := 4983230072969 + 3 ^ 40 * 3405569 * 2
def baseEnd_3405569 : Nat := 1748693799051691429325579

theorem tailTrace_3405569 : CollatzResearch.WordTrace tailWord_3405569 prefixEnd_3405569 1748693799051691429325579 := by
  unfold tailWord_3405569
  simp only [CollatzResearch.WordTrace]
  refine ⟨124211305799212612724787761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82807537199475075149858507 124211305799212612724787761)
  ·
    refine ⟨93158479349409459543590821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124211305799212612724787761 93158479349409459543590821)
    ·
      refine ⟨17467214878014273664423279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93158479349409459543590821 17467214878014273664423279)
      ·
        refine ⟨26200822317021410496634919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17467214878014273664423279 26200822317021410496634919)
        ·
          refine ⟨39301233475532115744952379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26200822317021410496634919 39301233475532115744952379)
          ·
            refine ⟨58951850213298173617428569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39301233475532115744952379 58951850213298173617428569)
            ·
              refine ⟨44213887659973630213071427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58951850213298173617428569 44213887659973630213071427)
              ·
                refine ⟨66320831489960445319607141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44213887659973630213071427 66320831489960445319607141)
                ·
                  refine ⟨12435155904367583497426339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66320831489960445319607141 12435155904367583497426339)
                  ·
                    refine ⟨18652733856551375246139509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12435155904367583497426339 18652733856551375246139509)
                    ·
                      refine ⟨1748693799051691429325579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18652733856551375246139509 1748693799051691429325579)
                      ·
                        rfl

theorem cell23_3405569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_3405569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3405569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3405569 prefixEnd_3405569 := by exact prefixLift 3405569
  have htrace : WordTrace (prefixWord ++ tailWord_3405569) baseStart_3405569 baseEnd_3405569 := by
    simpa [prefixWord, tailWord_3405569, baseEnd_3405569] using wordTrace_append hprefix tailTrace_3405569
  have hstable : (prefixWord ++ tailWord_3405569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3405569).length < 2 ^ (prefixWord ++ tailWord_3405569).sum := by decide
  have hdescent : baseEnd_3405569 < baseStart_3405569 := by decide
  rcases family_descends (prefixWord ++ tailWord_3405569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3405570 : List Nat := [3, 4, 1, 1, 1, 1, 2, 4, 1, 3, 2]
def baseStart_3405570 : Nat := 118140960795 + 3405570 * 2 ^ 59
def prefixEnd_3405570 : Nat := 4983230072969 + 3 ^ 40 * 3405570 * 2
def baseEnd_3405570 : Nat := 1748694312532345925413075

theorem tailTrace_3405570 : CollatzResearch.WordTrace tailWord_3405570 prefixEnd_3405570 1748694312532345925413075 := by
  unfold tailWord_3405570
  simp only [CollatzResearch.WordTrace]
  refine ⟨31052835568052247473893541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82807561514805993263716109 31052835568052247473893541)
  ·
    refine ⟨5822406669009796401355039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31052835568052247473893541 5822406669009796401355039)
    ·
      refine ⟨8733610003514694602032559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5822406669009796401355039 8733610003514694602032559)
      ·
        refine ⟨13100415005272041903048839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8733610003514694602032559 13100415005272041903048839)
        ·
          refine ⟨19650622507908062854573259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13100415005272041903048839 19650622507908062854573259)
          ·
            refine ⟨29475933761862094281859889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19650622507908062854573259 29475933761862094281859889)
            ·
              refine ⟨22106950321396570711394917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29475933761862094281859889 22106950321396570711394917)
              ·
                refine ⟨4145053185261857008386547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22106950321396570711394917 4145053185261857008386547)
                ·
                  refine ⟨6217579777892785512579821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4145053185261857008386547 6217579777892785512579821)
                  ·
                    refine ⟨2331592416709794567217433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6217579777892785512579821 2331592416709794567217433)
                    ·
                      refine ⟨1748694312532345925413075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2331592416709794567217433 1748694312532345925413075)
                      ·
                        rfl

theorem cell23_3405570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 4, 1, 3, 2].length) (baseStart_3405570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3405570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3405570 prefixEnd_3405570 := by exact prefixLift 3405570
  have htrace : WordTrace (prefixWord ++ tailWord_3405570) baseStart_3405570 baseEnd_3405570 := by
    simpa [prefixWord, tailWord_3405570, baseEnd_3405570] using wordTrace_append hprefix tailTrace_3405570
  have hstable : (prefixWord ++ tailWord_3405570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3405570).length < 2 ^ (prefixWord ++ tailWord_3405570).sum := by decide
  have hdescent : baseEnd_3405570 < baseStart_3405570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3405570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3405617 : List Nat := [1, 2, 2, 3, 2, 3, 3, 1, 2, 2, 2]
def baseStart_3405617 : Nat := 118140960795 + 3405617 * 2 ^ 59
def prefixEnd_3405617 : Nat := 4983230072969 + 3 ^ 40 * 3405617 * 2
def baseEnd_3405617 : Nat := 1748718446123107241525359

theorem tailTrace_3405617 : CollatzResearch.WordTrace tailWord_3405617 prefixEnd_3405617 1748718446123107241525359 := by
  unfold tailWord_3405617
  simp only [CollatzResearch.WordTrace]
  refine ⟨124213056503038716922535105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82808704335359144615023403 124213056503038716922535105)
  ·
    refine ⟨93159792377279037691901329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124213056503038716922535105 93159792377279037691901329)
    ·
      refine ⟨69869844282959278268925997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93159792377279037691901329 69869844282959278268925997)
      ·
        refine ⟨26201191606109729350847249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69869844282959278268925997 26201191606109729350847249)
        ·
          refine ⟨19650893704582297013135437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26201191606109729350847249 19650893704582297013135437)
          ·
            refine ⟨7369085139218361379925789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19650893704582297013135437 7369085139218361379925789)
            ·
              refine ⟨2763406927206885517472171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7369085139218361379925789 2763406927206885517472171)
              ·
                refine ⟨4145110390810328276208257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2763406927206885517472171 4145110390810328276208257)
                ·
                  refine ⟨3108832793107746207156193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4145110390810328276208257 3108832793107746207156193)
                  ·
                    refine ⟨2331624594830809655367145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3108832793107746207156193 2331624594830809655367145)
                    ·
                      refine ⟨1748718446123107241525359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2331624594830809655367145 1748718446123107241525359)
                      ·
                        rfl

theorem cell23_3405617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 3, 1, 2, 2, 2].length) (baseStart_3405617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3405617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3405617 prefixEnd_3405617 := by exact prefixLift 3405617
  have htrace : WordTrace (prefixWord ++ tailWord_3405617) baseStart_3405617 baseEnd_3405617 := by
    simpa [prefixWord, tailWord_3405617, baseEnd_3405617] using wordTrace_append hprefix tailTrace_3405617
  have hstable : (prefixWord ++ tailWord_3405617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3405617).length < 2 ^ (prefixWord ++ tailWord_3405617).sum := by decide
  have hdescent : baseEnd_3405617 < baseStart_3405617 := by decide
  rcases family_descends (prefixWord ++ tailWord_3405617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3405733 : List Nat := [1, 3, 1, 2, 1, 1, 1, 4, 4, 3, 2]
def baseStart_3405733 : Nat := 118140960795 + 3405733 * 2 ^ 59
def prefixEnd_3405733 : Nat := 4983230072969 + 3 ^ 40 * 3405733 * 2
def baseEnd_3405733 : Nat := 1748778009879028787674825

theorem tailTrace_3405733 : CollatzResearch.WordTrace tailWord_3405733 prefixEnd_3405733 1748778009879028787674825 := by
  unfold tailWord_3405733
  simp only [CollatzResearch.WordTrace]
  refine ⟨124217287370618468733757853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82811524913745645822505235 124217287370618468733757853)
  ·
    refine ⟨46581482763981925775159195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124217287370618468733757853 46581482763981925775159195)
    ·
      refine ⟨69872224145972888662738793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46581482763981925775159195 69872224145972888662738793)
      ·
        refine ⟨52404168109479666497054095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69872224145972888662738793 52404168109479666497054095)
        ·
          refine ⟨78606252164219499745581143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52404168109479666497054095 78606252164219499745581143)
          ·
            refine ⟨117909378246329249618371715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78606252164219499745581143 117909378246329249618371715)
            ·
              refine ⟨176864067369493874427557573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117909378246329249618371715 176864067369493874427557573)
              ·
                refine ⟨33162012631780101455167045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 176864067369493874427557573 33162012631780101455167045)
                ·
                  refine ⟨6217877368458769022843821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33162012631780101455167045 6217877368458769022843821)
                  ·
                    refine ⟨2331704013172038383566433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6217877368458769022843821 2331704013172038383566433)
                    ·
                      refine ⟨1748778009879028787674825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2331704013172038383566433 1748778009879028787674825)
                      ·
                        rfl

theorem cell23_3405733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 4, 3, 2].length) (baseStart_3405733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3405733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3405733 prefixEnd_3405733 := by exact prefixLift 3405733
  have htrace : WordTrace (prefixWord ++ tailWord_3405733) baseStart_3405733 baseEnd_3405733 := by
    simpa [prefixWord, tailWord_3405733, baseEnd_3405733] using wordTrace_append hprefix tailTrace_3405733
  have hstable : (prefixWord ++ tailWord_3405733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3405733).length < 2 ^ (prefixWord ++ tailWord_3405733).sum := by decide
  have hdescent : baseEnd_3405733 < baseStart_3405733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3405733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3405757 : List Nat := [1, 4, 1, 2, 3, 1, 1, 5, 1, 1, 3]
def baseStart_3405757 : Nat := 118140960795 + 3405757 * 2 ^ 59
def prefixEnd_3405757 : Nat := 4983230072969 + 3 ^ 40 * 3405757 * 2
def baseEnd_3405757 : Nat := 1748790333414736693774715

theorem tailTrace_3405757 : CollatzResearch.WordTrace tailWord_3405757 prefixEnd_3405757 1748790333414736693774715 := by
  unfold tailWord_3405757
  simp only [CollatzResearch.WordTrace]
  refine ⟨124218162722531520832631525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82812108481687680555087683 124218162722531520832631525)
  ·
    refine ⟨23290905510474660156118411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124218162722531520832631525 23290905510474660156118411)
    ·
      refine ⟨34936358265711990234177617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23290905510474660156118411 34936358265711990234177617)
      ·
        refine ⟨26202268699283992675633213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34936358265711990234177617 26202268699283992675633213)
        ·
          refine ⟨9825850762231497253362455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26202268699283992675633213 9825850762231497253362455)
          ·
            refine ⟨14738776143347245880043683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9825850762231497253362455 14738776143347245880043683)
            ·
              refine ⟨22108164215020868820065525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14738776143347245880043683 22108164215020868820065525)
              ·
                refine ⟨2072640395158206451881143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22108164215020868820065525 2072640395158206451881143)
                ·
                  refine ⟨3108960592737309677821715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2072640395158206451881143 3108960592737309677821715)
                  ·
                    refine ⟨4663440889105964516732573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3108960592737309677821715 4663440889105964516732573)
                    ·
                      refine ⟨1748790333414736693774715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4663440889105964516732573 1748790333414736693774715)
                      ·
                        rfl

theorem cell23_3405757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 5, 1, 1, 3].length) (baseStart_3405757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3405757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3405757 prefixEnd_3405757 := by exact prefixLift 3405757
  have htrace : WordTrace (prefixWord ++ tailWord_3405757) baseStart_3405757 baseEnd_3405757 := by
    simpa [prefixWord, tailWord_3405757, baseEnd_3405757] using wordTrace_append hprefix tailTrace_3405757
  have hstable : (prefixWord ++ tailWord_3405757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3405757).length < 2 ^ (prefixWord ++ tailWord_3405757).sum := by decide
  have hdescent : baseEnd_3405757 < baseStart_3405757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3405757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3405776 : List Nat := [2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 4]
def baseStart_3405776 : Nat := 118140960795 + 3405776 * 2 ^ 59
def prefixEnd_3405776 : Nat := 4983230072969 + 3 ^ 40 * 3405776 * 2
def baseEnd_3405776 : Nat := 1748800089547172119437127

theorem tailTrace_3405776 : CollatzResearch.WordTrace tailWord_3405776 prefixEnd_3405776 1748800089547172119437127 := by
  unfold tailWord_3405776
  simp only [CollatzResearch.WordTrace]
  refine ⟨62109427854731343538786591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82812570472975124718382121 62109427854731343538786591)
  ·
    refine ⟨93164141782097015308179887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62109427854731343538786591 93164141782097015308179887)
    ·
      refine ⟨139746212673145522962269831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93164141782097015308179887 139746212673145522962269831)
      ·
        refine ⟨209619319009718284443404747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139746212673145522962269831 209619319009718284443404747)
        ·
          refine ⟨314428978514577426665107121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209619319009718284443404747 314428978514577426665107121)
          ·
            refine ⟨235821733885933069998830341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 314428978514577426665107121 235821733885933069998830341)
            ·
              refine ⟨44216575103612450624780689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 235821733885933069998830341 44216575103612450624780689)
              ·
                refine ⟨33162431327709337968585517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44216575103612450624780689 33162431327709337968585517)
                ·
                  refine ⟨12435911747891001738219569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33162431327709337968585517 12435911747891001738219569)
                  ·
                    refine ⟨9326933810918251303664677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12435911747891001738219569 9326933810918251303664677)
                    ·
                      refine ⟨1748800089547172119437127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9326933810918251303664677 1748800089547172119437127)
                      ·
                        rfl

theorem cell23_3405776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 4].length) (baseStart_3405776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3405776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3405776 prefixEnd_3405776 := by exact prefixLift 3405776
  have htrace : WordTrace (prefixWord ++ tailWord_3405776) baseStart_3405776 baseEnd_3405776 := by
    simpa [prefixWord, tailWord_3405776, baseEnd_3405776] using wordTrace_append hprefix tailTrace_3405776
  have hstable : (prefixWord ++ tailWord_3405776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3405776).length < 2 ^ (prefixWord ++ tailWord_3405776).sum := by decide
  have hdescent : baseEnd_3405776 < baseStart_3405776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3405776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3405793 : List Nat := [1, 2, 3, 1, 2, 1, 5, 1, 1, 2, 4]
def baseStart_3405793 : Nat := 118140960795 + 3405793 * 2 ^ 59
def prefixEnd_3405793 : Nat := 4983230072969 + 3 ^ 40 * 3405793 * 2
def baseEnd_3405793 : Nat := 1748808818718298552924549

theorem tailTrace_3405793 : CollatzResearch.WordTrace tailWord_3405793 prefixEnd_3405793 1748808818718298552924549 := by
  unfold tailWord_3405793
  simp only [CollatzResearch.WordTrace]
  refine ⟨124219475750401098980942033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82812983833600732653961355 124219475750401098980942033)
  ·
    refine ⟨93164606812800824235706525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124219475750401098980942033 93164606812800824235706525)
    ·
      refine ⟨34936727554800309088389947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93164606812800824235706525 34936727554800309088389947)
      ·
        refine ⟨52405091332200463632584921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34936727554800309088389947 52405091332200463632584921)
        ·
          refine ⟨39303818499150347724438691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52405091332200463632584921 39303818499150347724438691)
          ·
            refine ⟨58955727748725521586658037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39303818499150347724438691 58955727748725521586658037)
            ·
              refine ⟨5527099476443017648749191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58955727748725521586658037 5527099476443017648749191)
              ·
                refine ⟨8290649214664526473123787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5527099476443017648749191 8290649214664526473123787)
                ·
                  refine ⟨12435973821996789709685681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8290649214664526473123787 12435973821996789709685681)
                  ·
                    refine ⟨9326980366497592282264261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12435973821996789709685681 9326980366497592282264261)
                    ·
                      refine ⟨1748808818718298552924549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9326980366497592282264261 1748808818718298552924549)
                      ·
                        rfl

theorem cell23_3405793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 1, 1, 2, 4].length) (baseStart_3405793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3405793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3405793 prefixEnd_3405793 := by exact prefixLift 3405793
  have htrace : WordTrace (prefixWord ++ tailWord_3405793) baseStart_3405793 baseEnd_3405793 := by
    simpa [prefixWord, tailWord_3405793, baseEnd_3405793] using wordTrace_append hprefix tailTrace_3405793
  have hstable : (prefixWord ++ tailWord_3405793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3405793).length < 2 ^ (prefixWord ++ tailWord_3405793).sum := by decide
  have hdescent : baseEnd_3405793 < baseStart_3405793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3405793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3405831 : List Nat := [1, 1, 4, 3, 1, 3, 3, 2, 1, 2, 2]
def baseStart_3405831 : Nat := 118140960795 + 3405831 * 2 ^ 59
def prefixEnd_3405831 : Nat := 4983230072969 + 3 ^ 40 * 3405831 * 2
def baseEnd_3405831 : Nat := 1748828330983169404249375

theorem tailTrace_3405831 : CollatzResearch.WordTrace tailWord_3405831 prefixEnd_3405831 1748828330983169404249375 := by
  unfold tailWord_3405831
  simp only [CollatzResearch.WordTrace]
  refine ⟨124220861724263431470825347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82813907816175620980550231 124220861724263431470825347)
  ·
    refine ⟨186331292586395147206238021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124220861724263431470825347 186331292586395147206238021)
    ·
      refine ⟨34937117359949090101169629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 186331292586395147206238021 34937117359949090101169629)
      ·
        refine ⟨13101419009980908787938611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34937117359949090101169629 13101419009980908787938611)
        ·
          refine ⟨19652128514971363181907917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13101419009980908787938611 19652128514971363181907917)
          ·
            refine ⟨7369548193114261193215469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19652128514971363181907917 7369548193114261193215469)
            ·
              refine ⟨2763580572417847947455801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7369548193114261193215469 2763580572417847947455801)
              ·
                refine ⟨2072685429313385960591851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2763580572417847947455801 2072685429313385960591851)
                ·
                  refine ⟨3109028143970078940887777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2072685429313385960591851 3109028143970078940887777)
                  ·
                    refine ⟨2331771107977559205665833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3109028143970078940887777 2331771107977559205665833)
                    ·
                      refine ⟨1748828330983169404249375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2331771107977559205665833 1748828330983169404249375)
                      ·
                        rfl

theorem cell23_3405831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 3, 2, 1, 2, 2].length) (baseStart_3405831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3405831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3405831 prefixEnd_3405831 := by exact prefixLift 3405831
  have htrace : WordTrace (prefixWord ++ tailWord_3405831) baseStart_3405831 baseEnd_3405831 := by
    simpa [prefixWord, tailWord_3405831, baseEnd_3405831] using wordTrace_append hprefix tailTrace_3405831
  have hstable : (prefixWord ++ tailWord_3405831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3405831).length < 2 ^ (prefixWord ++ tailWord_3405831).sum := by decide
  have hdescent : baseEnd_3405831 < baseStart_3405831 := by decide
  rcases family_descends (prefixWord ++ tailWord_3405831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3405857 : List Nat := [1, 2, 3, 2, 4, 1, 1, 1, 3, 3, 2]
def baseStart_3405857 : Nat := 118140960795 + 3405857 * 2 ^ 59
def prefixEnd_3405857 : Nat := 4983230072969 + 3 ^ 40 * 3405857 * 2
def baseEnd_3405857 : Nat := 1748841681480186302524255

theorem tailTrace_3405857 : CollatzResearch.WordTrace tailWord_3405857 prefixEnd_3405857 1748841681480186302524255 := by
  unfold tailWord_3405857
  simp only [CollatzResearch.WordTrace]
  refine ⟨124221810022169237911271825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82814540014779491940847883 124221810022169237911271825)
  ·
    refine ⟨93166357516626928433453869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124221810022169237911271825 93166357516626928433453869)
    ·
      refine ⟨34937384068735098162545201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93166357516626928433453869 34937384068735098162545201)
      ·
        refine ⟨26203038051551323621908901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34937384068735098162545201 26203038051551323621908901)
        ·
          refine ⟨4913069634665873179107919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26203038051551323621908901 4913069634665873179107919)
          ·
            refine ⟨7369604451998809768661879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4913069634665873179107919 7369604451998809768661879)
            ·
              refine ⟨11054406677998214652992819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7369604451998809768661879 11054406677998214652992819)
              ·
                refine ⟨16581610016997321979489229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11054406677998214652992819 16581610016997321979489229)
                ·
                  refine ⟨6218103756373995742308461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16581610016997321979489229 6218103756373995742308461)
                  ·
                    refine ⟨2331788908640248403365673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6218103756373995742308461 2331788908640248403365673)
                    ·
                      refine ⟨1748841681480186302524255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2331788908640248403365673 1748841681480186302524255)
                      ·
                        rfl

theorem cell23_3405857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 1, 3, 3, 2].length) (baseStart_3405857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3405857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3405857 prefixEnd_3405857 := by exact prefixLift 3405857
  have htrace : WordTrace (prefixWord ++ tailWord_3405857) baseStart_3405857 baseEnd_3405857 := by
    simpa [prefixWord, tailWord_3405857, baseEnd_3405857] using wordTrace_append hprefix tailTrace_3405857
  have hstable : (prefixWord ++ tailWord_3405857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3405857).length < 2 ^ (prefixWord ++ tailWord_3405857).sum := by decide
  have hdescent : baseEnd_3405857 < baseStart_3405857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3405857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
