import V185TrunkScan19Chunk044

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental

namespace V185TrunkScan19Incremental

def tailWord_451505 : List Nat := [1, 2, 2, 4, 3, 2, 1, 4]
def baseStart_451505 : Nat := 118140960795 + 451505 * 2 ^ 59
def prefixEnd_451505 : Nat := 4983230072969 + 3 ^ 40 * 451505 * 2
def baseEnd_451505 : Nat := 137386123204954796036191

theorem tailTrace_451505 : CollatzResearch.WordTrace tailWord_451505 prefixEnd_451505 137386123204954796036191 := by
  unfold tailWord_451505
  simp only [CollatzResearch.WordTrace]
  refine ⟨16467740229281970759995969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10978493486187980506663979 16467740229281970759995969)
  ·
    refine ⟨12350805171961478069996977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16467740229281970759995969 12350805171961478069996977)
    ·
      refine ⟨9263103878971108552497733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12350805171961478069996977 9263103878971108552497733)
      ·
        refine ⟨1736831977307082853593325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9263103878971108552497733 1736831977307082853593325)
        ·
          refine ⟨651311991490156070097497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1736831977307082853593325 651311991490156070097497)
          ·
            refine ⟨488483993617617052573123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 651311991490156070097497 488483993617617052573123)
            ·
              refine ⟨732725990426425578859685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 488483993617617052573123 732725990426425578859685)
              ·
                refine ⟨137386123204954796036191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 732725990426425578859685 137386123204954796036191)
                ·
                  rfl

theorem cell19_451505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 4].length) (baseStart_451505 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_451505 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_451505 prefixEnd_451505 := by exact prefixLift 451505
  have htrace : WordTrace (prefixWord ++ tailWord_451505) baseStart_451505 baseEnd_451505 := by
    simpa [prefixWord, tailWord_451505, baseEnd_451505] using wordTrace_append hprefix tailTrace_451505
  have hstable : (prefixWord ++ tailWord_451505).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451505).length < 2 ^ (prefixWord ++ tailWord_451505).sum := by decide
  have hdescent : baseEnd_451505 < baseStart_451505 := by decide
  rcases family_descends (prefixWord ++ tailWord_451505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451642 : List Nat := [3, 1, 1, 1, 3, 1, 4, 5]
def baseStart_451642 : Nat := 118140960795 + 451642 * 2 ^ 59
def prefixEnd_451642 : Nat := 4983230072969 + 3 ^ 40 * 451642 * 2
def baseEnd_451642 : Nat := 137427810226979070991373

theorem tailTrace_451642 : CollatzResearch.WordTrace tailWord_451642 prefixEnd_451642 137427810226979070991373 := by
  unfold tailWord_451642
  simp only [CollatzResearch.WordTrace]
  refine ⟨4118184257446410789433295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10981824686523762105155453 4118184257446410789433295)
  ·
    refine ⟨6177276386169616184149943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4118184257446410789433295 6177276386169616184149943)
    ·
      refine ⟨9265914579254424276224915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6177276386169616184149943 9265914579254424276224915)
      ·
        refine ⟨13898871868881636414337373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9265914579254424276224915 13898871868881636414337373)
        ·
          refine ⟨5212076950830613655376515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13898871868881636414337373 5212076950830613655376515)
          ·
            refine ⟨7818115426245920483064773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5212076950830613655376515 7818115426245920483064773)
            ·
              refine ⟨1465896642421110090574645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7818115426245920483064773 1465896642421110090574645)
              ·
                refine ⟨137427810226979070991373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1465896642421110090574645 137427810226979070991373)
                ·
                  rfl

theorem cell19_451642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 5].length) (baseStart_451642 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_451642 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_451642 prefixEnd_451642 := by exact prefixLift 451642
  have htrace : WordTrace (prefixWord ++ tailWord_451642) baseStart_451642 baseEnd_451642 := by
    simpa [prefixWord, tailWord_451642, baseEnd_451642] using wordTrace_append hprefix tailTrace_451642
  have hstable : (prefixWord ++ tailWord_451642).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451642).length < 2 ^ (prefixWord ++ tailWord_451642).sum := by decide
  have hdescent : baseEnd_451642 < baseStart_451642 := by decide
  rcases family_descends (prefixWord ++ tailWord_451642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451828 : List Nat := [2, 6, 1, 2, 8]
def baseStart_451828 : Nat := 118140960795 + 451828 * 2 ^ 59
def prefixEnd_451828 : Nat := 4983230072969 + 3 ^ 40 * 451828 * 2
def baseEnd_451828 : Nat := 5092015081695768550279

theorem tailTrace_451828 : CollatzResearch.WordTrace tailWord_451828 prefixEnd_451828 5092015081695768550279 := by
  unfold tailWord_451828
  simp only [CollatzResearch.WordTrace]
  refine ⟨8239760503555898462002069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10986347338074531282669425 8239760503555898462002069)
  ·
    refine ⟨386238773604182740406347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 8239760503555898462002069 386238773604182740406347)
    ·
      refine ⟨579358160406274110609521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386238773604182740406347 579358160406274110609521)
      ·
        refine ⟨434518620304705582957141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 579358160406274110609521 434518620304705582957141)
        ·
          refine ⟨5092015081695768550279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 434518620304705582957141 5092015081695768550279)
          ·
            rfl

theorem cell19_451828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 8].length) (baseStart_451828 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_451828 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_451828 prefixEnd_451828 := by exact prefixLift 451828
  have htrace : WordTrace (prefixWord ++ tailWord_451828) baseStart_451828 baseEnd_451828 := by
    simpa [prefixWord, tailWord_451828, baseEnd_451828] using wordTrace_append hprefix tailTrace_451828
  have hstable : (prefixWord ++ tailWord_451828).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451828).length < 2 ^ (prefixWord ++ tailWord_451828).sum := by decide
  have hdescent : baseEnd_451828 < baseStart_451828 := by decide
  rcases family_descends (prefixWord ++ tailWord_451828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451851 : List Nat := [1, 1, 1, 1, 5, 3, 3, 4]
def baseStart_451851 : Nat := 118140960795 + 451851 * 2 ^ 59
def prefixEnd_451851 : Nat := 4983230072969 + 3 ^ 40 * 451851 * 2
def baseEnd_451851 : Nat := 137491405756928512346359

theorem tailTrace_451851 : CollatzResearch.WordTrace tailWord_451851 prefixEnd_451851 137491405756928512346359 := by
  unfold tailWord_451851
  simp only [CollatzResearch.WordTrace]
  refine ⟨16480359886028471852091407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10986906590685647901394271 16480359886028471852091407)
  ·
    refine ⟨24720539829042707778137111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16480359886028471852091407 24720539829042707778137111)
    ·
      refine ⟨37080809743564061667205667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24720539829042707778137111 37080809743564061667205667)
      ·
        refine ⟨55621214615346092500808501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37080809743564061667205667 55621214615346092500808501)
        ·
          refine ⟨5214488870188696171950797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55621214615346092500808501 5214488870188696171950797)
          ·
            refine ⟨1955433326320761064481549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5214488870188696171950797 1955433326320761064481549)
            ·
              refine ⟨733287497370285399180581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1955433326320761064481549 733287497370285399180581)
              ·
                refine ⟨137491405756928512346359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 733287497370285399180581 137491405756928512346359)
                ·
                  rfl

theorem cell19_451851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 4].length) (baseStart_451851 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_451851 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_451851 prefixEnd_451851 := by exact prefixLift 451851
  have htrace : WordTrace (prefixWord ++ tailWord_451851) baseStart_451851 baseEnd_451851 := by
    simpa [prefixWord, tailWord_451851, baseEnd_451851] using wordTrace_append hprefix tailTrace_451851
  have hstable : (prefixWord ++ tailWord_451851).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451851).length < 2 ^ (prefixWord ++ tailWord_451851).sum := by decide
  have hdescent : baseEnd_451851 < baseStart_451851 := by decide
  rcases family_descends (prefixWord ++ tailWord_451851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451889 : List Nat := [1, 2, 2, 3, 3, 2, 6]
def baseStart_451889 : Nat := 118140960795 + 451889 * 2 ^ 59
def prefixEnd_451889 : Nat := 4983230072969 + 3 ^ 40 * 451889 * 2
def baseEnd_451889 : Nat := 45834322860185227833937

theorem tailTrace_451889 : CollatzResearch.WordTrace tailWord_451889 prefixEnd_451889 45834322860185227833937 := by
  unfold tailWord_451889
  simp only [CollatzResearch.WordTrace]
  refine ⟨16481745859890804341974721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10987830573260536227983147 16481745859890804341974721)
  ·
    refine ⟨12361309394918103256481041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16481745859890804341974721 12361309394918103256481041)
    ·
      refine ⟨9270982046188577442360781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12361309394918103256481041 9270982046188577442360781)
      ·
        refine ⟨3476618267320716540885293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9270982046188577442360781 3476618267320716540885293)
        ·
          refine ⟨1303731850245268702831985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3476618267320716540885293 1303731850245268702831985)
          ·
            refine ⟨977798887683951527123989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1303731850245268702831985 977798887683951527123989)
            ·
              refine ⟨45834322860185227833937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 977798887683951527123989 45834322860185227833937)
              ·
                rfl

theorem cell19_451889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 6].length) (baseStart_451889 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_451889 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_451889 prefixEnd_451889 := by exact prefixLift 451889
  have htrace : WordTrace (prefixWord ++ tailWord_451889) baseStart_451889 baseEnd_451889 := by
    simpa [prefixWord, tailWord_451889, baseEnd_451889] using wordTrace_append hprefix tailTrace_451889
  have hstable : (prefixWord ++ tailWord_451889).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451889).length < 2 ^ (prefixWord ++ tailWord_451889).sum := by decide
  have hdescent : baseEnd_451889 < baseStart_451889 := by decide
  rcases family_descends (prefixWord ++ tailWord_451889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451925 : List Nat := [1, 3, 2, 2, 3, 1, 4, 3]
def baseStart_451925 : Nat := 118140960795 + 451925 * 2 ^ 59
def prefixEnd_451925 : Nat := 4983230072969 + 3 ^ 40 * 451925 * 2
def baseEnd_451925 : Nat := 137513922834518266701713

theorem tailTrace_451925 : CollatzResearch.WordTrace tailWord_451925 prefixEnd_451925 137513922834518266701713 := by
  unfold tailWord_451925
  simp only [CollatzResearch.WordTrace]
  refine ⟨16483058887760382490285229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10988705925173588326856819 16483058887760382490285229)
  ·
    refine ⟨6181147082910143433856961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16483058887760382490285229 6181147082910143433856961)
    ·
      refine ⟨4635860312182607575392721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6181147082910143433856961 4635860312182607575392721)
      ·
        refine ⟨3476895234136955681544541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4635860312182607575392721 3476895234136955681544541)
        ·
          refine ⟨1303835712801358380579203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3476895234136955681544541 1303835712801358380579203)
          ·
            refine ⟨1955753569202037570868805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1303835712801358380579203 1955753569202037570868805)
            ·
              refine ⟨366703794225382044537901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1955753569202037570868805 366703794225382044537901)
              ·
                refine ⟨137513922834518266701713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 366703794225382044537901 137513922834518266701713)
                ·
                  rfl

theorem cell19_451925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 4, 3].length) (baseStart_451925 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_451925 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_451925 prefixEnd_451925 := by exact prefixLift 451925
  have htrace : WordTrace (prefixWord ++ tailWord_451925) baseStart_451925 baseEnd_451925 := by
    simpa [prefixWord, tailWord_451925, baseEnd_451925] using wordTrace_append hprefix tailTrace_451925
  have hstable : (prefixWord ++ tailWord_451925).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451925).length < 2 ^ (prefixWord ++ tailWord_451925).sum := by decide
  have hdescent : baseEnd_451925 < baseStart_451925 := by decide
  rcases family_descends (prefixWord ++ tailWord_451925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451927 : List Nat := [1, 1, 3, 2, 3, 3, 1, 5]
def baseStart_451927 : Nat := 118140960795 + 451927 * 2 ^ 59
def prefixEnd_451927 : Nat := 4983230072969 + 3 ^ 40 * 451927 * 2
def baseEnd_451927 : Nat := 137514531404182854657263

theorem tailTrace_451927 : CollatzResearch.WordTrace tailWord_451927 prefixEnd_451927 137514531404182854657263 := by
  unfold tailWord_451927
  simp only [CollatzResearch.WordTrace]
  refine ⟨16483131833753136831858035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10988754555835424554572023 16483131833753136831858035)
  ·
    refine ⟨24724697750629705247787053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16483131833753136831858035 24724697750629705247787053)
    ·
      refine ⟨9271761656486139467920145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24724697750629705247787053 9271761656486139467920145)
      ·
        refine ⟨6953821242364604600940109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9271761656486139467920145 6953821242364604600940109)
        ·
          refine ⟨2607682965886726725352541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6953821242364604600940109 2607682965886726725352541)
          ·
            refine ⟨977881112207522522007203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2607682965886726725352541 977881112207522522007203)
            ·
              refine ⟨1466821668311283783010805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 977881112207522522007203 1466821668311283783010805)
              ·
                refine ⟨137514531404182854657263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1466821668311283783010805 137514531404182854657263)
                ·
                  rfl

theorem cell19_451927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 5].length) (baseStart_451927 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_451927 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_451927 prefixEnd_451927 := by exact prefixLift 451927
  have htrace : WordTrace (prefixWord ++ tailWord_451927) baseStart_451927 baseEnd_451927 := by
    simpa [prefixWord, tailWord_451927, baseEnd_451927] using wordTrace_append hprefix tailTrace_451927
  have hstable : (prefixWord ++ tailWord_451927).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451927).length < 2 ^ (prefixWord ++ tailWord_451927).sum := by decide
  have hdescent : baseEnd_451927 < baseStart_451927 := by decide
  rcases family_descends (prefixWord ++ tailWord_451927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451944 : List Nat := [2, 1, 4, 2, 3, 2, 5]
def baseStart_451944 : Nat := 118140960795 + 451944 * 2 ^ 59
def prefixEnd_451944 : Nat := 4983230072969 + 3 ^ 40 * 451944 * 2
def baseEnd_451944 : Nat := 45839901415443950759813

theorem tailTrace_451944 : CollatzResearch.WordTrace tailWord_451944 prefixEnd_451944 45839901415443950759813 := by
  unfold tailWord_451944
  simp only [CollatzResearch.WordTrace]
  refine ⟨8241875937345774367613443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10989167916461032490151257 8241875937345774367613443)
  ·
    refine ⟨12362813906018661551420165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8241875937345774367613443 12362813906018661551420165)
    ·
      refine ⟨2318027607378499040891281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12362813906018661551420165 2318027607378499040891281)
      ·
        refine ⟨1738520705533874280668461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2318027607378499040891281 1738520705533874280668461)
        ·
          refine ⟨651945264575202855250673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1738520705533874280668461 651945264575202855250673)
          ·
            refine ⟨488958948431402141438005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 651945264575202855250673 488958948431402141438005)
            ·
              refine ⟨45839901415443950759813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 488958948431402141438005 45839901415443950759813)
              ·
                rfl

theorem cell19_451944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 5].length) (baseStart_451944 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_451944 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_451944 prefixEnd_451944 := by exact prefixLift 451944
  have htrace : WordTrace (prefixWord ++ tailWord_451944) baseStart_451944 baseEnd_451944 := by
    simpa [prefixWord, tailWord_451944, baseEnd_451944] using wordTrace_append hprefix tailTrace_451944
  have hstable : (prefixWord ++ tailWord_451944).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451944).length < 2 ^ (prefixWord ++ tailWord_451944).sum := by decide
  have hdescent : baseEnd_451944 < baseStart_451944 := by decide
  rcases family_descends (prefixWord ++ tailWord_451944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_451965 : List Nat := [1, 4, 1, 1, 2, 2, 4, 4]
def baseStart_451965 : Nat := 118140960795 + 451965 * 2 ^ 59
def prefixEnd_451965 : Nat := 4983230072969 + 3 ^ 40 * 451965 * 2
def baseEnd_451965 : Nat := 137526094227810025812715

theorem tailTrace_451965 : CollatzResearch.WordTrace tailWord_451965 prefixEnd_451965 137526094227810025812715 := by
  unfold tailWord_451965
  simp only [CollatzResearch.WordTrace]
  refine ⟨16484517807615469321741349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10989678538410312881160899 16484517807615469321741349)
  ·
    refine ⟨3090847088927900497826503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16484517807615469321741349 3090847088927900497826503)
    ·
      refine ⟨4636270633391850746739755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3090847088927900497826503 4636270633391850746739755)
      ·
        refine ⟨6954405950087776120109633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4636270633391850746739755 6954405950087776120109633)
        ·
          refine ⟨5215804462565832090082225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6954405950087776120109633 5215804462565832090082225)
          ·
            refine ⟨3911853346924374067561669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5215804462565832090082225 3911853346924374067561669)
            ·
              refine ⟨733472502548320137667813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3911853346924374067561669 733472502548320137667813)
              ·
                refine ⟨137526094227810025812715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 733472502548320137667813 137526094227810025812715)
                ·
                  rfl

theorem cell19_451965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 4].length) (baseStart_451965 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_451965 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_451965 prefixEnd_451965 := by exact prefixLift 451965
  have htrace : WordTrace (prefixWord ++ tailWord_451965) baseStart_451965 baseEnd_451965 := by
    simpa [prefixWord, tailWord_451965, baseEnd_451965] using wordTrace_append hprefix tailTrace_451965
  have hstable : (prefixWord ++ tailWord_451965).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_451965).length < 2 ^ (prefixWord ++ tailWord_451965).sum := by decide
  have hdescent : baseEnd_451965 < baseStart_451965 := by decide
  rcases family_descends (prefixWord ++ tailWord_451965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452043 : List Nat := [1, 1, 1, 1, 3, 3, 2, 7]
def baseStart_452043 : Nat := 118140960795 + 452043 * 2 ^ 59
def prefixEnd_452043 : Nat := 4983230072969 + 3 ^ 40 * 452043 * 2
def baseEnd_452043 : Nat := 137549828444728956079169

theorem tailTrace_452043 : CollatzResearch.WordTrace tailWord_452043 prefixEnd_452043 137549828444728956079169 := by
  unfold tailWord_452043
  simp only [CollatzResearch.WordTrace]
  refine ⟨16487362701332888643080783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10991575134221925762053855 16487362701332888643080783)
  ·
    refine ⟨24731044051999332964621175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16487362701332888643080783 24731044051999332964621175)
    ·
      refine ⟨37096566077998999446931763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24731044051999332964621175 37096566077998999446931763)
      ·
        refine ⟨55644849116998499170397645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37096566077998999446931763 55644849116998499170397645)
        ·
          refine ⟨20866818418874437188899117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55644849116998499170397645 20866818418874437188899117)
          ·
            refine ⟨7825056907077913945837169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20866818418874437188899117 7825056907077913945837169)
            ·
              refine ⟨5868792680308435459377877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7825056907077913945837169 5868792680308435459377877)
              ·
                refine ⟨137549828444728956079169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5868792680308435459377877 137549828444728956079169)
                ·
                  rfl

theorem cell19_452043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 7].length) (baseStart_452043 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_452043 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_452043 prefixEnd_452043 := by exact prefixLift 452043
  have htrace : WordTrace (prefixWord ++ tailWord_452043) baseStart_452043 baseEnd_452043 := by
    simpa [prefixWord, tailWord_452043, baseEnd_452043] using wordTrace_append hprefix tailTrace_452043
  have hstable : (prefixWord ++ tailWord_452043).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452043).length < 2 ^ (prefixWord ++ tailWord_452043).sum := by decide
  have hdescent : baseEnd_452043 < baseStart_452043 := by decide
  rcases family_descends (prefixWord ++ tailWord_452043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452094 : List Nat := [4, 2, 2, 3, 1, 1, 1, 5]
def baseStart_452094 : Nat := 118140960795 + 452094 * 2 ^ 59
def prefixEnd_452094 : Nat := 4983230072969 + 3 ^ 40 * 452094 * 2
def baseEnd_452094 : Nat := 137565346971175948945697

theorem tailTrace_452094 : CollatzResearch.WordTrace tailWord_452094 prefixEnd_452094 137565346971175948945697 := by
  unfold tailWord_452094
  simp only [CollatzResearch.WordTrace]
  refine ⟨2061152853018515544148417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10992815216098749568791557 2061152853018515544148417)
  ·
    refine ⟨1545864639763886658111313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2061152853018515544148417 1545864639763886658111313)
    ·
      refine ⟨1159398479822914993583485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1545864639763886658111313 1159398479822914993583485)
      ·
        refine ⟨434774429933593122593807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1159398479822914993583485 434774429933593122593807)
        ·
          refine ⟨652161644900389683890711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 434774429933593122593807 652161644900389683890711)
          ·
            refine ⟨978242467350584525836067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 652161644900389683890711 978242467350584525836067)
            ·
              refine ⟨1467363701025876788754101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 978242467350584525836067 1467363701025876788754101)
              ·
                refine ⟨137565346971175948945697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1467363701025876788754101 137565346971175948945697)
                ·
                  rfl

theorem cell19_452094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 5].length) (baseStart_452094 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_452094 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_452094 prefixEnd_452094 := by exact prefixLift 452094
  have htrace : WordTrace (prefixWord ++ tailWord_452094) baseStart_452094 baseEnd_452094 := by
    simpa [prefixWord, tailWord_452094, baseEnd_452094] using wordTrace_append hprefix tailTrace_452094
  have hstable : (prefixWord ++ tailWord_452094).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452094).length < 2 ^ (prefixWord ++ tailWord_452094).sum := by decide
  have hdescent : baseEnd_452094 < baseStart_452094 := by decide
  rcases family_descends (prefixWord ++ tailWord_452094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452117 : List Nat := [1, 3, 2, 1, 3, 4, 5]
def baseStart_452117 : Nat := 118140960795 + 452117 * 2 ^ 59
def prefixEnd_452117 : Nat := 4983230072969 + 3 ^ 40 * 452117 * 2
def baseEnd_452117 : Nat := 45857448507439570144841

theorem tailTrace_452117 : CollatzResearch.WordTrace tailWord_452117 prefixEnd_452117 45857448507439570144841 := by
  unfold tailWord_452117
  simp only [CollatzResearch.WordTrace]
  refine ⟨16490061703064799281274605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10993374468709866187516403 16490061703064799281274605)
  ·
    refine ⟨6183773138649299730477977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16490061703064799281274605 6183773138649299730477977)
    ·
      refine ⟨4637829853986974797858483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6183773138649299730477977 4637829853986974797858483)
      ·
        refine ⟨6956744780980462196787725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4637829853986974797858483 6956744780980462196787725)
        ·
          refine ⟨2608779292867673323795397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6956744780980462196787725 2608779292867673323795397)
          ·
            refine ⟨489146117412688748211637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2608779292867673323795397 489146117412688748211637)
            ·
              refine ⟨45857448507439570144841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 489146117412688748211637 45857448507439570144841)
              ·
                rfl

theorem cell19_452117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 5].length) (baseStart_452117 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_452117 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_452117 prefixEnd_452117 := by exact prefixLift 452117
  have htrace : WordTrace (prefixWord ++ tailWord_452117) baseStart_452117 baseEnd_452117 := by
    simpa [prefixWord, tailWord_452117, baseEnd_452117] using wordTrace_append hprefix tailTrace_452117
  have hstable : (prefixWord ++ tailWord_452117).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452117).length < 2 ^ (prefixWord ++ tailWord_452117).sum := by decide
  have hdescent : baseEnd_452117 < baseStart_452117 := by decide
  rcases family_descends (prefixWord ++ tailWord_452117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452210 : List Nat := [3, 2, 1, 2, 3, 2, 3, 3]
def baseStart_452210 : Nat := 118140960795 + 452210 * 2 ^ 59
def prefixEnd_452210 : Nat := 4983230072969 + 3 ^ 40 * 452210 * 2
def baseEnd_452210 : Nat := 137600644011722050367603

theorem tailTrace_452210 : CollatzResearch.WordTrace tailWord_452210 prefixEnd_452210 137600644011722050367603 := by
  unfold tailWord_452210
  simp only [CollatzResearch.WordTrace]
  refine ⟨4123363422931969041102521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10995635794485250776273389 4123363422931969041102521)
  ·
    refine ⟨3092522567198976780826891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4123363422931969041102521 3092522567198976780826891)
    ·
      refine ⟨4638783850798465171240337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3092522567198976780826891 4638783850798465171240337)
      ·
        refine ⟨3479087888098848878430253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4638783850798465171240337 3479087888098848878430253)
        ·
          refine ⟨1304657958037068329411345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3479087888098848878430253 1304657958037068329411345)
          ·
            refine ⟨978493468527801247058509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1304657958037068329411345 978493468527801247058509)
            ·
              refine ⟨366935050697925467646941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 978493468527801247058509 366935050697925467646941)
              ·
                refine ⟨137600644011722050367603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 366935050697925467646941 137600644011722050367603)
                ·
                  rfl

theorem cell19_452210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 3, 3].length) (baseStart_452210 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_452210 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_452210 prefixEnd_452210 := by exact prefixLift 452210
  have htrace : WordTrace (prefixWord ++ tailWord_452210) baseStart_452210 baseEnd_452210 := by
    simpa [prefixWord, tailWord_452210, baseEnd_452210] using wordTrace_append hprefix tailTrace_452210
  have hstable : (prefixWord ++ tailWord_452210).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452210).length < 2 ^ (prefixWord ++ tailWord_452210).sum := by decide
  have hdescent : baseEnd_452210 < baseStart_452210 := by decide
  rcases family_descends (prefixWord ++ tailWord_452210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452269 : List Nat := [1, 5, 2, 1, 1, 1, 3, 5]
def baseStart_452269 : Nat := 118140960795 + 452269 * 2 ^ 59
def prefixEnd_452269 : Nat := 4983230072969 + 3 ^ 40 * 452269 * 2
def baseEnd_452269 : Nat := 137618596816827395056331

theorem tailTrace_452269 : CollatzResearch.WordTrace tailWord_452269 prefixEnd_452269 137618596816827395056331 := by
  unfold tailWord_452269
  simp only [CollatzResearch.WordTrace]
  refine ⟨16495605598514129240807861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10997070399009419493871907 16495605598514129240807861)
  ·
    refine ⟨1546463024860699616325737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16495605598514129240807861 1546463024860699616325737)
    ·
      refine ⟨1159847268645524712244303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1546463024860699616325737 1159847268645524712244303)
      ·
        refine ⟨1739770902968287068366455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1159847268645524712244303 1739770902968287068366455)
        ·
          refine ⟨2609656354452430602549683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1739770902968287068366455 2609656354452430602549683)
          ·
            refine ⟨3914484531678645903824525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2609656354452430602549683 3914484531678645903824525)
            ·
              refine ⟨1467931699379492213934197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3914484531678645903824525 1467931699379492213934197)
              ·
                refine ⟨137618596816827395056331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1467931699379492213934197 137618596816827395056331)
                ·
                  rfl

theorem cell19_452269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 5].length) (baseStart_452269 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_452269 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_452269 prefixEnd_452269 := by exact prefixLift 452269
  have htrace : WordTrace (prefixWord ++ tailWord_452269) baseStart_452269 baseEnd_452269 := by
    simpa [prefixWord, tailWord_452269, baseEnd_452269] using wordTrace_append hprefix tailTrace_452269
  have hstable : (prefixWord ++ tailWord_452269).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452269).length < 2 ^ (prefixWord ++ tailWord_452269).sum := by decide
  have hdescent : baseEnd_452269 < baseStart_452269 := by decide
  rcases family_descends (prefixWord ++ tailWord_452269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452271 : List Nat := [1, 1, 2, 1, 2, 4, 3, 5]
def baseStart_452271 : Nat := 118140960795 + 452271 * 2 ^ 59
def prefixEnd_452271 : Nat := 4983230072969 + 3 ^ 40 * 452271 * 2
def baseEnd_452271 : Nat := 137619205386491983011881

theorem tailTrace_452271 : CollatzResearch.WordTrace tailWord_452271 prefixEnd_452271 137619205386491983011881 := by
  unfold tailWord_452271
  simp only [CollatzResearch.WordTrace]
  refine ⟨16495678544506883582380667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10997119029671255721587111 16495678544506883582380667)
  ·
    refine ⟨24743517816760325373571001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16495678544506883582380667 24743517816760325373571001)
    ·
      refine ⟨18557638362570244030178251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24743517816760325373571001 18557638362570244030178251)
      ·
        refine ⟨27836457543855366045267377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18557638362570244030178251 27836457543855366045267377)
        ·
          refine ⟨20877343157891524533950533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27836457543855366045267377 20877343157891524533950533)
          ·
            refine ⟨3914501842104660850115725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20877343157891524533950533 3914501842104660850115725)
            ·
              refine ⟨1467938190789247818793397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3914501842104660850115725 1467938190789247818793397)
              ·
                refine ⟨137619205386491983011881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1467938190789247818793397 137619205386491983011881)
                ·
                  rfl

theorem cell19_452271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 5].length) (baseStart_452271 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_452271 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_452271 prefixEnd_452271 := by exact prefixLift 452271
  have htrace : WordTrace (prefixWord ++ tailWord_452271) baseStart_452271 baseEnd_452271 := by
    simpa [prefixWord, tailWord_452271, baseEnd_452271] using wordTrace_append hprefix tailTrace_452271
  have hstable : (prefixWord ++ tailWord_452271).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452271).length < 2 ^ (prefixWord ++ tailWord_452271).sum := by decide
  have hdescent : baseEnd_452271 < baseStart_452271 := by decide
  rcases family_descends (prefixWord ++ tailWord_452271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452383 : List Nat := [1, 1, 2, 4, 2, 1, 5, 3]
def baseStart_452383 : Nat := 118140960795 + 452383 * 2 ^ 59
def prefixEnd_452383 : Nat := 4983230072969 + 3 ^ 40 * 452383 * 2
def baseEnd_452383 : Nat := 137653285287708908522687

theorem tailTrace_452383 : CollatzResearch.WordTrace tailWord_452383 prefixEnd_452383 137653285287708908522687 := by
  unfold tailWord_452383
  simp only [CollatzResearch.WordTrace]
  refine ⟨16499763520101126710457803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10999842346734084473638535 16499763520101126710457803)
  ·
    refine ⟨24749645280151690065686705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16499763520101126710457803 24749645280151690065686705)
    ·
      refine ⟨18562233960113767549265029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24749645280151690065686705 18562233960113767549265029)
      ·
        refine ⟨3480418867521331415487193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18562233960113767549265029 3480418867521331415487193)
        ·
          refine ⟨2610314150640998561615395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3480418867521331415487193 2610314150640998561615395)
          ·
            refine ⟨3915471225961497842423093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2610314150640998561615395 3915471225961497842423093)
            ·
              refine ⟨367075427433890422727165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3915471225961497842423093 367075427433890422727165)
              ·
                refine ⟨137653285287708908522687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 367075427433890422727165 137653285287708908522687)
                ·
                  rfl

theorem cell19_452383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 5, 3].length) (baseStart_452383 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_452383 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_452383 prefixEnd_452383 := by exact prefixLift 452383
  have htrace : WordTrace (prefixWord ++ tailWord_452383) baseStart_452383 baseEnd_452383 := by
    simpa [prefixWord, tailWord_452383, baseEnd_452383] using wordTrace_append hprefix tailTrace_452383
  have hstable : (prefixWord ++ tailWord_452383).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452383).length < 2 ^ (prefixWord ++ tailWord_452383).sum := by decide
  have hdescent : baseEnd_452383 < baseStart_452383 := by decide
  rcases family_descends (prefixWord ++ tailWord_452383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452442 : List Nat := [3, 1, 1, 2, 1, 3, 3, 5]
def baseStart_452442 : Nat := 118140960795 + 452442 * 2 ^ 59
def prefixEnd_452442 : Nat := 4983230072969 + 3 ^ 40 * 452442 * 2
def baseEnd_452442 : Nat := 137671238092814253211415

theorem tailTrace_452442 : CollatzResearch.WordTrace tailWord_452442 prefixEnd_452442 137671238092814253211415 := by
  unfold tailWord_452442
  simp only [CollatzResearch.WordTrace]
  refine ⟨4125478856721844946713895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11001276951258253191237053 4125478856721844946713895)
  ·
    refine ⟨6188218285082767420070843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4125478856721844946713895 6188218285082767420070843)
    ·
      refine ⟨9282327427624151130106265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6188218285082767420070843 9282327427624151130106265)
      ·
        refine ⟨6961745570718113347579699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9282327427624151130106265 6961745570718113347579699)
        ·
          refine ⟨10442618356077170021369549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6961745570718113347579699 10442618356077170021369549)
          ·
            refine ⟨3915981883528938758013581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10442618356077170021369549 3915981883528938758013581)
            ·
              refine ⟨1468493206323352034255093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3915981883528938758013581 1468493206323352034255093)
              ·
                refine ⟨137671238092814253211415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1468493206323352034255093 137671238092814253211415)
                ·
                  rfl

theorem cell19_452442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 5].length) (baseStart_452442 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_452442 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_452442 prefixEnd_452442 := by exact prefixLift 452442
  have htrace : WordTrace (prefixWord ++ tailWord_452442) baseStart_452442 baseEnd_452442 := by
    simpa [prefixWord, tailWord_452442, baseEnd_452442] using wordTrace_append hprefix tailTrace_452442
  have hstable : (prefixWord ++ tailWord_452442).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452442).length < 2 ^ (prefixWord ++ tailWord_452442).sum := by decide
  have hdescent : baseEnd_452442 < baseStart_452442 := by decide
  rcases family_descends (prefixWord ++ tailWord_452442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452461 : List Nat := [1, 5, 1, 1, 1, 1, 9]
def baseStart_452461 : Nat := 118140960795 + 452461 * 2 ^ 59
def prefixEnd_452461 : Nat := 4983230072969 + 3 ^ 40 * 452461 * 2
def baseEnd_452461 : Nat := 45892339834875946263047

theorem tailTrace_452461 : CollatzResearch.WordTrace tailWord_452461 prefixEnd_452461 45892339834875946263047 := by
  unfold tailWord_452461
  simp only [CollatzResearch.WordTrace]
  refine ⟨16502608413818546031797237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11001738942545697354531491 16502608413818546031797237)
  ·
    refine ⟨1547119538795488690480991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16502608413818546031797237 1547119538795488690480991)
    ·
      refine ⟨2320679308193233035721487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1547119538795488690480991 2320679308193233035721487)
      ·
        refine ⟨3481018962289849553582231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2320679308193233035721487 3481018962289849553582231)
        ·
          refine ⟨5221528443434774330373347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3481018962289849553582231 5221528443434774330373347)
          ·
            refine ⟨7832292665152161495560021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5221528443434774330373347 7832292665152161495560021)
            ·
              refine ⟨45892339834875946263047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7832292665152161495560021 45892339834875946263047)
              ·
                rfl

theorem cell19_452461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 9].length) (baseStart_452461 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_452461 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_452461 prefixEnd_452461 := by exact prefixLift 452461
  have htrace : WordTrace (prefixWord ++ tailWord_452461) baseStart_452461 baseEnd_452461 := by
    simpa [prefixWord, tailWord_452461, baseEnd_452461] using wordTrace_append hprefix tailTrace_452461
  have hstable : (prefixWord ++ tailWord_452461).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452461).length < 2 ^ (prefixWord ++ tailWord_452461).sum := by decide
  have hdescent : baseEnd_452461 < baseStart_452461 := by decide
  rcases family_descends (prefixWord ++ tailWord_452461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452480 : List Nat := [2, 1, 1, 2, 1, 2, 6, 4]
def baseStart_452480 : Nat := 118140960795 + 452480 * 2 ^ 59
def prefixEnd_452480 : Nat := 4983230072969 + 3 ^ 40 * 452480 * 2
def baseEnd_452480 : Nat := 137682800916441424366867

theorem tailTrace_452480 : CollatzResearch.WordTrace tailWord_452480 prefixEnd_452480 137682800916441424366867 := by
  unfold tailWord_452480
  simp only [CollatzResearch.WordTrace]
  refine ⟨8251650700374856138369447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11002200933833141517825929 8251650700374856138369447)
  ·
    refine ⟨12377476050562284207554171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8251650700374856138369447 12377476050562284207554171)
    ·
      refine ⟨18566214075843426311331257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12377476050562284207554171 18566214075843426311331257)
      ·
        refine ⟨13924660556882569733498443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18566214075843426311331257 13924660556882569733498443)
        ·
          refine ⟨20886990835323854600247665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13924660556882569733498443 20886990835323854600247665)
          ·
            refine ⟨15665243126492890950185749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20886990835323854600247665 15665243126492890950185749)
            ·
              refine ⟨734308271554354263289957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15665243126492890950185749 734308271554354263289957)
              ·
                refine ⟨137682800916441424366867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 734308271554354263289957 137682800916441424366867)
                ·
                  rfl

theorem cell19_452480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 4].length) (baseStart_452480 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_452480 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_452480 prefixEnd_452480 := by exact prefixLift 452480
  have htrace : WordTrace (prefixWord ++ tailWord_452480) baseStart_452480 baseEnd_452480 := by
    simpa [prefixWord, tailWord_452480, baseEnd_452480] using wordTrace_append hprefix tailTrace_452480
  have hstable : (prefixWord ++ tailWord_452480).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452480).length < 2 ^ (prefixWord ++ tailWord_452480).sum := by decide
  have hdescent : baseEnd_452480 < baseStart_452480 := by decide
  rcases family_descends (prefixWord ++ tailWord_452480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452573 : List Nat := [1, 4, 3, 1, 3, 1, 6]
def baseStart_452573 : Nat := 118140960795 + 452573 * 2 ^ 59
def prefixEnd_452573 : Nat := 4983230072969 + 3 ^ 40 * 452573 * 2
def baseEnd_452573 : Nat := 45903699801948254766649

theorem tailTrace_452573 : CollatzResearch.WordTrace tailWord_452573 prefixEnd_452573 45903699801948254766649 := by
  unfold tailWord_452573
  simp only [CollatzResearch.WordTrace]
  refine ⟨16506693389412789159874373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11004462259608526106582915 16506693389412789159874373)
  ·
    refine ⟨3095005010514897967476445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16506693389412789159874373 3095005010514897967476445)
    ·
      refine ⟨1160626878943086737803667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3095005010514897967476445 1160626878943086737803667)
      ·
        refine ⟨1740940318414630106705501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1160626878943086737803667 1740940318414630106705501)
        ·
          refine ⟨652852619405486290014563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1740940318414630106705501 652852619405486290014563)
          ·
            refine ⟨979278929108229435021845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 652852619405486290014563 979278929108229435021845)
            ·
              refine ⟨45903699801948254766649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 979278929108229435021845 45903699801948254766649)
              ·
                rfl

theorem cell19_452573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 6].length) (baseStart_452573 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_452573 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_452573 prefixEnd_452573 := by exact prefixLift 452573
  have htrace : WordTrace (prefixWord ++ tailWord_452573) baseStart_452573 baseEnd_452573 := by
    simpa [prefixWord, tailWord_452573, baseEnd_452573] using wordTrace_append hprefix tailTrace_452573
  have hstable : (prefixWord ++ tailWord_452573).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452573).length < 2 ^ (prefixWord ++ tailWord_452573).sum := by decide
  have hdescent : baseEnd_452573 < baseStart_452573 := by decide
  rcases family_descends (prefixWord ++ tailWord_452573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452575 : List Nat := [1, 1, 2, 3, 4, 2, 6]
def baseStart_452575 : Nat := 118140960795 + 452575 * 2 ^ 59
def prefixEnd_452575 : Nat := 4983230072969 + 3 ^ 40 * 452575 * 2
def baseEnd_452575 : Nat := 45903902658503117418499

theorem tailTrace_452575 : CollatzResearch.WordTrace tailWord_452575 prefixEnd_452575 45903902658503117418499 := by
  unfold tailWord_452575
  simp only [CollatzResearch.WordTrace]
  refine ⟨16506766335405543501447179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11004510890270362334298119 16506766335405543501447179)
  ·
    refine ⟨24760149503108315252170769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16506766335405543501447179 24760149503108315252170769)
    ·
      refine ⟨18570112127331236439128077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24760149503108315252170769 18570112127331236439128077)
      ·
        refine ⟨6963792047749213664673029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18570112127331236439128077 6963792047749213664673029)
        ·
          refine ⟨1305711008952977562126193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6963792047749213664673029 1305711008952977562126193)
          ·
            refine ⟨979283256714733171594645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1305711008952977562126193 979283256714733171594645)
            ·
              refine ⟨45903902658503117418499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 979283256714733171594645 45903902658503117418499)
              ·
                rfl

theorem cell19_452575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 6].length) (baseStart_452575 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_452575 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_452575 prefixEnd_452575 := by exact prefixLift 452575
  have htrace : WordTrace (prefixWord ++ tailWord_452575) baseStart_452575 baseEnd_452575 := by
    simpa [prefixWord, tailWord_452575, baseEnd_452575] using wordTrace_append hprefix tailTrace_452575
  have hstable : (prefixWord ++ tailWord_452575).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452575).length < 2 ^ (prefixWord ++ tailWord_452575).sum := by decide
  have hdescent : baseEnd_452575 < baseStart_452575 := by decide
  rcases family_descends (prefixWord ++ tailWord_452575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452613 : List Nat := [1, 3, 1, 1, 2, 5, 1, 5]
def baseStart_452613 : Nat := 118140960795 + 452613 * 2 ^ 59
def prefixEnd_452613 : Nat := 4983230072969 + 3 ^ 40 * 452613 * 2
def baseEnd_452613 : Nat := 137723270799136523410949

theorem tailTrace_452613 : CollatzResearch.WordTrace tailWord_452613 prefixEnd_452613 137723270799136523410949 := by
  unfold tailWord_452613
  simp only [CollatzResearch.WordTrace]
  refine ⟨16508152309267875991330493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11005434872845250660886995 16508152309267875991330493)
  ·
    refine ⟨6190557115975453496748935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16508152309267875991330493 6190557115975453496748935)
    ·
      refine ⟨9285835673963180245123403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6190557115975453496748935 9285835673963180245123403)
      ·
        refine ⟨13928753510944770367685105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9285835673963180245123403 13928753510944770367685105)
        ·
          refine ⟨10446565133208577775763829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13928753510944770367685105 10446565133208577775763829)
          ·
            refine ⟨979365481238304166477859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10446565133208577775763829 979365481238304166477859)
            ·
              refine ⟨1469048221857456249716789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 979365481238304166477859 1469048221857456249716789)
              ·
                refine ⟨137723270799136523410949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1469048221857456249716789 137723270799136523410949)
                ·
                  rfl

theorem cell19_452613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 5].length) (baseStart_452613 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_452613 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_452613 prefixEnd_452613 := by exact prefixLift 452613
  have htrace : WordTrace (prefixWord ++ tailWord_452613) baseStart_452613 baseEnd_452613 := by
    simpa [prefixWord, tailWord_452613, baseEnd_452613] using wordTrace_append hprefix tailTrace_452613
  have hstable : (prefixWord ++ tailWord_452613).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452613).length < 2 ^ (prefixWord ++ tailWord_452613).sum := by decide
  have hdescent : baseEnd_452613 < baseStart_452613 := by decide
  rcases family_descends (prefixWord ++ tailWord_452613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452647 : List Nat := [1, 1, 7, 1, 2, 1, 2, 4]
def baseStart_452647 : Nat := 118140960795 + 452647 * 2 ^ 59
def prefixEnd_452647 : Nat := 4983230072969 + 3 ^ 40 * 452647 * 2
def baseEnd_452647 : Nat := 137733616483434518655301

theorem tailTrace_452647 : CollatzResearch.WordTrace tailWord_452647 prefixEnd_452647 137733616483434518655301 := by
  unfold tailWord_452647
  simp only [CollatzResearch.WordTrace]
  refine ⟨16509392391144699798068195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11006261594096466532045463 16509392391144699798068195)
  ·
    refine ⟨24764088586717049697102293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16509392391144699798068195 24764088586717049697102293)
    ·
      refine ⟨580408326251180852275835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 24764088586717049697102293 580408326251180852275835)
      ·
        refine ⟨870612489376771278413753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 580408326251180852275835 870612489376771278413753)
        ·
          refine ⟨652959367032578458810315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 870612489376771278413753 652959367032578458810315)
          ·
            refine ⟨979439050548867688215473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 652959367032578458810315 979439050548867688215473)
            ·
              refine ⟨734579287911650766161605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 979439050548867688215473 734579287911650766161605)
              ·
                refine ⟨137733616483434518655301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 734579287911650766161605 137733616483434518655301)
                ·
                  rfl

theorem cell19_452647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 4].length) (baseStart_452647 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_452647 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_452647 prefixEnd_452647 := by exact prefixLift 452647
  have htrace : WordTrace (prefixWord ++ tailWord_452647) baseStart_452647 baseEnd_452647 := by
    simpa [prefixWord, tailWord_452647, baseEnd_452647] using wordTrace_append hprefix tailTrace_452647
  have hstable : (prefixWord ++ tailWord_452647).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452647).length < 2 ^ (prefixWord ++ tailWord_452647).sum := by decide
  have hdescent : baseEnd_452647 < baseStart_452647 := by decide
  rcases family_descends (prefixWord ++ tailWord_452647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452708 : List Nat := [2, 3, 1, 1, 2, 1, 5, 4]
def baseStart_452708 : Nat := 118140960795 + 452708 * 2 ^ 59
def prefixEnd_452708 : Nat := 4983230072969 + 3 ^ 40 * 452708 * 2
def baseEnd_452708 : Nat := 137752177858204451299579

theorem tailTrace_452708 : CollatzResearch.WordTrace tailWord_452708 prefixEnd_452708 137752177858204451299579 := by
  unfold tailWord_452708
  simp only [CollatzResearch.WordTrace]
  refine ⟨8255808621961853608019389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11007744829282471477359185 8255808621961853608019389)
  ·
    refine ⟨3095928233235695103007271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8255808621961853608019389 3095928233235695103007271)
    ·
      refine ⟨4643892349853542654510907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3095928233235695103007271 4643892349853542654510907)
      ·
        refine ⟨6965838524780313981766361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4643892349853542654510907 6965838524780313981766361)
        ·
          refine ⟨5224378893585235486324771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6965838524780313981766361 5224378893585235486324771)
          ·
            refine ⟨7836568340377853229487157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5224378893585235486324771 7836568340377853229487157)
            ·
              refine ⟨734678281910423740264421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7836568340377853229487157 734678281910423740264421)
              ·
                refine ⟨137752177858204451299579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 734678281910423740264421 137752177858204451299579)
                ·
                  rfl

theorem cell19_452708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 4].length) (baseStart_452708 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_452708 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_452708 prefixEnd_452708 := by exact prefixLift 452708
  have htrace : WordTrace (prefixWord ++ tailWord_452708) baseStart_452708 baseEnd_452708 := by
    simpa [prefixWord, tailWord_452708, baseEnd_452708] using wordTrace_append hprefix tailTrace_452708
  have hstable : (prefixWord ++ tailWord_452708).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452708).length < 2 ^ (prefixWord ++ tailWord_452708).sum := by decide
  have hdescent : baseEnd_452708 < baseStart_452708 := by decide
  rcases family_descends (prefixWord ++ tailWord_452708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452746 : List Nat := [3, 1, 2, 3, 1, 3, 6]
def baseStart_452746 : Nat := 118140960795 + 452746 * 2 ^ 59
def prefixEnd_452746 : Nat := 4983230072969 + 3 ^ 40 * 452746 * 2
def baseEnd_452746 : Nat := 45921246893943874151677

theorem tailTrace_452746 : CollatzResearch.WordTrace tailWord_452746 prefixEnd_452746 45921246893943874151677 := by
  unfold tailWord_452746
  simp only [CollatzResearch.WordTrace]
  refine ⟨4128250804446509926480523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11008668811857359803948061 4128250804446509926480523)
  ·
    refine ⟨6192376206669764889720785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4128250804446509926480523 6192376206669764889720785)
    ·
      refine ⟨4644282155002323667290589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6192376206669764889720785 4644282155002323667290589)
      ·
        refine ⟨1741605808125871375233971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4644282155002323667290589 1741605808125871375233971)
        ·
          refine ⟨2612408712188807062850957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1741605808125871375233971 2612408712188807062850957)
          ·
            refine ⟨979653267070802648569109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2612408712188807062850957 979653267070802648569109)
            ·
              refine ⟨45921246893943874151677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 979653267070802648569109 45921246893943874151677)
              ·
                rfl

theorem cell19_452746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 6].length) (baseStart_452746 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_452746 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_452746 prefixEnd_452746 := by exact prefixLift 452746
  have htrace : WordTrace (prefixWord ++ tailWord_452746) baseStart_452746 baseEnd_452746 := by
    simpa [prefixWord, tailWord_452746, baseEnd_452746] using wordTrace_append hprefix tailTrace_452746
  have hstable : (prefixWord ++ tailWord_452746).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452746).length < 2 ^ (prefixWord ++ tailWord_452746).sum := by decide
  have hdescent : baseEnd_452746 < baseStart_452746 := by decide
  rcases family_descends (prefixWord ++ tailWord_452746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452778 : List Nat := [3, 1, 5, 1, 2, 2, 2, 3]
def baseStart_452778 : Nat := 118140960795 + 452778 * 2 ^ 59
def prefixEnd_452778 : Nat := 4983230072969 + 3 ^ 40 * 452778 * 2
def baseEnd_452778 : Nat := 137773477796465029743833

theorem tailTrace_452778 : CollatzResearch.WordTrace tailWord_452778 prefixEnd_452778 137773477796465029743833 := by
  unfold tailWord_452778
  simp only [CollatzResearch.WordTrace]
  refine ⟨4128542588417527292771747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11009446902446739447391325 4128542588417527292771747)
  ·
    refine ⟨6192813882626290939157621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4128542588417527292771747 6192813882626290939157621)
    ·
      refine ⟨580576301496214775546027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6192813882626290939157621 580576301496214775546027)
      ·
        refine ⟨870864452244322163319041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 580576301496214775546027 870864452244322163319041)
        ·
          refine ⟨653148339183241622489281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 870864452244322163319041 653148339183241622489281)
          ·
            refine ⟨489861254387431216866961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 653148339183241622489281 489861254387431216866961)
            ·
              refine ⟨367395940790573412650221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 489861254387431216866961 367395940790573412650221)
              ·
                refine ⟨137773477796465029743833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 367395940790573412650221 137773477796465029743833)
                ·
                  rfl

theorem cell19_452778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 2, 3].length) (baseStart_452778 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_452778 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_452778 prefixEnd_452778 := by exact prefixLift 452778
  have htrace : WordTrace (prefixWord ++ tailWord_452778) baseStart_452778 baseEnd_452778 := by
    simpa [prefixWord, tailWord_452778, baseEnd_452778] using wordTrace_append hprefix tailTrace_452778
  have hstable : (prefixWord ++ tailWord_452778).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452778).length < 2 ^ (prefixWord ++ tailWord_452778).sum := by decide
  have hdescent : baseEnd_452778 < baseStart_452778 := by decide
  rcases family_descends (prefixWord ++ tailWord_452778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452805 : List Nat := [1, 3, 1, 1, 1, 1, 11]
def baseStart_452805 : Nat := 118140960795 + 452805 * 2 ^ 59
def prefixEnd_452805 : Nat := 4983230072969 + 3 ^ 40 * 452805 * 2
def baseEnd_452805 : Nat := 45927231162312322381253

theorem tailTrace_452805 : CollatzResearch.WordTrace tailWord_452805 prefixEnd_452805 45927231162312322381253 := by
  unfold tailWord_452805
  simp only [CollatzResearch.WordTrace]
  refine ⟨16515155124572292782319869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11010103416381528521546579 16515155124572292782319869)
  ·
    refine ⟨6193183171714609793369951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16515155124572292782319869 6193183171714609793369951)
    ·
      refine ⟨9289774757571914690054927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6193183171714609793369951 9289774757571914690054927)
      ·
        refine ⟨13934662136357872035082391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9289774757571914690054927 13934662136357872035082391)
        ·
          refine ⟨20901993204536808052623587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13934662136357872035082391 20901993204536808052623587)
          ·
            refine ⟨31352989806805212078935381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20901993204536808052623587 31352989806805212078935381)
            ·
              refine ⟨45927231162312322381253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 31352989806805212078935381 45927231162312322381253)
              ·
                rfl

theorem cell19_452805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 11].length) (baseStart_452805 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_452805 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_452805 prefixEnd_452805 := by exact prefixLift 452805
  have htrace : WordTrace (prefixWord ++ tailWord_452805) baseStart_452805 baseEnd_452805 := by
    simpa [prefixWord, tailWord_452805, baseEnd_452805] using wordTrace_append hprefix tailTrace_452805
  have hstable : (prefixWord ++ tailWord_452805).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452805).length < 2 ^ (prefixWord ++ tailWord_452805).sum := by decide
  have hdescent : baseEnd_452805 < baseStart_452805 := by decide
  rcases family_descends (prefixWord ++ tailWord_452805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452843 : List Nat := [1, 1, 1, 1, 2, 5, 1, 7]
def baseStart_452843 : Nat := 118140960795 + 452843 * 2 ^ 59
def prefixEnd_452843 : Nat := 4983230072969 + 3 ^ 40 * 452843 * 2
def baseEnd_452843 : Nat := 137793256310564138299211

theorem tailTrace_452843 : CollatzResearch.WordTrace tailWord_452843 prefixEnd_452843 137793256310564138299211 := by
  unfold tailWord_452843
  simp only [CollatzResearch.WordTrace]
  refine ⟨16516541098434625272203183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11011027398956416848135455 16516541098434625272203183)
  ·
    refine ⟨24774811647651937908304775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16516541098434625272203183 24774811647651937908304775)
    ·
      refine ⟨37162217471477906862457163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24774811647651937908304775 37162217471477906862457163)
      ·
        refine ⟨55743326207216860293685745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37162217471477906862457163 55743326207216860293685745)
        ·
          refine ⟨41807494655412645220264309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55743326207216860293685745 41807494655412645220264309)
          ·
            refine ⟨3919452623944935489399779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41807494655412645220264309 3919452623944935489399779)
            ·
              refine ⟨5879178935917403234099669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3919452623944935489399779 5879178935917403234099669)
              ·
                refine ⟨137793256310564138299211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5879178935917403234099669 137793256310564138299211)
                ·
                  rfl

theorem cell19_452843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 7].length) (baseStart_452843 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_452843 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_452843 prefixEnd_452843 := by exact prefixLift 452843
  have htrace : WordTrace (prefixWord ++ tailWord_452843) baseStart_452843 baseEnd_452843 := by
    simpa [prefixWord, tailWord_452843, baseEnd_452843] using wordTrace_append hprefix tailTrace_452843
  have hstable : (prefixWord ++ tailWord_452843).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452843).length < 2 ^ (prefixWord ++ tailWord_452843).sum := by decide
  have hdescent : baseEnd_452843 < baseStart_452843 := by decide
  rcases family_descends (prefixWord ++ tailWord_452843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452896 : List Nat := [2, 1, 1, 5, 2, 2, 3, 3]
def baseStart_452896 : Nat := 118140960795 + 452896 * 2 ^ 59
def prefixEnd_452896 : Nat := 4983230072969 + 3 ^ 40 * 452896 * 2
def baseEnd_452896 : Nat := 137809383406675719121289

theorem tailTrace_452896 : CollatzResearch.WordTrace tailWord_452896 prefixEnd_452896 137809383406675719121289 := by
  unfold tailWord_452896
  simp only [CollatzResearch.WordTrace]
  refine ⟨8259237083621307661941271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11012316111495076882588361 8259237083621307661941271)
  ·
    refine ⟨12388855625431961492911907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8259237083621307661941271 12388855625431961492911907)
    ·
      refine ⟨18583283438147942239367861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12388855625431961492911907 18583283438147942239367861)
      ·
        refine ⟨1742182822326369584940737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18583283438147942239367861 1742182822326369584940737)
        ·
          refine ⟨1306637116744777188705553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1742182822326369584940737 1306637116744777188705553)
          ·
            refine ⟨979977837558582891529165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1306637116744777188705553 979977837558582891529165)
            ·
              refine ⟨367491689084468584323437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 979977837558582891529165 367491689084468584323437)
              ·
                refine ⟨137809383406675719121289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 367491689084468584323437 137809383406675719121289)
                ·
                  rfl

theorem cell19_452896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 3, 3].length) (baseStart_452896 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_452896 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_452896 prefixEnd_452896 := by exact prefixLift 452896
  have htrace : WordTrace (prefixWord ++ tailWord_452896) baseStart_452896 baseEnd_452896 := by
    simpa [prefixWord, tailWord_452896, baseEnd_452896] using wordTrace_append hprefix tailTrace_452896
  have hstable : (prefixWord ++ tailWord_452896).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452896).length < 2 ^ (prefixWord ++ tailWord_452896).sum := by decide
  have hdescent : baseEnd_452896 < baseStart_452896 := by decide
  rcases family_descends (prefixWord ++ tailWord_452896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452972 : List Nat := [2, 2, 1, 1, 7, 1, 5]
def baseStart_452972 : Nat := 118140960795 + 452972 * 2 ^ 59
def prefixEnd_452972 : Nat := 4983230072969 + 3 ^ 40 * 452972 * 2
def baseEnd_452972 : Nat := 45944169684643353810731

theorem tailTrace_452972 : CollatzResearch.WordTrace tailWord_452972 prefixEnd_452972 45944169684643353810731 := by
  unfold tailWord_452972
  simp only [CollatzResearch.WordTrace]
  refine ⟨8260623057483640151824585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11014164076644853535766113 8260623057483640151824585)
  ·
    refine ⟨6195467293112730113868439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8260623057483640151824585 6195467293112730113868439)
    ·
      refine ⟨9293200939669095170802659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6195467293112730113868439 9293200939669095170802659)
      ·
        refine ⟨13939801409503642756203989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9293200939669095170802659 13939801409503642756203989)
        ·
          refine ⟨326714095535241627098531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 13939801409503642756203989 326714095535241627098531)
          ·
            refine ⟨490071143302862440647797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 326714095535241627098531 490071143302862440647797)
            ·
              refine ⟨45944169684643353810731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 490071143302862440647797 45944169684643353810731)
              ·
                rfl

theorem cell19_452972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 5].length) (baseStart_452972 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_452972 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_452972 prefixEnd_452972 := by exact prefixLift 452972
  have htrace : WordTrace (prefixWord ++ tailWord_452972) baseStart_452972 baseEnd_452972 := by
    simpa [prefixWord, tailWord_452972, baseEnd_452972] using wordTrace_append hprefix tailTrace_452972
  have hstable : (prefixWord ++ tailWord_452972).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452972).length < 2 ^ (prefixWord ++ tailWord_452972).sum := by decide
  have hdescent : baseEnd_452972 < baseStart_452972 := by decide
  rcases family_descends (prefixWord ++ tailWord_452972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452976 : List Nat := [2, 1, 1, 1, 4, 3, 7]
def baseStart_452976 : Nat := 118140960795 + 452976 * 2 ^ 59
def prefixEnd_452976 : Nat := 4983230072969 + 3 ^ 40 * 452976 * 2
def baseEnd_452976 : Nat := 45944575397753079114431

theorem tailTrace_452976 : CollatzResearch.WordTrace tailWord_452976 prefixEnd_452976 45944575397753079114431 := by
  unfold tailWord_452976
  simp only [CollatzResearch.WordTrace]
  refine ⟨8260696003476394493397391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11014261337968525991196521 8260696003476394493397391)
  ·
    refine ⟨12391044005214591740096087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8260696003476394493397391 12391044005214591740096087)
    ·
      refine ⟨18586566007821887610144131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12391044005214591740096087 18586566007821887610144131)
      ·
        refine ⟨27879849011732831415216197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18586566007821887610144131 27879849011732831415216197)
        ·
          refine ⟨5227471689699905890353037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27879849011732831415216197 5227471689699905890353037)
          ·
            refine ⟨1960301883637464708882389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5227471689699905890353037 1960301883637464708882389)
            ·
              refine ⟨45944575397753079114431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1960301883637464708882389 45944575397753079114431)
              ·
                rfl

theorem cell19_452976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 7].length) (baseStart_452976 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_452976 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_452976 prefixEnd_452976 := by exact prefixLift 452976
  have htrace : WordTrace (prefixWord ++ tailWord_452976) baseStart_452976 baseEnd_452976 := by
    simpa [prefixWord, tailWord_452976, baseEnd_452976] using wordTrace_append hprefix tailTrace_452976
  have hstable : (prefixWord ++ tailWord_452976).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452976).length < 2 ^ (prefixWord ++ tailWord_452976).sum := by decide
  have hdescent : baseEnd_452976 < baseStart_452976 := by decide
  rcases family_descends (prefixWord ++ tailWord_452976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_452993 : List Nat := [1, 2, 4, 3, 1, 1, 1, 6]
def baseStart_452993 : Nat := 118140960795 + 452993 * 2 ^ 59
def prefixEnd_452993 : Nat := 4983230072969 + 3 ^ 40 * 452993 * 2
def baseEnd_452993 : Nat := 137838899035408234965469

theorem tailTrace_452993 : CollatzResearch.WordTrace tailWord_452993 prefixEnd_452993 137838899035408234965469 := by
  unfold tailWord_452993
  simp only [CollatzResearch.WordTrace]
  refine ⟨16522012047891200890163633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11014674698594133926775755 16522012047891200890163633)
  ·
    refine ⟨12391509035918400667622725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16522012047891200890163633 12391509035918400667622725)
    ·
      refine ⟨2323407944234700125179261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12391509035918400667622725 2323407944234700125179261)
      ·
        refine ⟨871277979088012546942223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2323407944234700125179261 871277979088012546942223)
        ·
          refine ⟨1306916968632018820413335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 871277979088012546942223 1306916968632018820413335)
          ·
            refine ⟨1960375452948028230620003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1306916968632018820413335 1960375452948028230620003)
            ·
              refine ⟨2940563179422042345930005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1960375452948028230620003 2940563179422042345930005)
              ·
                refine ⟨137838899035408234965469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2940563179422042345930005 137838899035408234965469)
                ·
                  rfl

theorem cell19_452993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 6].length) (baseStart_452993 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_452993 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_452993 prefixEnd_452993 := by exact prefixLift 452993
  have htrace : WordTrace (prefixWord ++ tailWord_452993) baseStart_452993 baseEnd_452993 := by
    simpa [prefixWord, tailWord_452993, baseEnd_452993] using wordTrace_append hprefix tailTrace_452993
  have hstable : (prefixWord ++ tailWord_452993).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_452993).length < 2 ^ (prefixWord ++ tailWord_452993).sum := by decide
  have hdescent : baseEnd_452993 < baseStart_452993 := by decide
  rcases family_descends (prefixWord ++ tailWord_452993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453044 : List Nat := [2, 5, 2, 2, 1, 2, 1, 4]
def baseStart_453044 : Nat := 118140960795 + 453044 * 2 ^ 59
def prefixEnd_453044 : Nat := 4983230072969 + 3 ^ 40 * 453044 * 2
def baseEnd_453044 : Nat := 137854417561855227831997

theorem tailTrace_453044 : CollatzResearch.WordTrace tailWord_453044 prefixEnd_453044 137854417561855227831997 := by
  unfold tailWord_453044
  simp only [CollatzResearch.WordTrace]
  refine ⟨8261936085353218300135093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11015914780470957733513457 8261936085353218300135093)
  ·
    refine ⟨774556508001864215637665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8261936085353218300135093 774556508001864215637665)
    ·
      refine ⟨580917381001398161728249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 774556508001864215637665 580917381001398161728249)
      ·
        refine ⟨435688035751048621296187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 580917381001398161728249 435688035751048621296187)
        ·
          refine ⟨653532053626572931944281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 435688035751048621296187 653532053626572931944281)
          ·
            refine ⟨490149040219929698958211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 653532053626572931944281 490149040219929698958211)
            ·
              refine ⟨735223560329894548437317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 490149040219929698958211 735223560329894548437317)
              ·
                refine ⟨137854417561855227831997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 735223560329894548437317 137854417561855227831997)
                ·
                  rfl

theorem cell19_453044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 1, 4].length) (baseStart_453044 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_453044 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_453044 prefixEnd_453044 := by exact prefixLift 453044
  have htrace : WordTrace (prefixWord ++ tailWord_453044) baseStart_453044 baseEnd_453044 := by
    simpa [prefixWord, tailWord_453044, baseEnd_453044] using wordTrace_append hprefix tailTrace_453044
  have hstable : (prefixWord ++ tailWord_453044).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453044).length < 2 ^ (prefixWord ++ tailWord_453044).sum := by decide
  have hdescent : baseEnd_453044 < baseStart_453044 := by decide
  rcases family_descends (prefixWord ++ tailWord_453044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453124 : List Nat := [2, 3, 2, 3, 1, 1, 4, 3]
def baseStart_453124 : Nat := 118140960795 + 453124 * 2 ^ 59
def prefixEnd_453124 : Nat := 4983230072969 + 3 ^ 40 * 453124 * 2
def baseEnd_453124 : Nat := 137878760348438746054001

theorem tailTrace_453124 : CollatzResearch.WordTrace tailWord_453124 prefixEnd_453124 137878760348438746054001 := by
  unfold tailWord_453124
  simp only [CollatzResearch.WordTrace]
  refine ⟨8263395005208305131591213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11017860006944406842121617 8263395005208305131591213)
  ·
    refine ⟨3098773126953114424346705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8263395005208305131591213 3098773126953114424346705)
    ·
      refine ⟨2324079845214835818260029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3098773126953114424346705 2324079845214835818260029)
      ·
        refine ⟨871529941955563431847511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2324079845214835818260029 871529941955563431847511)
        ·
          refine ⟨1307294912933345147771267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 871529941955563431847511 1307294912933345147771267)
          ·
            refine ⟨1960942369400017721656901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1307294912933345147771267 1960942369400017721656901)
            ·
              refine ⟨367676694262503322810669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1960942369400017721656901 367676694262503322810669)
              ·
                refine ⟨137878760348438746054001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 367676694262503322810669 137878760348438746054001)
                ·
                  rfl

theorem cell19_453124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 4, 3].length) (baseStart_453124 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_453124 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_453124 prefixEnd_453124 := by exact prefixLift 453124
  have htrace : WordTrace (prefixWord ++ tailWord_453124) baseStart_453124 baseEnd_453124 := by
    simpa [prefixWord, tailWord_453124, baseEnd_453124] using wordTrace_append hprefix tailTrace_453124
  have hstable : (prefixWord ++ tailWord_453124).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453124).length < 2 ^ (prefixWord ++ tailWord_453124).sum := by decide
  have hdescent : baseEnd_453124 < baseStart_453124 := by decide
  rcases family_descends (prefixWord ++ tailWord_453124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453143 : List Nat := [1, 1, 3, 6, 1, 2, 5]
def baseStart_453143 : Nat := 118140960795 + 453143 * 2 ^ 59
def prefixEnd_453143 : Nat := 4983230072969 + 3 ^ 40 * 453143 * 2
def baseEnd_453143 : Nat := 45961513920084110543909

theorem tailTrace_453143 : CollatzResearch.WordTrace tailWord_453143 prefixEnd_453143 45961513920084110543909 := by
  unfold tailWord_453143
  simp only [CollatzResearch.WordTrace]
  refine ⟨16527482997347776508124083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11018321998231851005416055 16527482997347776508124083)
  ·
    refine ⟨24791224496021664762186125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16527482997347776508124083 24791224496021664762186125)
    ·
      refine ⟨9296709186008124285819797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24791224496021664762186125 9296709186008124285819797)
      ·
        refine ⟨435783243094130825897803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 9296709186008124285819797 435783243094130825897803)
        ·
          refine ⟨653674864641196238846705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 435783243094130825897803 653674864641196238846705)
          ·
            refine ⟨490256148480897179135029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 653674864641196238846705 490256148480897179135029)
            ·
              refine ⟨45961513920084110543909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 490256148480897179135029 45961513920084110543909)
              ·
                rfl

theorem cell19_453143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 5].length) (baseStart_453143 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_453143 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_453143 prefixEnd_453143 := by exact prefixLift 453143
  have htrace : WordTrace (prefixWord ++ tailWord_453143) baseStart_453143 baseEnd_453143 := by
    simpa [prefixWord, tailWord_453143, baseEnd_453143] using wordTrace_append hprefix tailTrace_453143
  have hstable : (prefixWord ++ tailWord_453143).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453143).length < 2 ^ (prefixWord ++ tailWord_453143).sum := by decide
  have hdescent : baseEnd_453143 < baseStart_453143 := by decide
  rcases family_descends (prefixWord ++ tailWord_453143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453204 : List Nat := [2, 4, 1, 1, 1, 10]
def baseStart_453204 : Nat := 118140960795 + 453204 * 2 ^ 59
def prefixEnd_453204 : Nat := 4983230072969 + 3 ^ 40 * 453204 * 2
def baseEnd_453204 : Nat := 15322567015002473808445

theorem tailTrace_453204 : CollatzResearch.WordTrace tailWord_453204 prefixEnd_453204 15322567015002473808445 := by
  unfold tailWord_453204
  simp only [CollatzResearch.WordTrace]
  refine ⟨8264853925063391963047333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11019805233417855950729777 8264853925063391963047333)
  ·
    refine ⟨1549660110949385993071375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8264853925063391963047333 1549660110949385993071375)
    ·
      refine ⟨2324490166424078989607063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1549660110949385993071375 2324490166424078989607063)
      ·
        refine ⟨3486735249636118484410595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2324490166424078989607063 3486735249636118484410595)
        ·
          refine ⟨5230102874454177726615893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3486735249636118484410595 5230102874454177726615893)
          ·
            refine ⟨15322567015002473808445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5230102874454177726615893 15322567015002473808445)
            ·
              rfl

theorem cell19_453204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 10].length) (baseStart_453204 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_453204 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_453204 prefixEnd_453204 := by exact prefixLift 453204
  have htrace : WordTrace (prefixWord ++ tailWord_453204) baseStart_453204 baseEnd_453204 := by
    simpa [prefixWord, tailWord_453204, baseEnd_453204] using wordTrace_append hprefix tailTrace_453204
  have hstable : (prefixWord ++ tailWord_453204).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453204).length < 2 ^ (prefixWord ++ tailWord_453204).sum := by decide
  have hdescent : baseEnd_453204 < baseStart_453204 := by decide
  rcases family_descends (prefixWord ++ tailWord_453204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453278 : List Nat := [4, 3, 1, 1, 1, 1, 2, 6]
def baseStart_453278 : Nat := 118140960795 + 453278 * 2 ^ 59
def prefixEnd_453278 : Nat := 4983230072969 + 3 ^ 40 * 453278 * 2
def baseEnd_453278 : Nat := 137925620212612018631359

theorem tailTrace_453278 : CollatzResearch.WordTrace tailWord_453278 prefixEnd_453278 137925620212612018631359 := by
  unfold tailWord_453278
  simp only [CollatzResearch.WordTrace]
  refine ⟨2066550856482336820536061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11021604567905796376192325 2066550856482336820536061)
  ·
    refine ⟨774956571180876307701023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2066550856482336820536061 774956571180876307701023)
    ·
      refine ⟨1162434856771314461551535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 774956571180876307701023 1162434856771314461551535)
      ·
        refine ⟨1743652285156971692327303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1162434856771314461551535 1743652285156971692327303)
        ·
          refine ⟨2615478427735457538490955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1743652285156971692327303 2615478427735457538490955)
          ·
            refine ⟨3923217641603186307736433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2615478427735457538490955 3923217641603186307736433)
            ·
              refine ⟨2942413231202389730802325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3923217641603186307736433 2942413231202389730802325)
              ·
                refine ⟨137925620212612018631359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2942413231202389730802325 137925620212612018631359)
                ·
                  rfl

theorem cell19_453278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_453278 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_453278 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_453278 prefixEnd_453278 := by exact prefixLift 453278
  have htrace : WordTrace (prefixWord ++ tailWord_453278) baseStart_453278 baseEnd_453278 := by
    simpa [prefixWord, tailWord_453278, baseEnd_453278] using wordTrace_append hprefix tailTrace_453278
  have hstable : (prefixWord ++ tailWord_453278).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453278).length < 2 ^ (prefixWord ++ tailWord_453278).sum := by decide
  have hdescent : baseEnd_453278 < baseStart_453278 := by decide
  rcases family_descends (prefixWord ++ tailWord_453278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453299 : List Nat := [1, 1, 1, 2, 3, 5, 1, 5]
def baseStart_453299 : Nat := 118140960795 + 453299 * 2 ^ 59
def prefixEnd_453299 : Nat := 4983230072969 + 3 ^ 40 * 453299 * 2
def baseEnd_453299 : Nat := 137932010194090192164635

theorem tailTrace_453299 : CollatzResearch.WordTrace tailWord_453299 prefixEnd_453299 137932010194090192164635 := by
  unfold tailWord_453299
  simp only [CollatzResearch.WordTrace]
  refine ⟨16533172784782615150802951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11022115189855076767201967 16533172784782615150802951)
  ·
    refine ⟨24799759177173922726204427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16533172784782615150802951 24799759177173922726204427)
    ·
      refine ⟨37199638765760884089306641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24799759177173922726204427 37199638765760884089306641)
      ·
        refine ⟨27899729074320663066979981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37199638765760884089306641 27899729074320663066979981)
        ·
          refine ⟨10462398402870248650117493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27899729074320663066979981 10462398402870248650117493)
          ·
            refine ⟨980849850269085810948515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10462398402870248650117493 980849850269085810948515)
            ·
              refine ⟨1471274775403628716422773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 980849850269085810948515 1471274775403628716422773)
              ·
                refine ⟨137932010194090192164635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1471274775403628716422773 137932010194090192164635)
                ·
                  rfl

theorem cell19_453299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 5].length) (baseStart_453299 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_453299 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_453299 prefixEnd_453299 := by exact prefixLift 453299
  have htrace : WordTrace (prefixWord ++ tailWord_453299) baseStart_453299 baseEnd_453299 := by
    simpa [prefixWord, tailWord_453299, baseEnd_453299] using wordTrace_append hprefix tailTrace_453299
  have hstable : (prefixWord ++ tailWord_453299).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453299).length < 2 ^ (prefixWord ++ tailWord_453299).sum := by decide
  have hdescent : baseEnd_453299 < baseStart_453299 := by decide
  rcases family_descends (prefixWord ++ tailWord_453299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453316 : List Nat := [2, 3, 3, 1, 1, 4, 5]
def baseStart_453316 : Nat := 118140960795 + 453316 * 2 ^ 59
def prefixEnd_453316 : Nat := 4983230072969 + 3 ^ 40 * 453316 * 2
def baseEnd_453316 : Nat := 45979061012079729928937

theorem tailTrace_453316 : CollatzResearch.WordTrace tailWord_453316 prefixEnd_453316 45979061012079729928937 := by
  unfold tailWord_453316
  simp only [CollatzResearch.WordTrace]
  refine ⟨8266896412860513527085901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11022528550480684702781201 8266896412860513527085901)
  ·
    refine ⟨3100086154822692572657213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8266896412860513527085901 3100086154822692572657213)
    ·
      refine ⟨1162532308058509714746455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3100086154822692572657213 1162532308058509714746455)
      ·
        refine ⟨1743798462087764572119683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1162532308058509714746455 1743798462087764572119683)
        ·
          refine ⟨2615697693131646858179525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1743798462087764572119683 2615697693131646858179525)
          ·
            refine ⟨490443317462183785908661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2615697693131646858179525 490443317462183785908661)
            ·
              refine ⟨45979061012079729928937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 490443317462183785908661 45979061012079729928937)
              ·
                rfl

theorem cell19_453316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 5].length) (baseStart_453316 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_453316 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_453316 prefixEnd_453316 := by exact prefixLift 453316
  have htrace : WordTrace (prefixWord ++ tailWord_453316) baseStart_453316 baseEnd_453316 := by
    simpa [prefixWord, tailWord_453316, baseEnd_453316] using wordTrace_append hprefix tailTrace_453316
  have hstable : (prefixWord ++ tailWord_453316).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453316).length < 2 ^ (prefixWord ++ tailWord_453316).sum := by decide
  have hdescent : baseEnd_453316 < baseStart_453316 := by decide
  rcases family_descends (prefixWord ++ tailWord_453316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453333 : List Nat := [1, 3, 2, 5, 1, 1, 2, 4]
def baseStart_453333 : Nat := 118140960795 + 453333 * 2 ^ 59
def prefixEnd_453333 : Nat := 4983230072969 + 3 ^ 40 * 453333 * 2
def baseEnd_453333 : Nat := 137942355878388187408987

theorem tailTrace_453333 : CollatzResearch.WordTrace tailWord_453333 prefixEnd_453333 137942355878388187408987 := by
  unfold tailWord_453333
  simp only [CollatzResearch.WordTrace]
  refine ⟨16534412866659438957540653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11022941911106292638360435 16534412866659438957540653)
  ·
    refine ⟨6200404824997289609077745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16534412866659438957540653 6200404824997289609077745)
    ·
      refine ⟨4650303618747967206808309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6200404824997289609077745 4650303618747967206808309)
      ·
        refine ⟨435965964257621925638279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4650303618747967206808309 435965964257621925638279)
        ·
          refine ⟨653948946386432888457419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 435965964257621925638279 653948946386432888457419)
          ·
            refine ⟨980923419579649332686129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 653948946386432888457419 980923419579649332686129)
            ·
              refine ⟨735692564684736999514597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 980923419579649332686129 735692564684736999514597)
              ·
                refine ⟨137942355878388187408987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 735692564684736999514597 137942355878388187408987)
                ·
                  rfl

theorem cell19_453333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 4].length) (baseStart_453333 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_453333 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_453333 prefixEnd_453333 := by exact prefixLift 453333
  have htrace : WordTrace (prefixWord ++ tailWord_453333) baseStart_453333 baseEnd_453333 := by
    simpa [prefixWord, tailWord_453333, baseEnd_453333] using wordTrace_append hprefix tailTrace_453333
  have hstable : (prefixWord ++ tailWord_453333).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453333).length < 2 ^ (prefixWord ++ tailWord_453333).sum := by decide
  have hdescent : baseEnd_453333 < baseStart_453333 := by decide
  rcases family_descends (prefixWord ++ tailWord_453333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453337 : List Nat := [1, 2, 1, 2, 3, 2, 4, 4]
def baseStart_453337 : Nat := 118140960795 + 453337 * 2 ^ 59
def prefixEnd_453337 : Nat := 4983230072969 + 3 ^ 40 * 453337 * 2
def baseEnd_453337 : Nat := 137943573017717363320087

theorem tailTrace_453337 : CollatzResearch.WordTrace tailWord_453337 prefixEnd_453337 137943573017717363320087 := by
  unfold tailWord_453337
  simp only [CollatzResearch.WordTrace]
  refine ⟨16534558758644947640686265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11023039172429965093790843 16534558758644947640686265)
  ·
    refine ⟨12400919068983710730514699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16534558758644947640686265 12400919068983710730514699)
    ·
      refine ⟨18601378603475566095772049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12400919068983710730514699 18601378603475566095772049)
      ·
        refine ⟨13951033952606674571829037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18601378603475566095772049 13951033952606674571829037)
        ·
          refine ⟨5231637732227502964435889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13951033952606674571829037 5231637732227502964435889)
          ·
            refine ⟨3923728299170627223326917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5231637732227502964435889 3923728299170627223326917)
            ·
              refine ⟨735699056094492604373797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3923728299170627223326917 735699056094492604373797)
              ·
                refine ⟨137943573017717363320087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 735699056094492604373797 137943573017717363320087)
                ·
                  rfl

theorem cell19_453337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 4].length) (baseStart_453337 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_453337 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_453337 prefixEnd_453337 := by exact prefixLift 453337
  have htrace : WordTrace (prefixWord ++ tailWord_453337) baseStart_453337 baseEnd_453337 := by
    simpa [prefixWord, tailWord_453337, baseEnd_453337] using wordTrace_append hprefix tailTrace_453337
  have hstable : (prefixWord ++ tailWord_453337).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453337).length < 2 ^ (prefixWord ++ tailWord_453337).sum := by decide
  have hdescent : baseEnd_453337 < baseStart_453337 := by decide
  rcases family_descends (prefixWord ++ tailWord_453337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453468 : List Nat := [2, 2, 4, 2, 1, 2, 1, 5]
def baseStart_453468 : Nat := 118140960795 + 453468 * 2 ^ 59
def prefixEnd_453468 : Nat := 4983230072969 + 3 ^ 40 * 453468 * 2
def baseEnd_453468 : Nat := 137983434330747874408619

theorem tailTrace_453468 : CollatzResearch.WordTrace tailWord_453468 prefixEnd_453468 137983434330747874408619 := by
  unfold tailWord_453468
  simp only [CollatzResearch.WordTrace]
  refine ⟨8269668360585178506852529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11026224480780238009136705 8269668360585178506852529)
  ·
    refine ⟨6202251270438883880139397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8269668360585178506852529 6202251270438883880139397)
    ·
      refine ⟨1162922113207290727526137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6202251270438883880139397 1162922113207290727526137)
      ·
        refine ⟨872191584905468045644603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1162922113207290727526137 872191584905468045644603)
        ·
          refine ⟨1308287377358202068466905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 872191584905468045644603 1308287377358202068466905)
          ·
            refine ⟨981215533018651551350179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1308287377358202068466905 981215533018651551350179)
            ·
              refine ⟨1471823299527977327025269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 981215533018651551350179 1471823299527977327025269)
              ·
                refine ⟨137983434330747874408619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1471823299527977327025269 137983434330747874408619)
                ·
                  rfl

theorem cell19_453468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 5].length) (baseStart_453468 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_453468 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_453468 prefixEnd_453468 := by exact prefixLift 453468
  have htrace : WordTrace (prefixWord ++ tailWord_453468) baseStart_453468 baseEnd_453468 := by
    simpa [prefixWord, tailWord_453468, baseEnd_453468] using wordTrace_append hprefix tailTrace_453468
  have hstable : (prefixWord ++ tailWord_453468).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453468).length < 2 ^ (prefixWord ++ tailWord_453468).sum := by decide
  have hdescent : baseEnd_453468 < baseStart_453468 := by decide
  rcases family_descends (prefixWord ++ tailWord_453468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453489 : List Nat := [1, 2, 2, 2, 1, 6, 5]
def baseStart_453489 : Nat := 118140960795 + 453489 * 2 ^ 59
def prefixEnd_453489 : Nat := 4983230072969 + 3 ^ 40 * 453489 * 2
def baseEnd_453489 : Nat := 45996608104075349313965

theorem tailTrace_453489 : CollatzResearch.WordTrace tailWord_453489 prefixEnd_453489 45996608104075349313965 := by
  unfold tailWord_453489
  simp only [CollatzResearch.WordTrace]
  refine ⟨16540102654094277600219521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11026735102729518400146347 16540102654094277600219521)
  ·
    refine ⟨12405076990570708200164641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16540102654094277600219521 12405076990570708200164641)
    ·
      refine ⟨9303807742928031150123481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12405076990570708200164641 9303807742928031150123481)
      ·
        refine ⟨6977855807196023362592611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9303807742928031150123481 6977855807196023362592611)
        ·
          refine ⟨10466783710794035043888917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6977855807196023362592611 10466783710794035043888917)
          ·
            refine ⟨490630486443470392682293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 10466783710794035043888917 490630486443470392682293)
            ·
              refine ⟨45996608104075349313965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 490630486443470392682293 45996608104075349313965)
              ·
                rfl

theorem cell19_453489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 5].length) (baseStart_453489 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_453489 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_453489 prefixEnd_453489 := by exact prefixLift 453489
  have htrace : WordTrace (prefixWord ++ tailWord_453489) baseStart_453489 baseEnd_453489 := by
    simpa [prefixWord, tailWord_453489, baseEnd_453489] using wordTrace_append hprefix tailTrace_453489
  have hstable : (prefixWord ++ tailWord_453489).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453489).length < 2 ^ (prefixWord ++ tailWord_453489).sum := by decide
  have hdescent : baseEnd_453489 < baseStart_453489 := by decide
  rcases family_descends (prefixWord ++ tailWord_453489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453491 : List Nat := [1, 1, 1, 2, 2, 1, 11]
def baseStart_453491 : Nat := 118140960795 + 453491 * 2 ^ 59
def prefixEnd_453491 : Nat := 4983230072969 + 3 ^ 40 * 453491 * 2
def baseEnd_453491 : Nat := 45996810960630211965815

theorem tailTrace_453491 : CollatzResearch.WordTrace tailWord_453491 prefixEnd_453491 45996810960630211965815 := by
  unfold tailWord_453491
  simp only [CollatzResearch.WordTrace]
  refine ⟨16540175600087031941792327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11026783733391354627861551 16540175600087031941792327)
  ·
    refine ⟨24810263400130547912688491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16540175600087031941792327 24810263400130547912688491)
    ·
      refine ⟨37215395100195821869032737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24810263400130547912688491 37215395100195821869032737)
      ·
        refine ⟨27911546325146866401774553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37215395100195821869032737 27911546325146866401774553)
        ·
          refine ⟨20933659743860149801330915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27911546325146866401774553 20933659743860149801330915)
          ·
            refine ⟨31400489615790224701996373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20933659743860149801330915 31400489615790224701996373)
            ·
              refine ⟨45996810960630211965815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 31400489615790224701996373 45996810960630211965815)
              ·
                rfl

theorem cell19_453491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 11].length) (baseStart_453491 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_453491 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_453491 prefixEnd_453491 := by exact prefixLift 453491
  have htrace : WordTrace (prefixWord ++ tailWord_453491) baseStart_453491 baseEnd_453491 := by
    simpa [prefixWord, tailWord_453491, baseEnd_453491] using wordTrace_append hprefix tailTrace_453491
  have hstable : (prefixWord ++ tailWord_453491).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453491).length < 2 ^ (prefixWord ++ tailWord_453491).sum := by decide
  have hdescent : baseEnd_453491 < baseStart_453491 := by decide
  rcases family_descends (prefixWord ++ tailWord_453491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453567 : List Nat := [1, 1, 2, 2, 2, 1, 2, 8]
def baseStart_453567 : Nat := 118140960795 + 453567 * 2 ^ 59
def prefixEnd_453567 : Nat := 4983230072969 + 3 ^ 40 * 453567 * 2
def baseEnd_453567 : Nat := 138013558529144978208349

theorem tailTrace_453567 : CollatzResearch.WordTrace tailWord_453567 prefixEnd_453567 138013558529144978208349 := by
  unfold tailWord_453567
  simp only [CollatzResearch.WordTrace]
  refine ⟨16542947547811696921558955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11028631698541131281039303 16542947547811696921558955)
  ·
    refine ⟨24814421321717545382338433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16542947547811696921558955 24814421321717545382338433)
    ·
      refine ⟨18610815991288159036753825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24814421321717545382338433 18610815991288159036753825)
      ·
        refine ⟨13958111993466119277565369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18610815991288159036753825 13958111993466119277565369)
        ·
          refine ⟨10468583995099589458174027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13958111993466119277565369 10468583995099589458174027)
          ·
            refine ⟨15702875992649384187261041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10468583995099589458174027 15702875992649384187261041)
            ·
              refine ⟨11777156994487038140445781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15702875992649384187261041 11777156994487038140445781)
              ·
                refine ⟨138013558529144978208349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11777156994487038140445781 138013558529144978208349)
                ·
                  rfl

theorem cell19_453567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 8].length) (baseStart_453567 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_453567 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_453567 prefixEnd_453567 := by exact prefixLift 453567
  have htrace : WordTrace (prefixWord ++ tailWord_453567) baseStart_453567 baseEnd_453567 := by
    simpa [prefixWord, tailWord_453567, baseEnd_453567] using wordTrace_append hprefix tailTrace_453567
  have hstable : (prefixWord ++ tailWord_453567).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453567).length < 2 ^ (prefixWord ++ tailWord_453567).sum := by decide
  have hdescent : baseEnd_453567 < baseStart_453567 := by decide
  rcases family_descends (prefixWord ++ tailWord_453567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453574 : List Nat := [6, 1, 3, 1, 1, 1, 3, 3]
def baseStart_453574 : Nat := 118140960795 + 453574 * 2 ^ 59
def prefixEnd_453574 : Nat := 4983230072969 + 3 ^ 40 * 453574 * 2
def baseEnd_453574 : Nat := 138015688522971036052775

theorem tailTrace_453574 : CollatzResearch.WordTrace tailWord_453574 prefixEnd_453574 138015688522971036052775 := by
  unfold tailWord_453574
  simp only [CollatzResearch.WordTrace]
  refine ⟨516975089337073034908243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11028801905857558078042517 516975089337073034908243)
  ·
    refine ⟨775462634005609552362365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 516975089337073034908243 775462634005609552362365)
    ·
      refine ⟨290798487752103582135887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 775462634005609552362365 290798487752103582135887)
      ·
        refine ⟨436197731628155373203831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290798487752103582135887 436197731628155373203831)
        ·
          refine ⟨654296597442233059805747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 436197731628155373203831 654296597442233059805747)
          ·
            refine ⟨981444896163349589708621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 654296597442233059805747 981444896163349589708621)
            ·
              refine ⟨368041836061256096140733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 981444896163349589708621 368041836061256096140733)
              ·
                refine ⟨138015688522971036052775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 368041836061256096140733 138015688522971036052775)
                ·
                  rfl

theorem cell19_453574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_453574 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_453574 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_453574 prefixEnd_453574 := by exact prefixLift 453574
  have htrace : WordTrace (prefixWord ++ tailWord_453574) baseStart_453574 baseEnd_453574 := by
    simpa [prefixWord, tailWord_453574, baseEnd_453574] using wordTrace_append hprefix tailTrace_453574
  have hstable : (prefixWord ++ tailWord_453574).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453574).length < 2 ^ (prefixWord ++ tailWord_453574).sum := by decide
  have hdescent : baseEnd_453574 < baseStart_453574 := by decide
  rcases family_descends (prefixWord ++ tailWord_453574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453582 : List Nat := [4, 1, 1, 1, 2, 4, 3, 3]
def baseStart_453582 : Nat := 118140960795 + 453582 * 2 ^ 59
def prefixEnd_453582 : Nat := 4983230072969 + 3 ^ 40 * 453582 * 2
def baseEnd_453582 : Nat := 138018122801629387874975

theorem tailTrace_453582 : CollatzResearch.WordTrace tailWord_453582 prefixEnd_453582 138018122801629387874975 := by
  unfold tailWord_453582
  simp only [CollatzResearch.WordTrace]
  refine ⟨2067936830344669310419375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11028996428504902988903333 2067936830344669310419375)
  ·
    refine ⟨3101905245517003965629063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2067936830344669310419375 3101905245517003965629063)
    ·
      refine ⟨4652857868275505948443595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3101905245517003965629063 4652857868275505948443595)
      ·
        refine ⟨6979286802413258922665393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4652857868275505948443595 6979286802413258922665393)
        ·
          refine ⟨5234465101809944191999045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6979286802413258922665393 5234465101809944191999045)
          ·
            refine ⟨981462206589364535999821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5234465101809944191999045 981462206589364535999821)
            ·
              refine ⟨368048327471011700999933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 981462206589364535999821 368048327471011700999933)
              ·
                refine ⟨138018122801629387874975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 368048327471011700999933 138018122801629387874975)
                ·
                  rfl

theorem cell19_453582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 3, 3].length) (baseStart_453582 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_453582 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_453582 prefixEnd_453582 := by exact prefixLift 453582
  have htrace : WordTrace (prefixWord ++ tailWord_453582) baseStart_453582 baseEnd_453582 := by
    simpa [prefixWord, tailWord_453582, baseEnd_453582] using wordTrace_append hprefix tailTrace_453582
  have hstable : (prefixWord ++ tailWord_453582).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453582).length < 2 ^ (prefixWord ++ tailWord_453582).sum := by decide
  have hdescent : baseEnd_453582 < baseStart_453582 := by decide
  rcases family_descends (prefixWord ++ tailWord_453582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453624 : List Nat := [2, 1, 2, 1, 1, 3, 1, 8]
def baseStart_453624 : Nat := 118140960795 + 453624 * 2 ^ 59
def prefixEnd_453624 : Nat := 4983230072969 + 3 ^ 40 * 453624 * 2
def baseEnd_453624 : Nat := 138030902764585734941527

theorem tailTrace_453624 : CollatzResearch.WordTrace tailWord_453624 prefixEnd_453624 138030902764585734941527 := by
  unfold tailWord_453624
  simp only [CollatzResearch.WordTrace]
  refine ⟨8272513254302597828191963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11030017672403463770922617 8272513254302597828191963)
  ·
    refine ⟨12408769881453896742287945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8272513254302597828191963 12408769881453896742287945)
    ·
      refine ⟨9306577411090422556715959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12408769881453896742287945 9306577411090422556715959)
      ·
        refine ⟨13959866116635633835073939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9306577411090422556715959 13959866116635633835073939)
        ·
          refine ⟨20939799174953450752610909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13959866116635633835073939 20939799174953450752610909)
          ·
            refine ⟨7852424690607544032229091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20939799174953450752610909 7852424690607544032229091)
            ·
              refine ⟨11778637035911316048343637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7852424690607544032229091 11778637035911316048343637)
              ·
                refine ⟨138030902764585734941527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11778637035911316048343637 138030902764585734941527)
                ·
                  rfl

theorem cell19_453624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 8].length) (baseStart_453624 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_453624 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_453624 prefixEnd_453624 := by exact prefixLift 453624
  have htrace : WordTrace (prefixWord ++ tailWord_453624) baseStart_453624 baseEnd_453624 := by
    simpa [prefixWord, tailWord_453624, baseEnd_453624] using wordTrace_append hprefix tailTrace_453624
  have hstable : (prefixWord ++ tailWord_453624).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453624).length < 2 ^ (prefixWord ++ tailWord_453624).sum := by decide
  have hdescent : baseEnd_453624 < baseStart_453624 := by decide
  rcases family_descends (prefixWord ++ tailWord_453624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453753 : List Nat := [1, 2, 1, 3, 5, 1, 3, 3]
def baseStart_453753 : Nat := 118140960795 + 453753 * 2 ^ 59
def prefixEnd_453753 : Nat := 4983230072969 + 3 ^ 40 * 453753 * 2
def baseEnd_453753 : Nat := 138070155507951658074509

theorem tailTrace_453753 : CollatzResearch.WordTrace tailWord_453753 prefixEnd_453753 138070155507951658074509 := by
  unfold tailWord_453753
  simp only [CollatzResearch.WordTrace]
  refine ⟨16549731525137850687829913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11033154350091900458553275 16549731525137850687829913)
  ·
    refine ⟨12412298643853388015872435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16549731525137850687829913 12412298643853388015872435)
    ·
      refine ⟨18618447965780082023808653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12412298643853388015872435 18618447965780082023808653)
      ·
        refine ⟨6981917987167530758928245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18618447965780082023808653 6981917987167530758928245)
        ·
          refine ⟨654554811296956008649523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6981917987167530758928245 654554811296956008649523)
          ·
            refine ⟨981832216945434012974285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 654554811296956008649523 981832216945434012974285)
            ·
              refine ⟨368187081354537754865357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 981832216945434012974285 368187081354537754865357)
              ·
                refine ⟨138070155507951658074509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 368187081354537754865357 138070155507951658074509)
                ·
                  rfl

theorem cell19_453753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 3, 3].length) (baseStart_453753 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_453753 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_453753 prefixEnd_453753 := by exact prefixLift 453753
  have htrace : WordTrace (prefixWord ++ tailWord_453753) baseStart_453753 baseEnd_453753 := by
    simpa [prefixWord, tailWord_453753, baseEnd_453753] using wordTrace_append hprefix tailTrace_453753
  have hstable : (prefixWord ++ tailWord_453753).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453753).length < 2 ^ (prefixWord ++ tailWord_453753).sum := by decide
  have hdescent : baseEnd_453753 < baseStart_453753 := by decide
  rcases family_descends (prefixWord ++ tailWord_453753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453774 : List Nat := [4, 1, 1, 3, 2, 2, 6]
def baseStart_453774 : Nat := 118140960795 + 453774 * 2 ^ 59
def prefixEnd_453774 : Nat := 4983230072969 + 3 ^ 40 * 453774 * 2
def baseEnd_453774 : Nat := 46025515163143277202595

theorem tailTrace_453774 : CollatzResearch.WordTrace tailWord_453774 prefixEnd_453774 46025515163143277202595 := by
  unfold tailWord_453774
  simp only [CollatzResearch.WordTrace]
  refine ⟨2068812182257721409293047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11033664972041180849562917 2068812182257721409293047)
  ·
    refine ⟨3103218273386582113939571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2068812182257721409293047 3103218273386582113939571)
    ·
      refine ⟨4654827410079873170909357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3103218273386582113939571 4654827410079873170909357)
      ·
        refine ⟨1745560278779952439091009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4654827410079873170909357 1745560278779952439091009)
        ·
          refine ⟨1309170209084964329318257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1745560278779952439091009 1309170209084964329318257)
          ·
            refine ⟨981877656813723246988693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1309170209084964329318257 981877656813723246988693)
            ·
              refine ⟨46025515163143277202595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 981877656813723246988693 46025515163143277202595)
              ·
                rfl

theorem cell19_453774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 6].length) (baseStart_453774 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_453774 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_453774 prefixEnd_453774 := by exact prefixLift 453774
  have htrace : WordTrace (prefixWord ++ tailWord_453774) baseStart_453774 baseEnd_453774 := by
    simpa [prefixWord, tailWord_453774, baseEnd_453774] using wordTrace_append hprefix tailTrace_453774
  have hstable : (prefixWord ++ tailWord_453774).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453774).length < 2 ^ (prefixWord ++ tailWord_453774).sum := by decide
  have hdescent : baseEnd_453774 < baseStart_453774 := by decide
  rcases family_descends (prefixWord ++ tailWord_453774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453810 : List Nat := [3, 2, 1, 1, 1, 6, 2, 3]
def baseStart_453810 : Nat := 118140960795 + 453810 * 2 ^ 59
def prefixEnd_453810 : Nat := 4983230072969 + 3 ^ 40 * 453810 * 2
def baseEnd_453810 : Nat := 138087499743392414807687

theorem tailTrace_453810 : CollatzResearch.WordTrace tailWord_453810 prefixEnd_453810 138087499743392414807687 := by
  unfold tailWord_453810
  simp only [CollatzResearch.WordTrace]
  refine ⟨4137952621482837355663721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11034540323954232948436589 4137952621482837355663721)
  ·
    refine ⟨3103464466112128016747791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4137952621482837355663721 3103464466112128016747791)
    ·
      refine ⟨4655196699168192025121687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3103464466112128016747791 4655196699168192025121687)
      ·
        refine ⟨6982795048752288037682531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4655196699168192025121687 6982795048752288037682531)
        ·
          refine ⟨10474192573128432056523797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6982795048752288037682531 10474192573128432056523797)
          ·
            refine ⟨490977776865395252649553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 10474192573128432056523797 490977776865395252649553)
            ·
              refine ⟨368233332649046439487165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 490977776865395252649553 368233332649046439487165)
              ·
                refine ⟨138087499743392414807687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 368233332649046439487165 138087499743392414807687)
                ·
                  rfl

theorem cell19_453810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 2, 3].length) (baseStart_453810 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_453810 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_453810 prefixEnd_453810 := by exact prefixLift 453810
  have htrace : WordTrace (prefixWord ++ tailWord_453810) baseStart_453810 baseEnd_453810 := by
    simpa [prefixWord, tailWord_453810, baseEnd_453810] using wordTrace_append hprefix tailTrace_453810
  have hstable : (prefixWord ++ tailWord_453810).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453810).length < 2 ^ (prefixWord ++ tailWord_453810).sum := by decide
  have hdescent : baseEnd_453810 < baseStart_453810 := by decide
  rcases family_descends (prefixWord ++ tailWord_453810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453846 : List Nat := [5, 2, 1, 2, 2, 1, 2, 4]
def baseStart_453846 : Nat := 118140960795 + 453846 * 2 ^ 59
def prefixEnd_453846 : Nat := 4983230072969 + 3 ^ 40 * 453846 * 2
def baseEnd_453846 : Nat := 138098453997354998007589

theorem tailTrace_453846 : CollatzResearch.WordTrace tailWord_453846 prefixEnd_453846 138098453997354998007589 := by
  unfold tailWord_453846
  simp only [CollatzResearch.WordTrace]
  refine ⟨1034570219612557973185337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11035415675867285047310261 1034570219612557973185337)
  ·
    refine ⟨775927664709418479889003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1034570219612557973185337 775927664709418479889003)
    ·
      refine ⟨1163891497064127719833505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 775927664709418479889003 1163891497064127719833505)
      ·
        refine ⟨872918622798095789875129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1163891497064127719833505 872918622798095789875129)
        ·
          refine ⟨654688967098571842406347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 872918622798095789875129 654688967098571842406347)
          ·
            refine ⟨982033450647857763609521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 654688967098571842406347 982033450647857763609521)
            ·
              refine ⟨736525087985893322707141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 982033450647857763609521 736525087985893322707141)
              ·
                refine ⟨138098453997354998007589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 736525087985893322707141 138098453997354998007589)
                ·
                  rfl

theorem cell19_453846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_453846 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_453846 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_453846 prefixEnd_453846 := by exact prefixLift 453846
  have htrace : WordTrace (prefixWord ++ tailWord_453846) baseStart_453846 baseEnd_453846 := by
    simpa [prefixWord, tailWord_453846, baseEnd_453846] using wordTrace_append hprefix tailTrace_453846
  have hstable : (prefixWord ++ tailWord_453846).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453846).length < 2 ^ (prefixWord ++ tailWord_453846).sum := by decide
  have hdescent : baseEnd_453846 < baseStart_453846 := by decide
  rcases family_descends (prefixWord ++ tailWord_453846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453869 : List Nat := [1, 5, 1, 2, 2, 1, 2, 5]
def baseStart_453869 : Nat := 118140960795 + 453869 * 2 ^ 59
def prefixEnd_453869 : Nat := 4983230072969 + 3 ^ 40 * 453869 * 2
def baseEnd_453869 : Nat := 138105452548497759496415

theorem tailTrace_453869 : CollatzResearch.WordTrace tailWord_453869 prefixEnd_453869 138105452548497759496415 := by
  unfold tailWord_453869
  simp only [CollatzResearch.WordTrace]
  refine ⟨16553962392717602499052661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11035974928478401666035107 16553962392717602499052661)
  ·
    refine ⟨1551933974317275234286187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16553962392717602499052661 1551933974317275234286187)
    ·
      refine ⟨2327900961475912851429281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1551933974317275234286187 2327900961475912851429281)
      ·
        refine ⟨1745925721106934638571961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2327900961475912851429281 1745925721106934638571961)
        ·
          refine ⟨1309444290830200978928971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1745925721106934638571961 1309444290830200978928971)
          ·
            refine ⟨1964166436245301468393457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1309444290830200978928971 1964166436245301468393457)
            ·
              refine ⟨1473124827183976101295093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1964166436245301468393457 1473124827183976101295093)
              ·
                refine ⟨138105452548497759496415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1473124827183976101295093 138105452548497759496415)
                ·
                  rfl

theorem cell19_453869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 5].length) (baseStart_453869 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_453869 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_453869 prefixEnd_453869 := by exact prefixLift 453869
  have htrace : WordTrace (prefixWord ++ tailWord_453869) baseStart_453869 baseEnd_453869 := by
    simpa [prefixWord, tailWord_453869, baseEnd_453869] using wordTrace_append hprefix tailTrace_453869
  have hstable : (prefixWord ++ tailWord_453869).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453869).length < 2 ^ (prefixWord ++ tailWord_453869).sum := by decide
  have hdescent : baseEnd_453869 < baseStart_453869 := by decide
  rcases family_descends (prefixWord ++ tailWord_453869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453945 : List Nat := [1, 2, 1, 6, 2, 1, 6]
def baseStart_453945 : Nat := 118140960795 + 453945 * 2 ^ 59
def prefixEnd_453945 : Nat := 4983230072969 + 3 ^ 40 * 453945 * 2
def baseEnd_453945 : Nat := 46042859398584033935773

theorem tailTrace_453945 : CollatzResearch.WordTrace tailWord_453945 prefixEnd_453945 46042859398584033935773 := by
  unfold tailWord_453945
  simp only [CollatzResearch.WordTrace]
  refine ⟨16556734340442267478819289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11037822893628178319212859 16556734340442267478819289)
  ·
    refine ⟨12417550755331700609114467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16556734340442267478819289 12417550755331700609114467)
    ·
      refine ⟨18626326132997550913671701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12417550755331700609114467 18626326132997550913671701)
      ·
        refine ⟨873109037484260199078361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 18626326132997550913671701 873109037484260199078361)
        ·
          refine ⟨654831778113195149308771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 873109037484260199078361 654831778113195149308771)
          ·
            refine ⟨982247667169792723963157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 654831778113195149308771 982247667169792723963157)
            ·
              refine ⟨46042859398584033935773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 982247667169792723963157 46042859398584033935773)
              ·
                rfl

theorem cell19_453945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 6].length) (baseStart_453945 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_453945 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_453945 prefixEnd_453945 := by exact prefixLift 453945
  have htrace : WordTrace (prefixWord ++ tailWord_453945) baseStart_453945 baseEnd_453945 := by
    simpa [prefixWord, tailWord_453945, baseEnd_453945] using wordTrace_append hprefix tailTrace_453945
  have hstable : (prefixWord ++ tailWord_453945).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453945).length < 2 ^ (prefixWord ++ tailWord_453945).sum := by decide
  have hdescent : baseEnd_453945 < baseStart_453945 := by decide
  rcases family_descends (prefixWord ++ tailWord_453945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453966 : List Nat := [4, 1, 1, 1, 1, 1, 4, 6]
def baseStart_453966 : Nat := 118140960795 + 453966 * 2 ^ 59
def prefixEnd_453966 : Nat := 4983230072969 + 3 ^ 40 * 453966 * 2
def baseEnd_453966 : Nat := 138134968177230275340595

theorem tailTrace_453966 : CollatzResearch.WordTrace tailWord_453966 prefixEnd_453966 138134968177230275340595 := by
  unfold tailWord_453966
  simp only [CollatzResearch.WordTrace]
  refine ⟨2069687534170773508166719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11038333515577458710222501 2069687534170773508166719)
  ·
    refine ⟨3104531301256160262250079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2069687534170773508166719 3104531301256160262250079)
    ·
      refine ⟨4656796951884240393375119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3104531301256160262250079 4656796951884240393375119)
      ·
        refine ⟨6985195427826360590062679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4656796951884240393375119 6985195427826360590062679)
        ·
          refine ⟨10477793141739540885094019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6985195427826360590062679 10477793141739540885094019)
          ·
            refine ⟨15716689712609311327641029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10477793141739540885094019 15716689712609311327641029)
            ·
              refine ⟨2946879321114245873932693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15716689712609311327641029 2946879321114245873932693)
              ·
                refine ⟨138134968177230275340595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2946879321114245873932693 138134968177230275340595)
                ·
                  rfl

theorem cell19_453966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_453966 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_453966 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_453966 prefixEnd_453966 := by exact prefixLift 453966
  have htrace : WordTrace (prefixWord ++ tailWord_453966) baseStart_453966 baseEnd_453966 := by
    simpa [prefixWord, tailWord_453966, baseEnd_453966] using wordTrace_append hprefix tailTrace_453966
  have hstable : (prefixWord ++ tailWord_453966).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453966).length < 2 ^ (prefixWord ++ tailWord_453966).sum := by decide
  have hdescent : baseEnd_453966 < baseStart_453966 := by decide
  rcases family_descends (prefixWord ++ tailWord_453966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_453998 : List Nat := [4, 1, 2, 4, 2, 1, 5]
def baseStart_453998 : Nat := 118140960795 + 453998 * 2 ^ 59
def prefixEnd_453998 : Nat := 4983230072969 + 3 ^ 40 * 453998 * 2
def baseEnd_453998 : Nat := 46048235097287894209799

theorem tailTrace_453998 : CollatzResearch.WordTrace tailWord_453998 prefixEnd_453998 46048235097287894209799 := by
  unfold tailWord_453998
  simp only [CollatzResearch.WordTrace]
  refine ⟨2069833426156282191312331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11039111606166838353665765 2069833426156282191312331)
  ·
    refine ⟨3104750139234423286968497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2069833426156282191312331 3104750139234423286968497)
    ·
      refine ⟨2328562604425817465226373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3104750139234423286968497 2328562604425817465226373)
      ·
        refine ⟨436605488329840774729945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2328562604425817465226373 436605488329840774729945)
        ·
          refine ⟨327454116247380581047459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 436605488329840774729945 327454116247380581047459)
          ·
            refine ⟨491181174371070871571189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327454116247380581047459 491181174371070871571189)
            ·
              refine ⟨46048235097287894209799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 491181174371070871571189 46048235097287894209799)
              ·
                rfl

theorem cell19_453998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 5].length) (baseStart_453998 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_453998 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_453998 prefixEnd_453998 := by exact prefixLift 453998
  have htrace : WordTrace (prefixWord ++ tailWord_453998) baseStart_453998 baseEnd_453998 := by
    simpa [prefixWord, tailWord_453998, baseEnd_453998] using wordTrace_append hprefix tailTrace_453998
  have hstable : (prefixWord ++ tailWord_453998).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_453998).length < 2 ^ (prefixWord ++ tailWord_453998).sum := by decide
  have hdescent : baseEnd_453998 < baseStart_453998 := by decide
  rcases family_descends (prefixWord ++ tailWord_453998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454023 : List Nat := [1, 1, 4, 2, 2, 2, 1, 6]
def baseStart_454023 : Nat := 118140960795 + 454023 * 2 ^ 59
def prefixEnd_454023 : Nat := 4983230072969 + 3 ^ 40 * 454023 * 2
def baseEnd_454023 : Nat := 138152312412671032073773

theorem tailTrace_454023 : CollatzResearch.WordTrace tailWord_454023 prefixEnd_454023 138152312412671032073773 := by
  unfold tailWord_454023
  simp only [CollatzResearch.WordTrace]
  refine ⟨16559579234159686800158723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11039719489439791200105815 16559579234159686800158723)
  ·
    refine ⟨24839368851239530200238085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16559579234159686800158723 24839368851239530200238085)
    ·
      refine ⟨4657381659607411912544641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24839368851239530200238085 4657381659607411912544641)
      ·
        refine ⟨3493036244705558934408481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4657381659607411912544641 3493036244705558934408481)
        ·
          refine ⟨2619777183529169200806361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3493036244705558934408481 2619777183529169200806361)
          ·
            refine ⟨1964832887646876900604771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2619777183529169200806361 1964832887646876900604771)
            ·
              refine ⟨2947249331470315350907157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1964832887646876900604771 2947249331470315350907157)
              ·
                refine ⟨138152312412671032073773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2947249331470315350907157 138152312412671032073773)
                ·
                  rfl

theorem cell19_454023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 6].length) (baseStart_454023 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_454023 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_454023 prefixEnd_454023 := by exact prefixLift 454023
  have htrace : WordTrace (prefixWord ++ tailWord_454023) baseStart_454023 baseEnd_454023 := by
    simpa [prefixWord, tailWord_454023, baseEnd_454023] using wordTrace_append hprefix tailTrace_454023
  have hstable : (prefixWord ++ tailWord_454023).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454023).length < 2 ^ (prefixWord ++ tailWord_454023).sum := by decide
  have hdescent : baseEnd_454023 < baseStart_454023 := by decide
  rcases family_descends (prefixWord ++ tailWord_454023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454042 : List Nat := [3, 1, 1, 4, 1, 1, 1, 7]
def baseStart_454042 : Nat := 118140960795 + 454042 * 2 ^ 59
def prefixEnd_454042 : Nat := 4983230072969 + 3 ^ 40 * 454042 * 2
def baseEnd_454042 : Nat := 138158093824484617651499

theorem tailTrace_454042 : CollatzResearch.WordTrace tailWord_454042 prefixEnd_454042 138158093824484617651499 := by
  unfold tailWord_454042
  simp only [CollatzResearch.WordTrace]
  refine ⟨4140068055272713261275095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11040181480727235363400253 4140068055272713261275095)
  ·
    refine ⟨6210102082909069891912643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4140068055272713261275095 6210102082909069891912643)
    ·
      refine ⟨9315153124363604837868965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6210102082909069891912643 9315153124363604837868965)
      ·
        refine ⟨1746591210818175907100431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9315153124363604837868965 1746591210818175907100431)
        ·
          refine ⟨2619886816227263860650647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1746591210818175907100431 2619886816227263860650647)
          ·
            refine ⟨3929830224340895790975971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2619886816227263860650647 3929830224340895790975971)
            ·
              refine ⟨5894745336511343686463957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3929830224340895790975971 5894745336511343686463957)
              ·
                refine ⟨138158093824484617651499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5894745336511343686463957 138158093824484617651499)
                ·
                  rfl

theorem cell19_454042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 7].length) (baseStart_454042 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_454042 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_454042 prefixEnd_454042 := by exact prefixLift 454042
  have htrace : WordTrace (prefixWord ++ tailWord_454042) baseStart_454042 baseEnd_454042 := by
    simpa [prefixWord, tailWord_454042, baseEnd_454042] using wordTrace_append hprefix tailTrace_454042
  have hstable : (prefixWord ++ tailWord_454042).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454042).length < 2 ^ (prefixWord ++ tailWord_454042).sum := by decide
  have hdescent : baseEnd_454042 < baseStart_454042 := by decide
  rcases family_descends (prefixWord ++ tailWord_454042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454076 : List Nat := [2, 2, 2, 4, 2, 2, 1, 4]
def baseStart_454076 : Nat := 118140960795 + 454076 * 2 ^ 59
def prefixEnd_454076 : Nat := 4983230072969 + 3 ^ 40 * 454076 * 2
def baseEnd_454076 : Nat := 138168439508782612895851

theorem tailTrace_454076 : CollatzResearch.WordTrace tailWord_454076 prefixEnd_454076 138168439508782612895851 := by
  unfold tailWord_454076
  simp only [CollatzResearch.WordTrace]
  refine ⟨8280756151483838425919041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11041008201978451234558721 8280756151483838425919041)
  ·
    refine ⟨6210567113612878819439281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8280756151483838425919041 6210567113612878819439281)
    ·
      refine ⟨4657925335209659114579461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6210567113612878819439281 4657925335209659114579461)
      ·
        refine ⟨873361000351811083983649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4657925335209659114579461 873361000351811083983649)
        ·
          refine ⟨655020750263858312987737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 873361000351811083983649 655020750263858312987737)
          ·
            refine ⟨491265562697893734740803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 655020750263858312987737 491265562697893734740803)
            ·
              refine ⟨736898344046840602111205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 491265562697893734740803 736898344046840602111205)
              ·
                refine ⟨138168439508782612895851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 736898344046840602111205 138168439508782612895851)
                ·
                  rfl

theorem cell19_454076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 4].length) (baseStart_454076 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_454076 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_454076 prefixEnd_454076 := by exact prefixLift 454076
  have htrace : WordTrace (prefixWord ++ tailWord_454076) baseStart_454076 baseEnd_454076 := by
    simpa [prefixWord, tailWord_454076, baseEnd_454076] using wordTrace_append hprefix tailTrace_454076
  have hstable : (prefixWord ++ tailWord_454076).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454076).length < 2 ^ (prefixWord ++ tailWord_454076).sum := by decide
  have hdescent : baseEnd_454076 < baseStart_454076 := by decide
  rcases family_descends (prefixWord ++ tailWord_454076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454080 : List Nat := [2, 1, 1, 2, 3, 1, 5, 4]
def baseStart_454080 : Nat := 118140960795 + 454080 * 2 ^ 59
def prefixEnd_454080 : Nat := 4983230072969 + 3 ^ 40 * 454080 * 2
def baseEnd_454080 : Nat := 138169656648111788806951

theorem tailTrace_454080 : CollatzResearch.WordTrace tailWord_454080 prefixEnd_454080 138169656648111788806951 := by
  unfold tailWord_454080
  simp only [CollatzResearch.WordTrace]
  refine ⟨8280829097476592767491847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11041105463302123689989129 8280829097476592767491847)
  ·
    refine ⟨12421243646214889151237771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8280829097476592767491847 12421243646214889151237771)
    ·
      refine ⟨18631865469322333726856657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12421243646214889151237771 18631865469322333726856657)
      ·
        refine ⟨13973899101991750295142493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18631865469322333726856657 13973899101991750295142493)
        ·
          refine ⟨5240212163246906360678435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13973899101991750295142493 5240212163246906360678435)
          ·
            refine ⟨7860318244870359541017653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5240212163246906360678435 7860318244870359541017653)
            ·
              refine ⟨736904835456596206970405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7860318244870359541017653 736904835456596206970405)
              ·
                refine ⟨138169656648111788806951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 736904835456596206970405 138169656648111788806951)
                ·
                  rfl

theorem cell19_454080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 4].length) (baseStart_454080 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_454080 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_454080 prefixEnd_454080 := by exact prefixLift 454080
  have htrace : WordTrace (prefixWord ++ tailWord_454080) baseStart_454080 baseEnd_454080 := by
    simpa [prefixWord, tailWord_454080, baseEnd_454080] using wordTrace_append hprefix tailTrace_454080
  have hstable : (prefixWord ++ tailWord_454080).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454080).length < 2 ^ (prefixWord ++ tailWord_454080).sum := by decide
  have hdescent : baseEnd_454080 < baseStart_454080 := by decide
  rcases family_descends (prefixWord ++ tailWord_454080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454154 : List Nat := [3, 1, 2, 2, 2, 2, 4, 3]
def baseStart_454154 : Nat := 118140960795 + 454154 * 2 ^ 59
def prefixEnd_454154 : Nat := 4983230072969 + 3 ^ 40 * 454154 * 2
def baseEnd_454154 : Nat := 138192173725701543162305

theorem tailTrace_454154 : CollatzResearch.WordTrace tailWord_454154 prefixEnd_454154 138192173725701543162305 := by
  unfold tailWord_454154
  simp only [CollatzResearch.WordTrace]
  refine ⟨4141089299171274043294379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11042904797790064115451677 4141089299171274043294379)
  ·
    refine ⟨6211633948756911064941569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4141089299171274043294379 6211633948756911064941569)
    ·
      refine ⟨4658725461567683298706177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6211633948756911064941569 4658725461567683298706177)
      ·
        refine ⟨3494044096175762474029633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4658725461567683298706177 3494044096175762474029633)
        ·
          refine ⟨2620533072131821855522225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3494044096175762474029633 2620533072131821855522225)
          ·
            refine ⟨1965399804098866391641669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2620533072131821855522225 1965399804098866391641669)
            ·
              refine ⟨368512463268537448432813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1965399804098866391641669 368512463268537448432813)
              ·
                refine ⟨138192173725701543162305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 368512463268537448432813 138192173725701543162305)
                ·
                  rfl

theorem cell19_454154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 4, 3].length) (baseStart_454154 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_454154 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_454154 prefixEnd_454154 := by exact prefixLift 454154
  have htrace : WordTrace (prefixWord ++ tailWord_454154) baseStart_454154 baseEnd_454154 := by
    simpa [prefixWord, tailWord_454154, baseEnd_454154] using wordTrace_append hprefix tailTrace_454154
  have hstable : (prefixWord ++ tailWord_454154).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454154).length < 2 ^ (prefixWord ++ tailWord_454154).sum := by decide
  have hdescent : baseEnd_454154 < baseStart_454154 := by decide
  rcases family_descends (prefixWord ++ tailWord_454154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454325 : List Nat := [1, 3, 3, 3, 2, 1, 1, 5]
def baseStart_454325 : Nat := 118140960795 + 454325 * 2 ^ 59
def prefixEnd_454325 : Nat := 4983230072969 + 3 ^ 40 * 454325 * 2
def baseEnd_454325 : Nat := 138244206432023813361839

theorem tailTrace_454325 : CollatzResearch.WordTrace tailWord_454325 prefixEnd_454325 138244206432023813361839 := by
  unfold tailWord_454325
  simp only [CollatzResearch.WordTrace]
  refine ⟨16570594079065592377652429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11047062719377061585101619 16570594079065592377652429)
  ·
    refine ⟨6213972779649597141619661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16570594079065592377652429 6213972779649597141619661)
    ·
      refine ⟨2330239792368598928107373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6213972779649597141619661 2330239792368598928107373)
      ·
        refine ⟨873839922138224598040265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2330239792368598928107373 873839922138224598040265)
        ·
          refine ⟨655379941603668448530199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 873839922138224598040265 655379941603668448530199)
          ·
            refine ⟨983069912405502672795299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 655379941603668448530199 983069912405502672795299)
            ·
              refine ⟨1474604868608254009192949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 983069912405502672795299 1474604868608254009192949)
              ·
                refine ⟨138244206432023813361839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1474604868608254009192949 138244206432023813361839)
                ·
                  rfl

theorem cell19_454325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 5].length) (baseStart_454325 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_454325 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_454325 prefixEnd_454325 := by exact prefixLift 454325
  have htrace : WordTrace (prefixWord ++ tailWord_454325) baseStart_454325 baseEnd_454325 := by
    simpa [prefixWord, tailWord_454325, baseEnd_454325] using wordTrace_append hprefix tailTrace_454325
  have hstable : (prefixWord ++ tailWord_454325).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454325).length < 2 ^ (prefixWord ++ tailWord_454325).sum := by decide
  have hdescent : baseEnd_454325 < baseStart_454325 := by decide
  rcases family_descends (prefixWord ++ tailWord_454325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454327 : List Nat := [1, 1, 3, 1, 5, 2, 1, 5]
def baseStart_454327 : Nat := 118140960795 + 454327 * 2 ^ 59
def prefixEnd_454327 : Nat := 4983230072969 + 3 ^ 40 * 454327 * 2
def baseEnd_454327 : Nat := 138244815001688401317389

theorem tailTrace_454327 : CollatzResearch.WordTrace tailWord_454327 prefixEnd_454327 138244815001688401317389 := by
  unfold tailWord_454327
  simp only [CollatzResearch.WordTrace]
  refine ⟨16570667025058346719225235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11047111350038897812816823 16570667025058346719225235)
  ·
    refine ⟨24856000537587520078837853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16570667025058346719225235 24856000537587520078837853)
    ·
      refine ⟨9321000201595320029564195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24856000537587520078837853 9321000201595320029564195)
      ·
        refine ⟨13981500302392980044346293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9321000201595320029564195 13981500302392980044346293)
        ·
          refine ⟨1310765653349341879157465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13981500302392980044346293 1310765653349341879157465)
          ·
            refine ⟨983074240012006409368099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1310765653349341879157465 983074240012006409368099)
            ·
              refine ⟨1474611360018009614052149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 983074240012006409368099 1474611360018009614052149)
              ·
                refine ⟨138244815001688401317389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1474611360018009614052149 138244815001688401317389)
                ·
                  rfl

theorem cell19_454327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 5].length) (baseStart_454327 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_454327 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_454327 prefixEnd_454327 := by exact prefixLift 454327
  have htrace : WordTrace (prefixWord ++ tailWord_454327) baseStart_454327 baseEnd_454327 := by
    simpa [prefixWord, tailWord_454327, baseEnd_454327] using wordTrace_append hprefix tailTrace_454327
  have hstable : (prefixWord ++ tailWord_454327).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454327).length < 2 ^ (prefixWord ++ tailWord_454327).sum := by decide
  have hdescent : baseEnd_454327 < baseStart_454327 := by decide
  rcases family_descends (prefixWord ++ tailWord_454327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454338 : List Nat := [3, 5, 1, 2, 2, 1, 5]
def baseStart_454338 : Nat := 118140960795 + 454338 * 2 ^ 59
def prefixEnd_454338 : Nat := 4983230072969 + 3 ^ 40 * 454338 * 2
def baseEnd_454338 : Nat := 46082720711614545024305

theorem tailTrace_454338 : CollatzResearch.WordTrace tailWord_454338 prefixEnd_454338 46082720711614545024305 := by
  unfold tailWord_454338
  simp only [CollatzResearch.WordTrace]
  refine ⟨4142767057004623899468917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11047378818678997065250445 4142767057004623899468917)
  ·
    refine ⟨388384411594183490575211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4142767057004623899468917 388384411594183490575211)
    ·
      refine ⟨582576617391275235862817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388384411594183490575211 582576617391275235862817)
      ·
        refine ⟨436932463043456426897113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 582576617391275235862817 436932463043456426897113)
        ·
          refine ⟨327699347282592320172835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 436932463043456426897113 327699347282592320172835)
          ·
            refine ⟨491549020923888480259253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327699347282592320172835 491549020923888480259253)
            ·
              refine ⟨46082720711614545024305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 491549020923888480259253 46082720711614545024305)
              ·
                rfl

theorem cell19_454338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 5].length) (baseStart_454338 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_454338 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_454338 prefixEnd_454338 := by exact prefixLift 454338
  have htrace : WordTrace (prefixWord ++ tailWord_454338) baseStart_454338 baseEnd_454338 := by
    simpa [prefixWord, tailWord_454338, baseEnd_454338] using wordTrace_append hprefix tailTrace_454338
  have hstable : (prefixWord ++ tailWord_454338).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454338).length < 2 ^ (prefixWord ++ tailWord_454338).sum := by decide
  have hdescent : baseEnd_454338 < baseStart_454338 := by decide
  rcases family_descends (prefixWord ++ tailWord_454338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454342 : List Nat := [6, 1, 2, 1, 1, 1, 7]
def baseStart_454342 : Nat := 118140960795 + 454342 * 2 ^ 59
def prefixEnd_454342 : Nat := 4983230072969 + 3 ^ 40 * 454342 * 2
def baseEnd_454342 : Nat := 46083126424724270328005

theorem tailTrace_454342 : CollatzResearch.WordTrace tailWord_454342 prefixEnd_454342 46083126424724270328005 := by
  unfold tailWord_454342
  simp only [CollatzResearch.WordTrace]
  refine ⟨517850441250125133781915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11047476080002669520680853 517850441250125133781915)
  ·
    refine ⟨776775661875187700672873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 517850441250125133781915 776775661875187700672873)
    ·
      refine ⟨582581746406390775504655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 776775661875187700672873 582581746406390775504655)
      ·
        refine ⟨873872619609586163256983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 582581746406390775504655 873872619609586163256983)
        ·
          refine ⟨1310808929414379244885475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 873872619609586163256983 1310808929414379244885475)
          ·
            refine ⟨1966213394121568867328213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1310808929414379244885475 1966213394121568867328213)
            ·
              refine ⟨46083126424724270328005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1966213394121568867328213 46083126424724270328005)
              ·
                rfl

theorem cell19_454342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 7].length) (baseStart_454342 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_454342 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_454342 prefixEnd_454342 := by exact prefixLift 454342
  have htrace : WordTrace (prefixWord ++ tailWord_454342) baseStart_454342 baseEnd_454342 := by
    simpa [prefixWord, tailWord_454342, baseEnd_454342] using wordTrace_append hprefix tailTrace_454342
  have hstable : (prefixWord ++ tailWord_454342).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454342).length < 2 ^ (prefixWord ++ tailWord_454342).sum := by decide
  have hdescent : baseEnd_454342 < baseStart_454342 := by decide
  rcases family_descends (prefixWord ++ tailWord_454342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454418 : List Nat := [3, 2, 4, 1, 1, 3, 1, 4]
def baseStart_454418 : Nat := 118140960795 + 454418 * 2 ^ 59
def prefixEnd_454418 : Nat := 4983230072969 + 3 ^ 40 * 454418 * 2
def baseEnd_454418 : Nat := 138272504921427153294919

theorem tailTrace_454418 : CollatzResearch.WordTrace tailWord_454418 prefixEnd_454418 138272504921427153294919 := by
  unfold tailWord_454418
  simp only [CollatzResearch.WordTrace]
  refine ⟨4143496516932167315196977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11049324045152446173858605 4143496516932167315196977)
  ·
    refine ⟨3107622387699125486397733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4143496516932167315196977 3107622387699125486397733)
    ·
      refine ⟨582679197693586028699575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3107622387699125486397733 582679197693586028699575)
      ·
        refine ⟨874018796540379043049363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 582679197693586028699575 874018796540379043049363)
        ·
          refine ⟨1311028194810568564574045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 874018796540379043049363 1311028194810568564574045)
          ·
            refine ⟨491635573053963211715267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1311028194810568564574045 491635573053963211715267)
            ·
              refine ⟨737453359580944817572901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 491635573053963211715267 737453359580944817572901)
              ·
                refine ⟨138272504921427153294919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 737453359580944817572901 138272504921427153294919)
                ·
                  rfl

theorem cell19_454418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 4].length) (baseStart_454418 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_454418 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_454418 prefixEnd_454418 := by exact prefixLift 454418
  have htrace : WordTrace (prefixWord ++ tailWord_454418) baseStart_454418 baseEnd_454418 := by
    simpa [prefixWord, tailWord_454418, baseEnd_454418] using wordTrace_append hprefix tailTrace_454418
  have hstable : (prefixWord ++ tailWord_454418).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454418).length < 2 ^ (prefixWord ++ tailWord_454418).sum := by decide
  have hdescent : baseEnd_454418 < baseStart_454418 := by decide
  rcases family_descends (prefixWord ++ tailWord_454418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454492 : List Nat := [2, 2, 4, 2, 3, 1, 2, 3]
def baseStart_454492 : Nat := 118140960795 + 454492 * 2 ^ 59
def prefixEnd_454492 : Nat := 4983230072969 + 3 ^ 40 * 454492 * 2
def baseEnd_454492 : Nat := 138295021999016907650273

theorem tailTrace_454492 : CollatzResearch.WordTrace tailWord_454492 prefixEnd_454492 138295021999016907650273 := by
  unfold tailWord_454492
  simp only [CollatzResearch.WordTrace]
  refine ⟨8288342534730289949490865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11051123379640386599321153 8288342534730289949490865)
  ·
    refine ⟨6216256901047717462118149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8288342534730289949490865 6216256901047717462118149)
    ·
      refine ⟨1165548168946447024147153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6216256901047717462118149 1165548168946447024147153)
      ·
        refine ⟨874161126709835268110365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1165548168946447024147153 874161126709835268110365)
        ·
          refine ⟨327810422516188225541387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 874161126709835268110365 327810422516188225541387)
          ·
            refine ⟨491715633774282338312081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327810422516188225541387 491715633774282338312081)
            ·
              refine ⟨368786725330711753734061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 491715633774282338312081 368786725330711753734061)
              ·
                refine ⟨138295021999016907650273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 368786725330711753734061 138295021999016907650273)
                ·
                  rfl

theorem cell19_454492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 2, 3].length) (baseStart_454492 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_454492 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_454492 prefixEnd_454492 := by exact prefixLift 454492
  have htrace : WordTrace (prefixWord ++ tailWord_454492) baseStart_454492 baseEnd_454492 := by
    simpa [prefixWord, tailWord_454492, baseEnd_454492] using wordTrace_append hprefix tailTrace_454492
  have hstable : (prefixWord ++ tailWord_454492).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454492).length < 2 ^ (prefixWord ++ tailWord_454492).sum := by decide
  have hdescent : baseEnd_454492 < baseStart_454492 := by decide
  rcases family_descends (prefixWord ++ tailWord_454492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454496 : List Nat := [2, 1, 1, 3, 3, 4, 2, 3]
def baseStart_454496 : Nat := 118140960795 + 454496 * 2 ^ 59
def prefixEnd_454496 : Nat := 4983230072969 + 3 ^ 40 * 454496 * 2
def baseEnd_454496 : Nat := 138296239138346083561373

theorem tailTrace_454496 : CollatzResearch.WordTrace tailWord_454496 prefixEnd_454496 138296239138346083561373 := by
  unfold tailWord_454496
  simp only [CollatzResearch.WordTrace]
  refine ⟨8288415480723044291063671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11051220640964059054751561 8288415480723044291063671)
  ·
    refine ⟨12432623221084566436595507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8288415480723044291063671 12432623221084566436595507)
    ·
      refine ⟨18648934831626849654893261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12432623221084566436595507 18648934831626849654893261)
      ·
        refine ⟨6993350561860068620584973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18648934831626849654893261 6993350561860068620584973)
        ·
          refine ⟨2622506460697525732719365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6993350561860068620584973 2622506460697525732719365)
          ·
            refine ⟨491719961380786074884881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2622506460697525732719365 491719961380786074884881)
            ·
              refine ⟨368789971035589556163661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 491719961380786074884881 368789971035589556163661)
              ·
                refine ⟨138296239138346083561373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 368789971035589556163661 138296239138346083561373)
                ·
                  rfl

theorem cell19_454496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 2, 3].length) (baseStart_454496 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_454496 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_454496 prefixEnd_454496 := by exact prefixLift 454496
  have htrace : WordTrace (prefixWord ++ tailWord_454496) baseStart_454496 baseEnd_454496 := by
    simpa [prefixWord, tailWord_454496, baseEnd_454496] using wordTrace_append hprefix tailTrace_454496
  have hstable : (prefixWord ++ tailWord_454496).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454496).length < 2 ^ (prefixWord ++ tailWord_454496).sum := by decide
  have hdescent : baseEnd_454496 < baseStart_454496 := by decide
  rcases family_descends (prefixWord ++ tailWord_454496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454631 : List Nat := [1, 1, 5, 2, 3, 1, 6]
def baseStart_454631 : Nat := 118140960795 + 454631 * 2 ^ 59
def prefixEnd_454631 : Nat := 4983230072969 + 3 ^ 40 * 454631 * 2
def baseEnd_454631 : Nat := 46112439196901923520335

theorem tailTrace_454631 : CollatzResearch.WordTrace tailWord_454631 prefixEnd_454631 46112439196901923520335 := by
  unfold tailWord_454631
  simp only [CollatzResearch.WordTrace]
  refine ⟨16581754815957006638291747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11054503210638004425527831 16581754815957006638291747)
  ·
    refine ⟨24872632223935509957437621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16581754815957006638291747 24872632223935509957437621)
    ·
      refine ⟨2331809270993954058509777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24872632223935509957437621 2331809270993954058509777)
      ·
        refine ⟨1748856953245465543882333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2331809270993954058509777 1748856953245465543882333)
        ·
          refine ⟨655821357467049578955875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1748856953245465543882333 655821357467049578955875)
          ·
            refine ⟨983732036200574368433813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 655821357467049578955875 983732036200574368433813)
            ·
              refine ⟨46112439196901923520335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 983732036200574368433813 46112439196901923520335)
              ·
                rfl

theorem cell19_454631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 6].length) (baseStart_454631 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_454631 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_454631 prefixEnd_454631 := by exact prefixLift 454631
  have htrace : WordTrace (prefixWord ++ tailWord_454631) baseStart_454631 baseEnd_454631 := by
    simpa [prefixWord, tailWord_454631, baseEnd_454631] using wordTrace_append hprefix tailTrace_454631
  have hstable : (prefixWord ++ tailWord_454631).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454631).length < 2 ^ (prefixWord ++ tailWord_454631).sum := by decide
  have hdescent : baseEnd_454631 < baseStart_454631 := by decide
  rcases family_descends (prefixWord ++ tailWord_454631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454652 : List Nat := [2, 2, 2, 1, 2, 2, 2, 6]
def baseStart_454652 : Nat := 118140960795 + 454652 * 2 ^ 59
def prefixEnd_454652 : Nat := 4983230072969 + 3 ^ 40 * 454652 * 2
def baseEnd_454652 : Nat := 138343707572183944094281

theorem tailTrace_454652 : CollatzResearch.WordTrace tailWord_454652 prefixEnd_454652 138343707572183944094281 := by
  unfold tailWord_454652
  simp only [CollatzResearch.WordTrace]
  refine ⟨8291260374440463612403105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11055013832587284816537473 8291260374440463612403105)
  ·
    refine ⟨6218445280830347709302329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8291260374440463612403105 6218445280830347709302329)
    ·
      refine ⟨4663833960622760781976747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6218445280830347709302329 4663833960622760781976747)
      ·
        refine ⟨6995750940934141172965121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4663833960622760781976747 6995750940934141172965121)
        ·
          refine ⟨5246813205700605879723841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6995750940934141172965121 5246813205700605879723841)
          ·
            refine ⟨3935109904275454409792881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5246813205700605879723841 3935109904275454409792881)
            ·
              refine ⟨2951332428206590807344661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3935109904275454409792881 2951332428206590807344661)
              ·
                refine ⟨138343707572183944094281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2951332428206590807344661 138343707572183944094281)
                ·
                  rfl

theorem cell19_454652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 6].length) (baseStart_454652 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_454652 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_454652 prefixEnd_454652 := by exact prefixLift 454652
  have htrace : WordTrace (prefixWord ++ tailWord_454652) baseStart_454652 baseEnd_454652 := by
    simpa [prefixWord, tailWord_454652, baseEnd_454652] using wordTrace_append hprefix tailTrace_454652
  have hstable : (prefixWord ++ tailWord_454652).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454652).length < 2 ^ (prefixWord ++ tailWord_454652).sum := by decide
  have hdescent : baseEnd_454652 < baseStart_454652 := by decide
  rcases family_descends (prefixWord ++ tailWord_454652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454709 : List Nat := [1, 3, 3, 1, 1, 1, 3, 6]
def baseStart_454709 : Nat := 118140960795 + 454709 * 2 ^ 59
def prefixEnd_454709 : Nat := 4983230072969 + 3 ^ 40 * 454709 * 2
def baseEnd_454709 : Nat := 138361051807624700827459

theorem tailTrace_454709 : CollatzResearch.WordTrace tailWord_454709 prefixEnd_454709 138361051807624700827459 := by
  unfold tailWord_454709
  simp only [CollatzResearch.WordTrace]
  refine ⟨16584599709674425959631181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11056399806449617306420787 16584599709674425959631181)
  ·
    refine ⟨6219224891127909734861693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16584599709674425959631181 6219224891127909734861693)
    ·
      refine ⟨2332209334172966150573135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6219224891127909734861693 2332209334172966150573135)
      ·
        refine ⟨3498314001259449225859703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2332209334172966150573135 3498314001259449225859703)
        ·
          refine ⟨5247471001889173838789555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3498314001259449225859703 5247471001889173838789555)
          ·
            refine ⟨7871206502833760758184333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5247471001889173838789555 7871206502833760758184333)
            ·
              refine ⟨2951702438562660284319125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7871206502833760758184333 2951702438562660284319125)
              ·
                refine ⟨138361051807624700827459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2951702438562660284319125 138361051807624700827459)
                ·
                  rfl

theorem cell19_454709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 6].length) (baseStart_454709 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_454709 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_454709 prefixEnd_454709 := by exact prefixLift 454709
  have htrace : WordTrace (prefixWord ++ tailWord_454709) baseStart_454709 baseEnd_454709 := by
    simpa [prefixWord, tailWord_454709, baseEnd_454709] using wordTrace_append hprefix tailTrace_454709
  have hstable : (prefixWord ++ tailWord_454709).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454709).length < 2 ^ (prefixWord ++ tailWord_454709).sum := by decide
  have hdescent : baseEnd_454709 < baseStart_454709 := by decide
  rcases family_descends (prefixWord ++ tailWord_454709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454762 : List Nat := [3, 1, 3, 2, 3, 2, 1, 4]
def baseStart_454762 : Nat := 118140960795 + 454762 * 2 ^ 59
def prefixEnd_454762 : Nat := 4983230072969 + 3 ^ 40 * 454762 * 2
def baseEnd_454762 : Nat := 138377178903736281649537

theorem tailTrace_454762 : CollatzResearch.WordTrace tailWord_454762 prefixEnd_454762 138377178903736281649537 := by
  unfold tailWord_454762
  simp only [CollatzResearch.WordTrace]
  refine ⟨4146633194620604002827635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11057688518988277340873693 4146633194620604002827635)
  ·
    refine ⟨6219949791930906004241453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4146633194620604002827635 6219949791930906004241453)
    ·
      refine ⟨2332481171974089751590545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6219949791930906004241453 2332481171974089751590545)
      ·
        refine ⟨1749360878980567313692909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2332481171974089751590545 1749360878980567313692909)
        ·
          refine ⟨656010329617712742634841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1749360878980567313692909 656010329617712742634841)
          ·
            refine ⟨492007747213284556976131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 656010329617712742634841 492007747213284556976131)
            ·
              refine ⟨738011620819926835464197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 492007747213284556976131 738011620819926835464197)
              ·
                refine ⟨138377178903736281649537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 738011620819926835464197 138377178903736281649537)
                ·
                  rfl

theorem cell19_454762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 4].length) (baseStart_454762 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_454762 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_454762 prefixEnd_454762 := by exact prefixLift 454762
  have htrace : WordTrace (prefixWord ++ tailWord_454762) baseStart_454762 baseEnd_454762 := by
    simpa [prefixWord, tailWord_454762, baseEnd_454762] using wordTrace_append hprefix tailTrace_454762
  have hstable : (prefixWord ++ tailWord_454762).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454762).length < 2 ^ (prefixWord ++ tailWord_454762).sum := by decide
  have hdescent : baseEnd_454762 < baseStart_454762 := by decide
  rcases family_descends (prefixWord ++ tailWord_454762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454764 : List Nat := [2, 2, 1, 1, 3, 5, 1, 4]
def baseStart_454764 : Nat := 118140960795 + 454764 * 2 ^ 59
def prefixEnd_454764 : Nat := 4983230072969 + 3 ^ 40 * 454764 * 2
def baseEnd_454764 : Nat := 138377787473400869605087

theorem tailTrace_454764 : CollatzResearch.WordTrace tailWord_454764 prefixEnd_454764 138377787473400869605087 := by
  unfold tailWord_454764
  simp only [CollatzResearch.WordTrace]
  refine ⟨8293302862237585176441673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11057737149650113568588897 8293302862237585176441673)
  ·
    refine ⟨6219977146678188882331255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8293302862237585176441673 6219977146678188882331255)
    ·
      refine ⟨9329965720017283323496883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6219977146678188882331255 9329965720017283323496883)
      ·
        refine ⟨13994948580025924985245325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9329965720017283323496883 13994948580025924985245325)
        ·
          refine ⟨5248105717509721869466997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13994948580025924985245325 5248105717509721869466997)
          ·
            refine ⟨492009911016536425262531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5248105717509721869466997 492009911016536425262531)
            ·
              refine ⟨738014866524804637893797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 492009911016536425262531 738014866524804637893797)
              ·
                refine ⟨138377787473400869605087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 738014866524804637893797 138377787473400869605087)
                ·
                  rfl

theorem cell19_454764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 4].length) (baseStart_454764 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_454764 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_454764 prefixEnd_454764 := by exact prefixLift 454764
  have htrace : WordTrace (prefixWord ++ tailWord_454764) baseStart_454764 baseEnd_454764 := by
    simpa [prefixWord, tailWord_454764, baseEnd_454764] using wordTrace_append hprefix tailTrace_454764
  have hstable : (prefixWord ++ tailWord_454764).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454764).length < 2 ^ (prefixWord ++ tailWord_454764).sum := by decide
  have hdescent : baseEnd_454764 < baseStart_454764 := by decide
  rcases family_descends (prefixWord ++ tailWord_454764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454880 : List Nat := [2, 1, 1, 3, 1, 3, 4, 4]
def baseStart_454880 : Nat := 118140960795 + 454880 * 2 ^ 59
def prefixEnd_454880 : Nat := 4983230072969 + 3 ^ 40 * 454880 * 2
def baseEnd_454880 : Nat := 138413084513946971026993

theorem tailTrace_454880 : CollatzResearch.WordTrace tailWord_454880 prefixEnd_454880 138413084513946971026993 := by
  unfold tailWord_454880
  simp only [CollatzResearch.WordTrace]
  refine ⟨8295418296027461082053047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11060557728036614776070729 8295418296027461082053047)
  ·
    refine ⟨12443127444041191623079571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8295418296027461082053047 12443127444041191623079571)
    ·
      refine ⟨18664691166061787434619357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12443127444041191623079571 18664691166061787434619357)
      ·
        refine ⟨6999259187273170287982259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18664691166061787434619357 6999259187273170287982259)
        ·
          refine ⟨10498888780909755431973389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6999259187273170287982259 10498888780909755431973389)
          ·
            refine ⟨3937083292841158286990021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10498888780909755431973389 3937083292841158286990021)
            ·
              refine ⟨738203117407717178810629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3937083292841158286990021 738203117407717178810629)
              ·
                refine ⟨138413084513946971026993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 738203117407717178810629 138413084513946971026993)
                ·
                  rfl

theorem cell19_454880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 4].length) (baseStart_454880 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_454880 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_454880 prefixEnd_454880 := by exact prefixLift 454880
  have htrace : WordTrace (prefixWord ++ tailWord_454880) baseStart_454880 baseEnd_454880 := by
    simpa [prefixWord, tailWord_454880, baseEnd_454880] using wordTrace_append hprefix tailTrace_454880
  have hstable : (prefixWord ++ tailWord_454880).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454880).length < 2 ^ (prefixWord ++ tailWord_454880).sum := by decide
  have hdescent : baseEnd_454880 < baseStart_454880 := by decide
  rcases family_descends (prefixWord ++ tailWord_454880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454916 : List Nat := [2, 3, 2, 2, 4, 6]
def baseStart_454916 : Nat := 118140960795 + 454916 * 2 ^ 59
def prefixEnd_454916 : Nat := 4983230072969 + 3 ^ 40 * 454916 * 2
def baseEnd_454916 : Nat := 15380448751989950469655

theorem tailTrace_454916 : CollatzResearch.WordTrace tailWord_454916 prefixEnd_454916 15380448751989950469655 := by
  unfold tailWord_454916
  simp only [CollatzResearch.WordTrace]
  refine ⟨8296074809962250156208301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11061433079949666874944401 8296074809962250156208301)
  ·
    refine ⟨3111028053735843808578113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8296074809962250156208301 3111028053735843808578113)
    ·
      refine ⟨2333271040301882856433585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3111028053735843808578113 2333271040301882856433585)
      ·
        refine ⟨1749953280226412142325189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2333271040301882856433585 1749953280226412142325189)
        ·
          refine ⟨328116240042452276685973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1749953280226412142325189 328116240042452276685973)
          ·
            refine ⟨15380448751989950469655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 328116240042452276685973 15380448751989950469655)
            ·
              rfl

theorem cell19_454916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 6].length) (baseStart_454916 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_454916 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_454916 prefixEnd_454916 := by exact prefixLift 454916
  have htrace : WordTrace (prefixWord ++ tailWord_454916) baseStart_454916 baseEnd_454916 := by
    simpa [prefixWord, tailWord_454916, baseEnd_454916] using wordTrace_append hprefix tailTrace_454916
  have hstable : (prefixWord ++ tailWord_454916).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454916).length < 2 ^ (prefixWord ++ tailWord_454916).sum := by decide
  have hdescent : baseEnd_454916 < baseStart_454916 := by decide
  rcases family_descends (prefixWord ++ tailWord_454916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454935 : List Nat := [1, 1, 3, 4, 1, 4, 1, 4]
def baseStart_454935 : Nat := 118140960795 + 454935 * 2 ^ 59
def prefixEnd_454935 : Nat := 4983230072969 + 3 ^ 40 * 454935 * 2
def baseEnd_454935 : Nat := 138429820179723139804621

theorem tailTrace_454935 : CollatzResearch.WordTrace tailWord_454935 prefixEnd_454935 138429820179723139804621 := by
  unfold tailWord_454935
  simp only [CollatzResearch.WordTrace]
  refine ⟨16592842606855666557358259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11061895071237111038238839 16592842606855666557358259)
  ·
    refine ⟨24889263910283499836037389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16592842606855666557358259 24889263910283499836037389)
    ·
      refine ⟨9333473966356312438514021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24889263910283499836037389 9333473966356312438514021)
      ·
        refine ⟨1750026368691808582221379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9333473966356312438514021 1750026368691808582221379)
        ·
          refine ⟨2625039553037712873332069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1750026368691808582221379 2625039553037712873332069)
          ·
            refine ⟨492194916194571163749763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2625039553037712873332069 492194916194571163749763)
            ·
              refine ⟨738292374291856745624645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 492194916194571163749763 738292374291856745624645)
              ·
                refine ⟨138429820179723139804621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 738292374291856745624645 138429820179723139804621)
                ·
                  rfl

theorem cell19_454935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 4].length) (baseStart_454935 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_454935 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_454935 prefixEnd_454935 := by exact prefixLift 454935
  have htrace : WordTrace (prefixWord ++ tailWord_454935) baseStart_454935 baseEnd_454935 := by
    simpa [prefixWord, tailWord_454935, baseEnd_454935] using wordTrace_append hprefix tailTrace_454935
  have hstable : (prefixWord ++ tailWord_454935).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454935).length < 2 ^ (prefixWord ++ tailWord_454935).sum := by decide
  have hdescent : baseEnd_454935 < baseStart_454935 := by decide
  rcases family_descends (prefixWord ++ tailWord_454935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_454952 : List Nat := [2, 1, 5, 1, 3, 1, 3, 3]
def baseStart_454952 : Nat := 118140960795 + 454952 * 2 ^ 59
def prefixEnd_454952 : Nat := 4983230072969 + 3 ^ 40 * 454952 * 2
def baseEnd_454952 : Nat := 138434993021872137426797

theorem tailTrace_454952 : CollatzResearch.WordTrace tailWord_454952 prefixEnd_454952 138434993021872137426797 := by
  unfold tailWord_454952
  simp only [CollatzResearch.WordTrace]
  refine ⟨8296731323897039230363555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11062308431862718973818073 8296731323897039230363555)
  ·
    refine ⟨12445096985845558845545333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8296731323897039230363555 12445096985845558845545333)
    ·
      refine ⟨1166727842423021141769875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12445096985845558845545333 1166727842423021141769875)
      ·
        refine ⟨1750091763634531712654813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1166727842423021141769875 1750091763634531712654813)
        ·
          refine ⟨656284411362949392245555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1750091763634531712654813 656284411362949392245555)
          ·
            refine ⟨984426617044424088368333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 656284411362949392245555 984426617044424088368333)
            ·
              refine ⟨369159981391659033138125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 984426617044424088368333 369159981391659033138125)
              ·
                refine ⟨138434993021872137426797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 369159981391659033138125 138434993021872137426797)
                ·
                  rfl

theorem cell19_454952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 3, 3].length) (baseStart_454952 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_454952 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_454952 prefixEnd_454952 := by exact prefixLift 454952
  have htrace : WordTrace (prefixWord ++ tailWord_454952) baseStart_454952 baseEnd_454952 := by
    simpa [prefixWord, tailWord_454952, baseEnd_454952] using wordTrace_append hprefix tailTrace_454952
  have hstable : (prefixWord ++ tailWord_454952).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_454952).length < 2 ^ (prefixWord ++ tailWord_454952).sum := by decide
  have hdescent : baseEnd_454952 < baseStart_454952 := by decide
  rcases family_descends (prefixWord ++ tailWord_454952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455013 : List Nat := [1, 3, 1, 3, 1, 4, 1, 5]
def baseStart_455013 : Nat := 118140960795 + 455013 * 2 ^ 59
def prefixEnd_455013 : Nat := 4983230072969 + 3 ^ 40 * 455013 * 2
def baseEnd_455013 : Nat := 138453554396642070071075

theorem tailTrace_455013 : CollatzResearch.WordTrace tailWord_455013 prefixEnd_455013 138453554396642070071075 := by
  unfold tailWord_455013
  simp only [CollatzResearch.WordTrace]
  refine ⟨16595687500573085878697693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11063791667048723919131795 16595687500573085878697693)
  ·
    refine ⟨6223382812714907204511635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16595687500573085878697693 6223382812714907204511635)
    ·
      refine ⟨9335074219072360806767453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6223382812714907204511635 9335074219072360806767453)
      ·
        refine ⟨3500652832152135302537795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9335074219072360806767453 3500652832152135302537795)
        ·
          refine ⟨5250979248228202953806693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3500652832152135302537795 5250979248228202953806693)
          ·
            refine ⟨984558609042788053838755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5250979248228202953806693 984558609042788053838755)
            ·
              refine ⟨1476837913564182080758133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 984558609042788053838755 1476837913564182080758133)
              ·
                refine ⟨138453554396642070071075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1476837913564182080758133 138453554396642070071075)
                ·
                  rfl

theorem cell19_455013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 5].length) (baseStart_455013 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_455013 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_455013 prefixEnd_455013 := by exact prefixLift 455013
  have htrace : WordTrace (prefixWord ++ tailWord_455013) baseStart_455013 baseEnd_455013 := by
    simpa [prefixWord, tailWord_455013, baseEnd_455013] using wordTrace_append hprefix tailTrace_455013
  have hstable : (prefixWord ++ tailWord_455013).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455013).length < 2 ^ (prefixWord ++ tailWord_455013).sum := by decide
  have hdescent : baseEnd_455013 < baseStart_455013 := by decide
  rcases family_descends (prefixWord ++ tailWord_455013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455051 : List Nat := [1, 1, 1, 1, 4, 5, 2, 4]
def baseStart_455051 : Nat := 118140960795 + 455051 * 2 ^ 59
def prefixEnd_455051 : Nat := 4983230072969 + 3 ^ 40 * 455051 * 2
def baseEnd_455051 : Nat := 138465117220269241226527

theorem tailTrace_455051 : CollatzResearch.WordTrace tailWord_455051 prefixEnd_455051 138465117220269241226527 := by
  unfold tailWord_455051
  simp only [CollatzResearch.WordTrace]
  refine ⟨16597073474435418368581007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11064715649623612245720671 16597073474435418368581007)
  ·
    refine ⟨24895610211653127552871511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16597073474435418368581007 24895610211653127552871511)
    ·
      refine ⟨37343415317479691329307267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24895610211653127552871511 37343415317479691329307267)
      ·
        refine ⟨56015122976219536993960901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37343415317479691329307267 56015122976219536993960901)
        ·
          refine ⟨10502835558041163186367669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56015122976219536993960901 10502835558041163186367669)
          ·
            refine ⟨984640833566359048721969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10502835558041163186367669 984640833566359048721969)
            ·
              refine ⟨738480625174769286541477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 984640833566359048721969 738480625174769286541477)
              ·
                refine ⟨138465117220269241226527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 738480625174769286541477 138465117220269241226527)
                ·
                  rfl

theorem cell19_455051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 4].length) (baseStart_455051 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_455051 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_455051 prefixEnd_455051 := by exact prefixLift 455051
  have htrace : WordTrace (prefixWord ++ tailWord_455051) baseStart_455051 baseEnd_455051 := by
    simpa [prefixWord, tailWord_455051, baseEnd_455051] using wordTrace_append hprefix tailTrace_455051
  have hstable : (prefixWord ++ tailWord_455051).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455051).length < 2 ^ (prefixWord ++ tailWord_455051).sum := by decide
  have hdescent : baseEnd_455051 < baseStart_455051 := by decide
  rcases family_descends (prefixWord ++ tailWord_455051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455125 : List Nat := [1, 3, 2, 3, 1, 3, 3, 3]
def baseStart_455125 : Nat := 118140960795 + 455125 * 2 ^ 59
def prefixEnd_455125 : Nat := 4983230072969 + 3 ^ 40 * 455125 * 2
def baseEnd_455125 : Nat := 138487634297858995581881

theorem tailTrace_455125 : CollatzResearch.WordTrace tailWord_455125 prefixEnd_455125 138487634297858995581881 := by
  unfold tailWord_455125
  simp only [CollatzResearch.WordTrace]
  refine ⟨16599772476167329006774829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11066514984111552671183219 16599772476167329006774829)
  ·
    refine ⟨6224914678562748377540561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16599772476167329006774829 6224914678562748377540561)
    ·
      refine ⟨4668686008922061283155421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6224914678562748377540561 4668686008922061283155421)
      ·
        refine ⟨1750757253345772981183283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4668686008922061283155421 1750757253345772981183283)
        ·
          refine ⟨2626135880018659471774925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1750757253345772981183283 2626135880018659471774925)
          ·
            refine ⟨984800955006997301915597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2626135880018659471774925 984800955006997301915597)
            ·
              refine ⟨369300358127623988218349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 984800955006997301915597 369300358127623988218349)
              ·
                refine ⟨138487634297858995581881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 369300358127623988218349 138487634297858995581881)
                ·
                  rfl

theorem cell19_455125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 3, 3].length) (baseStart_455125 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_455125 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_455125 prefixEnd_455125 := by exact prefixLift 455125
  have htrace : WordTrace (prefixWord ++ tailWord_455125) baseStart_455125 baseEnd_455125 := by
    simpa [prefixWord, tailWord_455125, baseEnd_455125] using wordTrace_append hprefix tailTrace_455125
  have hstable : (prefixWord ++ tailWord_455125).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455125).length < 2 ^ (prefixWord ++ tailWord_455125).sum := by decide
  have hdescent : baseEnd_455125 < baseStart_455125 := by decide
  rcases family_descends (prefixWord ++ tailWord_455125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455146 : List Nat := [3, 1, 3, 1, 3, 2, 6]
def baseStart_455146 : Nat := 118140960795 + 455146 * 2 ^ 59
def prefixEnd_455146 : Nat := 4983230072969 + 3 ^ 40 * 455146 * 2
def baseEnd_455146 : Nat := 46164674759779056371719

theorem tailTrace_455146 : CollatzResearch.WordTrace tailWord_455146 prefixEnd_455146 46164674759779056371719 := by
  unfold tailWord_455146
  simp only [CollatzResearch.WordTrace]
  refine ⟨4150134602272812398322323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11067025606060833062192861 4150134602272812398322323)
  ·
    refine ⟨6225201903409218597483485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4150134602272812398322323 6225201903409218597483485)
    ·
      refine ⟨2334450713778456974056307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6225201903409218597483485 2334450713778456974056307)
      ·
        refine ⟨3501676070667685461084461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2334450713778456974056307 3501676070667685461084461)
        ·
          refine ⟨1313128526500382047906673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3501676070667685461084461 1313128526500382047906673)
          ·
            refine ⟨984846394875286535930005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1313128526500382047906673 984846394875286535930005)
            ·
              refine ⟨46164674759779056371719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 984846394875286535930005 46164674759779056371719)
              ·
                rfl

theorem cell19_455146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 6].length) (baseStart_455146 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_455146 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_455146 prefixEnd_455146 := by exact prefixLift 455146
  have htrace : WordTrace (prefixWord ++ tailWord_455146) baseStart_455146 baseEnd_455146 := by
    simpa [prefixWord, tailWord_455146, baseEnd_455146] using wordTrace_append hprefix tailTrace_455146
  have hstable : (prefixWord ++ tailWord_455146).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455146).length < 2 ^ (prefixWord ++ tailWord_455146).sum := by decide
  have hdescent : baseEnd_455146 < baseStart_455146 := by decide
  rcases family_descends (prefixWord ++ tailWord_455146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455148 : List Nat := [2, 2, 1, 1, 2, 1, 10]
def baseStart_455148 : Nat := 118140960795 + 455148 * 2 ^ 59
def prefixEnd_455148 : Nat := 4983230072969 + 3 ^ 40 * 455148 * 2
def baseEnd_455148 : Nat := 46164877616333919023569

theorem tailTrace_455148 : CollatzResearch.WordTrace tailWord_455148 prefixEnd_455148 46164877616333919023569 := by
  unfold tailWord_455148
  simp only [CollatzResearch.WordTrace]
  refine ⟨8300305677542001967431049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11067074236722669289908065 8300305677542001967431049)
  ·
    refine ⟨6225229258156501475573287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8300305677542001967431049 6225229258156501475573287)
    ·
      refine ⟨9337843887234752213359931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6225229258156501475573287 9337843887234752213359931)
      ·
        refine ⟨14006765830852128320039897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9337843887234752213359931 14006765830852128320039897)
        ·
          refine ⟨10505074373139096240029923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14006765830852128320039897 10505074373139096240029923)
          ·
            refine ⟨15757611559708644360044885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10505074373139096240029923 15757611559708644360044885)
            ·
              refine ⟨46164877616333919023569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15757611559708644360044885 46164877616333919023569)
              ·
                rfl

theorem cell19_455148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 10].length) (baseStart_455148 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_455148 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_455148 prefixEnd_455148 := by exact prefixLift 455148
  have htrace : WordTrace (prefixWord ++ tailWord_455148) baseStart_455148 baseEnd_455148 := by
    simpa [prefixWord, tailWord_455148, baseEnd_455148] using wordTrace_append hprefix tailTrace_455148
  have hstable : (prefixWord ++ tailWord_455148).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455148).length < 2 ^ (prefixWord ++ tailWord_455148).sum := by decide
  have hdescent : baseEnd_455148 < baseStart_455148 := by decide
  rcases family_descends (prefixWord ++ tailWord_455148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455167 : List Nat := [1, 1, 2, 2, 1, 2, 4, 6]
def baseStart_455167 : Nat := 118140960795 + 455167 * 2 ^ 59
def prefixEnd_455167 : Nat := 4983230072969 + 3 ^ 40 * 455167 * 2
def baseEnd_455167 : Nat := 138500414260815342648433

theorem tailTrace_455167 : CollatzResearch.WordTrace tailWord_455167 prefixEnd_455167 138500414260815342648433 := by
  unfold tailWord_455167
  simp only [CollatzResearch.WordTrace]
  refine ⟨16601304342015170179803755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11067536228010113453202503 16601304342015170179803755)
  ·
    refine ⟨24901956513022755269705633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16601304342015170179803755 24901956513022755269705633)
    ·
      refine ⟨18676467384767066452279225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24901956513022755269705633 18676467384767066452279225)
      ·
        refine ⟨14007350538575299839209419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18676467384767066452279225 14007350538575299839209419)
        ·
          refine ⟨21011025807862949758814129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14007350538575299839209419 21011025807862949758814129)
          ·
            refine ⟨15758269355897212319110597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21011025807862949758814129 15758269355897212319110597)
            ·
              refine ⟨2954675504230727309833237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15758269355897212319110597 2954675504230727309833237)
              ·
                refine ⟨138500414260815342648433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2954675504230727309833237 138500414260815342648433)
                ·
                  rfl

theorem cell19_455167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 6].length) (baseStart_455167 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_455167 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_455167 prefixEnd_455167 := by exact prefixLift 455167
  have htrace : WordTrace (prefixWord ++ tailWord_455167) baseStart_455167 baseEnd_455167 := by
    simpa [prefixWord, tailWord_455167, baseEnd_455167] using wordTrace_append hprefix tailTrace_455167
  have hstable : (prefixWord ++ tailWord_455167).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455167).length < 2 ^ (prefixWord ++ tailWord_455167).sum := by decide
  have hdescent : baseEnd_455167 < baseStart_455167 := by decide
  rcases family_descends (prefixWord ++ tailWord_455167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455182 : List Nat := [4, 1, 1, 2, 3, 1, 4, 3]
def baseStart_455182 : Nat := 118140960795 + 455182 * 2 ^ 59
def prefixEnd_455182 : Nat := 4983230072969 + 3 ^ 40 * 455182 * 2
def baseEnd_455182 : Nat := 138504978533299752315059

theorem tailTrace_455182 : CollatzResearch.WordTrace tailWord_455182 prefixEnd_455182 138504978533299752315059 := by
  unfold tailWord_455182
  simp only [CollatzResearch.WordTrace]
  refine ⟨2075231429620103467699975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11067900957973885161066533 2075231429620103467699975)
  ·
    refine ⟨3112847144430155201549963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2075231429620103467699975 3112847144430155201549963)
    ·
      refine ⟨4669270716645232802324945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3112847144430155201549963 4669270716645232802324945)
      ·
        refine ⟨3501953037483924601743709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4669270716645232802324945 3501953037483924601743709)
        ·
          refine ⟨1313232389056471725653891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3501953037483924601743709 1313232389056471725653891)
          ·
            refine ⟨1969848583584707588480837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1313232389056471725653891 1969848583584707588480837)
            ·
              refine ⟨369346609422132672840157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1969848583584707588480837 369346609422132672840157)
              ·
                refine ⟨138504978533299752315059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 369346609422132672840157 138504978533299752315059)
                ·
                  rfl

theorem cell19_455182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 4, 3].length) (baseStart_455182 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_455182 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_455182 prefixEnd_455182 := by exact prefixLift 455182
  have htrace : WordTrace (prefixWord ++ tailWord_455182) baseStart_455182 baseEnd_455182 := by
    simpa [prefixWord, tailWord_455182, baseEnd_455182] using wordTrace_append hprefix tailTrace_455182
  have hstable : (prefixWord ++ tailWord_455182).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455182).length < 2 ^ (prefixWord ++ tailWord_455182).sum := by decide
  have hdescent : baseEnd_455182 < baseStart_455182 := by decide
  rcases family_descends (prefixWord ++ tailWord_455182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455203 : List Nat := [1, 1, 1, 4, 4, 3, 5]
def baseStart_455203 : Nat := 118140960795 + 455203 * 2 ^ 59
def prefixEnd_455203 : Nat := 4983230072969 + 3 ^ 40 * 455203 * 2
def baseEnd_455203 : Nat := 46170456171592641949445

theorem tailTrace_455203 : CollatzResearch.WordTrace tailWord_455203 prefixEnd_455203 46170456171592641949445 := by
  unfold tailWord_455203
  simp only [CollatzResearch.WordTrace]
  refine ⟨16602617369884748328114263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11068411579923165552076175 16602617369884748328114263)
  ·
    refine ⟨24903926054827122492171395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16602617369884748328114263 24903926054827122492171395)
    ·
      refine ⟨37355889082240683738257093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24903926054827122492171395 37355889082240683738257093)
      ·
        refine ⟨7004229202920128200923205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37355889082240683738257093 7004229202920128200923205)
        ·
          refine ⟨1313292975547524037673101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7004229202920128200923205 1313292975547524037673101)
          ·
            refine ⟨492484865830321514127413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1313292975547524037673101 492484865830321514127413)
            ·
              refine ⟨46170456171592641949445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 492484865830321514127413 46170456171592641949445)
              ·
                rfl

theorem cell19_455203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 5].length) (baseStart_455203 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_455203 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_455203 prefixEnd_455203 := by exact prefixLift 455203
  have htrace : WordTrace (prefixWord ++ tailWord_455203) baseStart_455203 baseEnd_455203 := by
    simpa [prefixWord, tailWord_455203, baseEnd_455203] using wordTrace_append hprefix tailTrace_455203
  have hstable : (prefixWord ++ tailWord_455203).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455203).length < 2 ^ (prefixWord ++ tailWord_455203).sum := by decide
  have hdescent : baseEnd_455203 < baseStart_455203 := by decide
  rcases family_descends (prefixWord ++ tailWord_455203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455205 : List Nat := [1, 3, 1, 2, 2, 1, 9]
def baseStart_455205 : Nat := 118140960795 + 455205 * 2 ^ 59
def prefixEnd_455205 : Nat := 4983230072969 + 3 ^ 40 * 455205 * 2
def baseEnd_455205 : Nat := 46170659028147504601295

theorem tailTrace_455205 : CollatzResearch.WordTrace tailWord_455205 prefixEnd_455205 46170659028147504601295 := by
  unfold tailWord_455205
  simp only [CollatzResearch.WordTrace]
  refine ⟨16602690315877502669687069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11068460210585001779791379 16602690315877502669687069)
  ·
    refine ⟨6226008868454063501132651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16602690315877502669687069 6226008868454063501132651)
    ·
      refine ⟨9339013302681095251698977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6226008868454063501132651 9339013302681095251698977)
      ·
        refine ⟨7004259977010821438774233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9339013302681095251698977 7004259977010821438774233)
        ·
          refine ⟨5253194982758116079080675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7004259977010821438774233 5253194982758116079080675)
          ·
            refine ⟨7879792474137174118621013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5253194982758116079080675 7879792474137174118621013)
            ·
              refine ⟨46170659028147504601295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7879792474137174118621013 46170659028147504601295)
              ·
                rfl

theorem cell19_455205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 9].length) (baseStart_455205 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_455205 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_455205 prefixEnd_455205 := by exact prefixLift 455205
  have htrace : WordTrace (prefixWord ++ tailWord_455205) baseStart_455205 baseEnd_455205 := by
    simpa [prefixWord, tailWord_455205, baseEnd_455205] using wordTrace_append hprefix tailTrace_455205
  have hstable : (prefixWord ++ tailWord_455205).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455205).length < 2 ^ (prefixWord ++ tailWord_455205).sum := by decide
  have hdescent : baseEnd_455205 < baseStart_455205 := by decide
  rcases family_descends (prefixWord ++ tailWord_455205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455243 : List Nat := [1, 1, 1, 1, 3, 1, 6, 5]
def baseStart_455243 : Nat := 118140960795 + 455243 * 2 ^ 59
def prefixEnd_455243 : Nat := 4983230072969 + 3 ^ 40 * 455243 * 2
def baseEnd_455243 : Nat := 138523539908069684959337

theorem tailTrace_455243 : CollatzResearch.WordTrace tailWord_455243 prefixEnd_455243 138523539908069684959337 := by
  unfold tailWord_455243
  simp only [CollatzResearch.WordTrace]
  refine ⟨16604076289739835159570383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11069384193159890106380255 16604076289739835159570383)
  ·
    refine ⟨24906114434609752739355575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16604076289739835159570383 24906114434609752739355575)
    ·
      refine ⟨37359171651914629109033363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24906114434609752739355575 37359171651914629109033363)
      ·
        refine ⟨56038757477871943663550045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37359171651914629109033363 56038757477871943663550045)
        ·
          refine ⟨21014534054201978873831267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56038757477871943663550045 21014534054201978873831267)
          ·
            refine ⟨31521801081302968310746901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21014534054201978873831267 31521801081302968310746901)
            ·
              refine ⟨1477584425686076639566261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 31521801081302968310746901 1477584425686076639566261)
              ·
                refine ⟨138523539908069684959337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1477584425686076639566261 138523539908069684959337)
                ·
                  rfl

theorem cell19_455243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 5].length) (baseStart_455243 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_455243 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_455243 prefixEnd_455243 := by exact prefixLift 455243
  have htrace : WordTrace (prefixWord ++ tailWord_455243) baseStart_455243 baseEnd_455243 := by
    simpa [prefixWord, tailWord_455243, baseEnd_455243] using wordTrace_append hprefix tailTrace_455243
  have hstable : (prefixWord ++ tailWord_455243).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455243).length < 2 ^ (prefixWord ++ tailWord_455243).sum := by decide
  have hdescent : baseEnd_455243 < baseStart_455243 := by decide
  rcases family_descends (prefixWord ++ tailWord_455243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455260 : List Nat := [2, 2, 4, 1, 3, 7]
def baseStart_455260 : Nat := 118140960795 + 455260 * 2 ^ 59
def prefixEnd_455260 : Nat := 4983230072969 + 3 ^ 40 * 455260 * 2
def baseEnd_455260 : Nat := 15392079194468742509057

theorem tailTrace_455260 : CollatzResearch.WordTrace tailWord_455260 prefixEnd_455260 15392079194468742509057 := by
  unfold tailWord_455260
  simp only [CollatzResearch.WordTrace]
  refine ⟨8302348165339123531469617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11069797553785498041959489 8302348165339123531469617)
  ·
    refine ⟨6226761124004342648602213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8302348165339123531469617 6226761124004342648602213)
    ·
      refine ⟨1167517710750814246612915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6226761124004342648602213 1167517710750814246612915)
      ·
        refine ⟨1751276566126221369919373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1167517710750814246612915 1751276566126221369919373)
        ·
          refine ⟨656728712297333013719765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1751276566126221369919373 656728712297333013719765)
          ·
            refine ⟨15392079194468742509057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 656728712297333013719765 15392079194468742509057)
            ·
              rfl

theorem cell19_455260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 7].length) (baseStart_455260 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_455260 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_455260 prefixEnd_455260 := by exact prefixLift 455260
  have htrace : WordTrace (prefixWord ++ tailWord_455260) baseStart_455260 baseEnd_455260 := by
    simpa [prefixWord, tailWord_455260, baseEnd_455260] using wordTrace_append hprefix tailTrace_455260
  have hstable : (prefixWord ++ tailWord_455260).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455260).length < 2 ^ (prefixWord ++ tailWord_455260).sum := by decide
  have hdescent : baseEnd_455260 < baseStart_455260 := by decide
  rcases family_descends (prefixWord ++ tailWord_455260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455277 : List Nat := [1, 5, 1, 1, 3, 3, 1, 4]
def baseStart_455277 : Nat := 118140960795 + 455277 * 2 ^ 59
def prefixEnd_455277 : Nat := 4983230072969 + 3 ^ 40 * 455277 * 2
def baseEnd_455277 : Nat := 138533885592367680203689

theorem tailTrace_455277 : CollatzResearch.WordTrace tailWord_455277 prefixEnd_455277 138533885592367680203689 := by
  unfold tailWord_455277
  simp only [CollatzResearch.WordTrace]
  refine ⟨16605316371616658966308085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11070210914411105977538723 16605316371616658966308085)
  ·
    refine ⟨1556748409839061778091383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16605316371616658966308085 1556748409839061778091383)
    ·
      refine ⟨2335122614758592667137075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1556748409839061778091383 2335122614758592667137075)
      ·
        refine ⟨3502683922137889000705613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2335122614758592667137075 3502683922137889000705613)
        ·
          refine ⟨1313506470801708375264605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3502683922137889000705613 1313506470801708375264605)
          ·
            refine ⟨492564926550640640724227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1313506470801708375264605 492564926550640640724227)
            ·
              refine ⟨738847389825960961086341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 492564926550640640724227 738847389825960961086341)
              ·
                refine ⟨138533885592367680203689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 738847389825960961086341 138533885592367680203689)
                ·
                  rfl

theorem cell19_455277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 4].length) (baseStart_455277 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_455277 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_455277 prefixEnd_455277 := by exact prefixLift 455277
  have htrace : WordTrace (prefixWord ++ tailWord_455277) baseStart_455277 baseEnd_455277 := by
    simpa [prefixWord, tailWord_455277, baseEnd_455277] using wordTrace_append hprefix tailTrace_455277
  have hstable : (prefixWord ++ tailWord_455277).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455277).length < 2 ^ (prefixWord ++ tailWord_455277).sum := by decide
  have hdescent : baseEnd_455277 < baseStart_455277 := by decide
  rcases family_descends (prefixWord ++ tailWord_455277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455319 : List Nat := [1, 1, 3, 3, 2, 1, 8]
def baseStart_455319 : Nat := 118140960795 + 455319 * 2 ^ 59
def prefixEnd_455319 : Nat := 4983230072969 + 3 ^ 40 * 455319 * 2
def baseEnd_455319 : Nat := 46182221851774675756747

theorem tailTrace_455319 : CollatzResearch.WordTrace tailWord_455319 prefixEnd_455319 46182221851774675756747 := by
  unfold tailWord_455319
  simp only [CollatzResearch.WordTrace]
  refine ⟨16606848237464500139337011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11071232158309666759558007 16606848237464500139337011)
  ·
    refine ⟨24910272356196750209005517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16606848237464500139337011 24910272356196750209005517)
    ·
      refine ⟨9341352133573781328377069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24910272356196750209005517 9341352133573781328377069)
      ·
        refine ⟨3503007050090167998141401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9341352133573781328377069 3503007050090167998141401)
        ·
          refine ⟨2627255287567625998606051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3503007050090167998141401 2627255287567625998606051)
          ·
            refine ⟨3940882931351438997909077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2627255287567625998606051 3940882931351438997909077)
            ·
              refine ⟨46182221851774675756747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3940882931351438997909077 46182221851774675756747)
              ·
                rfl

theorem cell19_455319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 8].length) (baseStart_455319 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_455319 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_455319 prefixEnd_455319 := by exact prefixLift 455319
  have htrace : WordTrace (prefixWord ++ tailWord_455319) baseStart_455319 baseEnd_455319 := by
    simpa [prefixWord, tailWord_455319, baseEnd_455319] using wordTrace_append hprefix tailTrace_455319
  have hstable : (prefixWord ++ tailWord_455319).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455319).length < 2 ^ (prefixWord ++ tailWord_455319).sum := by decide
  have hdescent : baseEnd_455319 < baseStart_455319 := by decide
  rcases family_descends (prefixWord ++ tailWord_455319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455351 : List Nat := [1, 1, 3, 1, 7, 1, 2, 3]
def baseStart_455351 : Nat := 118140960795 + 455351 * 2 ^ 59
def prefixEnd_455351 : Nat := 4983230072969 + 3 ^ 40 * 455351 * 2
def baseEnd_455351 : Nat := 138556402669957434559043

theorem tailTrace_455351 : CollatzResearch.WordTrace tailWord_455351 prefixEnd_455351 138556402669957434559043 := by
  unfold tailWord_455351
  simp only [CollatzResearch.WordTrace]
  refine ⟨16608015373348569604501907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11072010248899046403001271 16608015373348569604501907)
  ·
    refine ⟨24912023060022854406752861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16608015373348569604501907 24912023060022854406752861)
    ·
      refine ⟨9342008647508570402532323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24912023060022854406752861 9342008647508570402532323)
      ·
        refine ⟨14013012971262855603798485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9342008647508570402532323 14013012971262855603798485)
        ·
          refine ⟨328429991513973178214027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 14013012971262855603798485 328429991513973178214027)
          ·
            refine ⟨492644987270959767321041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328429991513973178214027 492644987270959767321041)
            ·
              refine ⟨369483740453219825490781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 492644987270959767321041 369483740453219825490781)
              ·
                refine ⟨138556402669957434559043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 369483740453219825490781 138556402669957434559043)
                ·
                  rfl

theorem cell19_455351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 2, 3].length) (baseStart_455351 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_455351 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_455351 prefixEnd_455351 := by exact prefixLift 455351
  have htrace : WordTrace (prefixWord ++ tailWord_455351) baseStart_455351 baseEnd_455351 := by
    simpa [prefixWord, tailWord_455351, baseEnd_455351] using wordTrace_append hprefix tailTrace_455351
  have hstable : (prefixWord ++ tailWord_455351).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455351).length < 2 ^ (prefixWord ++ tailWord_455351).sum := by decide
  have hdescent : baseEnd_455351 < baseStart_455351 := by decide
  rcases family_descends (prefixWord ++ tailWord_455351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455374 : List Nat := [4, 1, 1, 1, 3, 4, 5]
def baseStart_455374 : Nat := 118140960795 + 455374 * 2 ^ 59
def prefixEnd_455374 : Nat := 4983230072969 + 3 ^ 40 * 455374 * 2
def baseEnd_455374 : Nat := 46187800407033398682623

theorem tailTrace_455374 : CollatzResearch.WordTrace tailWord_455374 prefixEnd_455374 46187800407033398682623 := by
  unfold tailWord_455374
  simp only [CollatzResearch.WordTrace]
  refine ⟨2076106781533155566573647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11072569501510163021726117 2076106781533155566573647)
  ·
    refine ⟨3114160172299733349860471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2076106781533155566573647 3114160172299733349860471)
    ·
      refine ⟨4671240258449600024790707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3114160172299733349860471 4671240258449600024790707)
      ·
        refine ⟨7006860387674400037186061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4671240258449600024790707 7006860387674400037186061)
        ·
          refine ⟨2627572645377900013944773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7006860387674400037186061 2627572645377900013944773)
          ·
            refine ⟨492669871008356252614645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2627572645377900013944773 492669871008356252614645)
            ·
              refine ⟨46187800407033398682623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 492669871008356252614645 46187800407033398682623)
              ·
                rfl

theorem cell19_455374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 5].length) (baseStart_455374 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_455374 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_455374 prefixEnd_455374 := by exact prefixLift 455374
  have htrace : WordTrace (prefixWord ++ tailWord_455374) baseStart_455374 baseEnd_455374 := by
    simpa [prefixWord, tailWord_455374, baseEnd_455374] using wordTrace_append hprefix tailTrace_455374
  have hstable : (prefixWord ++ tailWord_455374).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455374).length < 2 ^ (prefixWord ++ tailWord_455374).sum := by decide
  have hdescent : baseEnd_455374 < baseStart_455374 := by decide
  rcases family_descends (prefixWord ++ tailWord_455374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455393 : List Nat := [1, 2, 3, 1, 4, 2, 2, 4]
def baseStart_455393 : Nat := 118140960795 + 455393 * 2 ^ 59
def prefixEnd_455393 : Nat := 4983230072969 + 3 ^ 40 * 455393 * 2
def baseEnd_455393 : Nat := 138569182632913781625595

theorem tailTrace_455393 : CollatzResearch.WordTrace tailWord_455393 prefixEnd_455393 138569182632913781625595 := by
  unfold tailWord_455393
  simp only [CollatzResearch.WordTrace]
  refine ⟨16609547239196410777530833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11073031492797607185020555 16609547239196410777530833)
  ·
    refine ⟨12457160429397308083148125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16609547239196410777530833 12457160429397308083148125)
    ·
      refine ⟨4671435161023990531180547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12457160429397308083148125 4671435161023990531180547)
      ·
        refine ⟨7007152741535985796770821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4671435161023990531180547 7007152741535985796770821)
        ·
          refine ⟨1313841139037997336894529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7007152741535985796770821 1313841139037997336894529)
          ·
            refine ⟨985380854278498002670897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1313841139037997336894529 985380854278498002670897)
            ·
              refine ⟨739035640708873502003173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 985380854278498002670897 739035640708873502003173)
              ·
                refine ⟨138569182632913781625595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 739035640708873502003173 138569182632913781625595)
                ·
                  rfl

theorem cell19_455393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 4].length) (baseStart_455393 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_455393 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_455393 prefixEnd_455393 := by exact prefixLift 455393
  have htrace : WordTrace (prefixWord ++ tailWord_455393) baseStart_455393 baseEnd_455393 := by
    simpa [prefixWord, tailWord_455393, baseEnd_455393] using wordTrace_append hprefix tailTrace_455393
  have hstable : (prefixWord ++ tailWord_455393).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455393).length < 2 ^ (prefixWord ++ tailWord_455393).sum := by decide
  have hdescent : baseEnd_455393 < baseStart_455393 := by decide
  rcases family_descends (prefixWord ++ tailWord_455393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455509 : List Nat := [1, 3, 2, 2, 2, 1, 2, 6]
def baseStart_455509 : Nat := 118140960795 + 455509 * 2 ^ 59
def prefixEnd_455509 : Nat := 4983230072969 + 3 ^ 40 * 455509 * 2
def baseEnd_455509 : Nat := 138604479673459883047501

theorem tailTrace_455509 : CollatzResearch.WordTrace tailWord_455509 prefixEnd_455509 138604479673459883047501 := by
  unfold tailWord_455509
  simp only [CollatzResearch.WordTrace]
  refine ⟨16613778106776162588753581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11075852071184108392502387 16613778106776162588753581)
  ·
    refine ⟨6230166790041060970782593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16613778106776162588753581 6230166790041060970782593)
    ·
      refine ⟨4672625092530795728086945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6230166790041060970782593 4672625092530795728086945)
      ·
        refine ⟨3504468819398096796065209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4672625092530795728086945 3504468819398096796065209)
        ·
          refine ⟨2628351614548572597048907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3504468819398096796065209 2628351614548572597048907)
          ·
            refine ⟨3942527421822858895573361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2628351614548572597048907 3942527421822858895573361)
            ·
              refine ⟨2956895566367144171680021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3942527421822858895573361 2956895566367144171680021)
              ·
                refine ⟨138604479673459883047501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2956895566367144171680021 138604479673459883047501)
                ·
                  rfl

theorem cell19_455509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 6].length) (baseStart_455509 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_455509 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_455509 prefixEnd_455509 := by exact prefixLift 455509
  have htrace : WordTrace (prefixWord ++ tailWord_455509) baseStart_455509 baseEnd_455509 := by
    simpa [prefixWord, tailWord_455509, baseEnd_455509] using wordTrace_append hprefix tailTrace_455509
  have hstable : (prefixWord ++ tailWord_455509).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455509).length < 2 ^ (prefixWord ++ tailWord_455509).sum := by decide
  have hdescent : baseEnd_455509 < baseStart_455509 := by decide
  rcases family_descends (prefixWord ++ tailWord_455509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455522 : List Nat := [3, 3, 2, 1, 3, 2, 2, 3]
def baseStart_455522 : Nat := 118140960795 + 455522 * 2 ^ 59
def prefixEnd_455522 : Nat := 4983230072969 + 3 ^ 40 * 455522 * 2
def baseEnd_455522 : Nat := 138608435376279704758577

theorem tailTrace_455522 : CollatzResearch.WordTrace tailWord_455522 prefixEnd_455522 138608435376279704758577 := by
  unfold tailWord_455522
  simp only [CollatzResearch.WordTrace]
  refine ⟨4153563063932266452244205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11076168170486043872651213 4153563063932266452244205)
  ·
    refine ⟨1557586148974599919591577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4153563063932266452244205 1557586148974599919591577)
    ·
      refine ⟨1168189611730949939693683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1557586148974599919591577 1168189611730949939693683)
      ·
        refine ⟨1752284417596424909540525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1168189611730949939693683 1752284417596424909540525)
        ·
          refine ⟨657106656598659341077697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1752284417596424909540525 657106656598659341077697)
          ·
            refine ⟨492829992448994505808273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 657106656598659341077697 492829992448994505808273)
            ·
              refine ⟨369622494336745879356205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 492829992448994505808273 369622494336745879356205)
              ·
                refine ⟨138608435376279704758577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 369622494336745879356205 138608435376279704758577)
                ·
                  rfl

theorem cell19_455522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 2, 3].length) (baseStart_455522 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_455522 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_455522 prefixEnd_455522 := by exact prefixLift 455522
  have htrace : WordTrace (prefixWord ++ tailWord_455522) baseStart_455522 baseEnd_455522 := by
    simpa [prefixWord, tailWord_455522, baseEnd_455522] using wordTrace_append hprefix tailTrace_455522
  have hstable : (prefixWord ++ tailWord_455522).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455522).length < 2 ^ (prefixWord ++ tailWord_455522).sum := by decide
  have hdescent : baseEnd_455522 < baseStart_455522 := by decide
  rcases family_descends (prefixWord ++ tailWord_455522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455524 : List Nat := [2, 3, 1, 1, 4, 3, 2, 3]
def baseStart_455524 : Nat := 118140960795 + 455524 * 2 ^ 59
def prefixEnd_455524 : Nat := 4983230072969 + 3 ^ 40 * 455524 * 2
def baseEnd_455524 : Nat := 138609043945944292714127

theorem tailTrace_455524 : CollatzResearch.WordTrace tailWord_455524 prefixEnd_455524 138609043945944292714127 := by
  unfold tailWord_455524
  simp only [CollatzResearch.WordTrace]
  refine ⟨8307162600860910075274813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11076216801147880100366417 8307162600860910075274813)
  ·
    refine ⟨3115185975322841278228055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8307162600860910075274813 3115185975322841278228055)
    ·
      refine ⟨4672778962984261917342083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3115185975322841278228055 4672778962984261917342083)
      ·
        refine ⟨7009168444476392876013125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4672778962984261917342083 7009168444476392876013125)
        ·
          refine ⟨1314219083339323664252461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7009168444476392876013125 1314219083339323664252461)
          ·
            refine ⟨492832156252246374094673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1314219083339323664252461 492832156252246374094673)
            ·
              refine ⟨369624117189184780571005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 492832156252246374094673 369624117189184780571005)
              ·
                refine ⟨138609043945944292714127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 369624117189184780571005 138609043945944292714127)
                ·
                  rfl

theorem cell19_455524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 2, 3].length) (baseStart_455524 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_455524 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_455524 prefixEnd_455524 := by exact prefixLift 455524
  have htrace : WordTrace (prefixWord ++ tailWord_455524) baseStart_455524 baseEnd_455524 := by
    simpa [prefixWord, tailWord_455524, baseEnd_455524] using wordTrace_append hprefix tailTrace_455524
  have hstable : (prefixWord ++ tailWord_455524).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455524).length < 2 ^ (prefixWord ++ tailWord_455524).sum := by decide
  have hdescent : baseEnd_455524 < baseStart_455524 := by decide
  rcases family_descends (prefixWord ++ tailWord_455524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455623 : List Nat := [1, 1, 4, 1, 1, 2, 5, 4]
def baseStart_455623 : Nat := 118140960795 + 455623 * 2 ^ 59
def prefixEnd_455623 : Nat := 4983230072969 + 3 ^ 40 * 455623 * 2
def baseEnd_455623 : Nat := 138639168144341396513857

theorem tailTrace_455623 : CollatzResearch.WordTrace tailWord_455623 prefixEnd_455623 138639168144341396513857 := by
  unfold tailWord_455623
  simp only [CollatzResearch.WordTrace]
  refine ⟨16617936028363160058403523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11078624018908773372269015 16617936028363160058403523)
  ·
    refine ⟨24926904042544740087605285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16617936028363160058403523 24926904042544740087605285)
    ·
      refine ⟨4673794507977138766425991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24926904042544740087605285 4673794507977138766425991)
      ·
        refine ⟨7010691761965708149638987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4673794507977138766425991 7010691761965708149638987)
        ·
          refine ⟨10516037642948562224458481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7010691761965708149638987 10516037642948562224458481)
          ·
            refine ⟨7887028232211421668343861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10516037642948562224458481 7887028232211421668343861)
            ·
              refine ⟨739408896769820781407237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7887028232211421668343861 739408896769820781407237)
              ·
                refine ⟨138639168144341396513857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 739408896769820781407237 138639168144341396513857)
                ·
                  rfl

theorem cell19_455623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 4].length) (baseStart_455623 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_455623 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_455623 prefixEnd_455623 := by exact prefixLift 455623
  have htrace : WordTrace (prefixWord ++ tailWord_455623) baseStart_455623 baseEnd_455623 := by
    simpa [prefixWord, tailWord_455623, baseEnd_455623] using wordTrace_append hprefix tailTrace_455623
  have hstable : (prefixWord ++ tailWord_455623).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455623).length < 2 ^ (prefixWord ++ tailWord_455623).sum := by decide
  have hdescent : baseEnd_455623 < baseStart_455623 := by decide
  rcases family_descends (prefixWord ++ tailWord_455623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455640 : List Nat := [2, 1, 2, 2, 2, 4, 3, 3]
def baseStart_455640 : Nat := 118140960795 + 455640 * 2 ^ 59
def prefixEnd_455640 : Nat := 4983230072969 + 3 ^ 40 * 455640 * 2
def baseEnd_455640 : Nat := 138644340986490394136033

theorem tailTrace_455640 : CollatzResearch.WordTrace tailWord_455640 prefixEnd_455640 138644340986490394136033 := by
  unfold tailWord_455640
  simp only [CollatzResearch.WordTrace]
  refine ⟨8309278034650785980886187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11079037379534381307848249 8309278034650785980886187)
  ·
    refine ⟨12463917051976178971329281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8309278034650785980886187 12463917051976178971329281)
    ·
      refine ⟨9347937788982134228496961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12463917051976178971329281 9347937788982134228496961)
      ·
        refine ⟨7010953341736600671372721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9347937788982134228496961 7010953341736600671372721)
        ·
          refine ⟨5258215006302450503529541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7010953341736600671372721 5258215006302450503529541)
          ·
            refine ⟨985915313681709469411789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5258215006302450503529541 985915313681709469411789)
            ·
              refine ⟨369718242630641051029421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 985915313681709469411789 369718242630641051029421)
              ·
                refine ⟨138644340986490394136033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 369718242630641051029421 138644340986490394136033)
                ·
                  rfl

theorem cell19_455640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 3, 3].length) (baseStart_455640 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_455640 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_455640 prefixEnd_455640 := by exact prefixLift 455640
  have htrace : WordTrace (prefixWord ++ tailWord_455640) baseStart_455640 baseEnd_455640 := by
    simpa [prefixWord, tailWord_455640, baseEnd_455640] using wordTrace_append hprefix tailTrace_455640
  have hstable : (prefixWord ++ tailWord_455640).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455640).length < 2 ^ (prefixWord ++ tailWord_455640).sum := by decide
  have hdescent : baseEnd_455640 < baseStart_455640 := by decide
  rcases family_descends (prefixWord ++ tailWord_455640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455716 : List Nat := [2, 3, 1, 4, 1, 3, 5]
def baseStart_455716 : Nat := 118140960795 + 455716 * 2 ^ 59
def prefixEnd_455716 : Nat := 4983230072969 + 3 ^ 40 * 455716 * 2
def baseEnd_455716 : Nat := 46222488877914912148979

theorem tailTrace_455716 : CollatzResearch.WordTrace tailWord_455716 prefixEnd_455716 46222488877914912148979 := by
  unfold tailWord_455716
  simp only [CollatzResearch.WordTrace]
  refine ⟨8310664008513118470769501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11080885344684157961026001 8310664008513118470769501)
  ·
    refine ⟨3116499003192419426538563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8310664008513118470769501 3116499003192419426538563)
    ·
      refine ⟨4674748504788629139807845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3116499003192419426538563 4674748504788629139807845)
      ·
        refine ⟨876515344647867963713971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4674748504788629139807845 876515344647867963713971)
        ·
          refine ⟨1314773016971801945570957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 876515344647867963713971 1314773016971801945570957)
          ·
            refine ⟨493039881364425729589109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1314773016971801945570957 493039881364425729589109)
            ·
              refine ⟨46222488877914912148979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 493039881364425729589109 46222488877914912148979)
              ·
                rfl

theorem cell19_455716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 5].length) (baseStart_455716 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_455716 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_455716 prefixEnd_455716 := by exact prefixLift 455716
  have htrace : WordTrace (prefixWord ++ tailWord_455716) baseStart_455716 baseEnd_455716 := by
    simpa [prefixWord, tailWord_455716, baseEnd_455716] using wordTrace_append hprefix tailTrace_455716
  have hstable : (prefixWord ++ tailWord_455716).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455716).length < 2 ^ (prefixWord ++ tailWord_455716).sum := by decide
  have hdescent : baseEnd_455716 < baseStart_455716 := by decide
  rcases family_descends (prefixWord ++ tailWord_455716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455737 : List Nat := [1, 2, 1, 5, 2, 1, 1, 6]
def baseStart_455737 : Nat := 118140960795 + 455737 * 2 ^ 59
def prefixEnd_455737 : Nat := 4983230072969 + 3 ^ 40 * 455737 * 2
def baseEnd_455737 : Nat := 138673856615222909980213

theorem tailTrace_455737 : CollatzResearch.WordTrace tailWord_455737 prefixEnd_455737 138673856615222909980213 := by
  unfold tailWord_455737
  simp only [CollatzResearch.WordTrace]
  refine ⟨16622093949950157528053465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11081395966633438352035643 16622093949950157528053465)
  ·
    refine ⟨12466570462462618146040099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16622093949950157528053465 12466570462462618146040099)
    ·
      refine ⟨18699855693693927219060149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12466570462462618146040099 18699855693693927219060149)
      ·
        refine ⟨1753111471283805676786889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18699855693693927219060149 1753111471283805676786889)
        ·
          refine ⟨1314833603462854257590167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1753111471283805676786889 1314833603462854257590167)
          ·
            refine ⟨1972250405194281386385251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1314833603462854257590167 1972250405194281386385251)
            ·
              refine ⟨2958375607791422079577877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1972250405194281386385251 2958375607791422079577877)
              ·
                refine ⟨138673856615222909980213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2958375607791422079577877 138673856615222909980213)
                ·
                  rfl

theorem cell19_455737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 6].length) (baseStart_455737 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_455737 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_455737 prefixEnd_455737 := by exact prefixLift 455737
  have htrace : WordTrace (prefixWord ++ tailWord_455737) baseStart_455737 baseEnd_455737 := by
    simpa [prefixWord, tailWord_455737, baseEnd_455737] using wordTrace_append hprefix tailTrace_455737
  have hstable : (prefixWord ++ tailWord_455737).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455737).length < 2 ^ (prefixWord ++ tailWord_455737).sum := by decide
  have hdescent : baseEnd_455737 < baseStart_455737 := by decide
  rcases family_descends (prefixWord ++ tailWord_455737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455773 : List Nat := [1, 4, 4, 1, 2, 7]
def baseStart_455773 : Nat := 118140960795 + 455773 * 2 ^ 59
def prefixEnd_455773 : Nat := 4983230072969 + 3 ^ 40 * 455773 * 2
def baseEnd_455773 : Nat := 15409423429909499242235

theorem tailTrace_455773 : CollatzResearch.WordTrace tailWord_455773 prefixEnd_455773 15409423429909499242235 := by
  unfold tailWord_455773
  simp only [CollatzResearch.WordTrace]
  refine ⟨16623406977819735676363973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11082271318546490450909315 16623406977819735676363973)
  ·
    refine ⟨3116888808341200439318245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16623406977819735676363973 3116888808341200439318245)
    ·
      refine ⟨584416651563975082372171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3116888808341200439318245 584416651563975082372171)
      ·
        refine ⟨876624977345962623558257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 584416651563975082372171 876624977345962623558257)
        ·
          refine ⟨657468733009471967668693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 876624977345962623558257 657468733009471967668693)
          ·
            refine ⟨15409423429909499242235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 657468733009471967668693 15409423429909499242235)
            ·
              rfl

theorem cell19_455773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 7].length) (baseStart_455773 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_455773 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_455773 prefixEnd_455773 := by exact prefixLift 455773
  have htrace : WordTrace (prefixWord ++ tailWord_455773) baseStart_455773 baseEnd_455773 := by
    simpa [prefixWord, tailWord_455773, baseEnd_455773] using wordTrace_append hprefix tailTrace_455773
  have hstable : (prefixWord ++ tailWord_455773).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455773).length < 2 ^ (prefixWord ++ tailWord_455773).sum := by decide
  have hdescent : baseEnd_455773 < baseStart_455773 := by decide
  rcases family_descends (prefixWord ++ tailWord_455773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455832 : List Nat := [2, 1, 2, 4, 2, 2, 6]
def baseStart_455832 : Nat := 118140960795 + 455832 * 2 ^ 59
def prefixEnd_455832 : Nat := 4983230072969 + 3 ^ 40 * 455832 * 2
def baseEnd_455832 : Nat := 46234254558096945956281

theorem tailTrace_455832 : CollatzResearch.WordTrace tailWord_455832 prefixEnd_455832 46234254558096945956281 := by
  unfold tailWord_455832
  simp only [CollatzResearch.WordTrace]
  refine ⟨8312779442302994376380875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11083705923070659168507833 8312779442302994376380875)
  ·
    refine ⟨12469169163454491564571313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8312779442302994376380875 12469169163454491564571313)
    ·
      refine ⟨9351876872590868673428485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12469169163454491564571313 9351876872590868673428485)
      ·
        refine ⟨1753476913610787876267841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9351876872590868673428485 1753476913610787876267841)
        ·
          refine ⟨1315107685208090907200881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1753476913610787876267841 1315107685208090907200881)
          ·
            refine ⟨986330763906068180400661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1315107685208090907200881 986330763906068180400661)
            ·
              refine ⟨46234254558096945956281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 986330763906068180400661 46234254558096945956281)
              ·
                rfl

theorem cell19_455832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 6].length) (baseStart_455832 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_455832 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_455832 prefixEnd_455832 := by exact prefixLift 455832
  have htrace : WordTrace (prefixWord ++ tailWord_455832) baseStart_455832 baseEnd_455832 := by
    simpa [prefixWord, tailWord_455832, baseEnd_455832] using wordTrace_append hprefix tailTrace_455832
  have hstable : (prefixWord ++ tailWord_455832).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455832).length < 2 ^ (prefixWord ++ tailWord_455832).sum := by decide
  have hdescent : baseEnd_455832 < baseStart_455832 := by decide
  rcases family_descends (prefixWord ++ tailWord_455832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455862 : List Nat := [5, 1, 3, 2, 1, 2, 2, 3]
def baseStart_455862 : Nat := 118140960795 + 455862 * 2 ^ 59
def prefixEnd_455862 : Nat := 4983230072969 + 3 ^ 40 * 455862 * 2
def baseEnd_455862 : Nat := 138711892219259657202095

theorem tailTrace_455862 : CollatzResearch.WordTrace tailWord_455862 prefixEnd_455862 138711892219259657202095 := by
  unfold tailWord_455862
  simp only [CollatzResearch.WordTrace]
  refine ⟨1039165817156081492272115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11084435382998202584235893 1039165817156081492272115)
  ·
    refine ⟨1558748725734122238408173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1039165817156081492272115 1558748725734122238408173)
    ·
      refine ⟨584530772150295839403065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1558748725734122238408173 584530772150295839403065)
      ·
        refine ⟨438398079112721879552299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 584530772150295839403065 438398079112721879552299)
        ·
          refine ⟨657597118669082819328449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 438398079112721879552299 657597118669082819328449)
          ·
            refine ⟨493197839001812114496337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 657597118669082819328449 493197839001812114496337)
            ·
              refine ⟨369898379251359085872253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 493197839001812114496337 369898379251359085872253)
              ·
                refine ⟨138711892219259657202095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 369898379251359085872253 138711892219259657202095)
                ·
                  rfl

theorem cell19_455862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_455862 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_455862 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_455862 prefixEnd_455862 := by exact prefixLift 455862
  have htrace : WordTrace (prefixWord ++ tailWord_455862) baseStart_455862 baseEnd_455862 := by
    simpa [prefixWord, tailWord_455862, baseEnd_455862] using wordTrace_append hprefix tailTrace_455862
  have hstable : (prefixWord ++ tailWord_455862).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455862).length < 2 ^ (prefixWord ++ tailWord_455862).sum := by decide
  have hdescent : baseEnd_455862 < baseStart_455862 := by decide
  rcases family_descends (prefixWord ++ tailWord_455862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455868 : List Nat := [2, 2, 2, 3, 2, 1, 4, 3]
def baseStart_455868 : Nat := 118140960795 + 455868 * 2 ^ 59
def prefixEnd_455868 : Nat := 4983230072969 + 3 ^ 40 * 455868 * 2
def baseEnd_455868 : Nat := 138713717928253421068745

theorem tailTrace_455868 : CollatzResearch.WordTrace tailWord_455868 prefixEnd_455868 138713717928253421068745 := by
  unfold tailWord_455868
  simp only [CollatzResearch.WordTrace]
  refine ⟨8313435956237783450536129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11084581274983711267381505 8313435956237783450536129)
  ·
    refine ⟨6235076967178337587902097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8313435956237783450536129 6235076967178337587902097)
    ·
      refine ⟨4676307725383753190926573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6235076967178337587902097 4676307725383753190926573)
      ·
        refine ⟨1753615397018907446597465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4676307725383753190926573 1753615397018907446597465)
        ·
          refine ⟨1315211547764180584948099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1753615397018907446597465 1315211547764180584948099)
          ·
            refine ⟨1972817321646270877422149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1315211547764180584948099 1972817321646270877422149)
            ·
              refine ⟨369903247808675789516653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1972817321646270877422149 369903247808675789516653)
              ·
                refine ⟨138713717928253421068745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 369903247808675789516653 138713717928253421068745)
                ·
                  rfl

theorem cell19_455868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 4, 3].length) (baseStart_455868 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_455868 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_455868 prefixEnd_455868 := by exact prefixLift 455868
  have htrace : WordTrace (prefixWord ++ tailWord_455868) baseStart_455868 baseEnd_455868 := by
    simpa [prefixWord, tailWord_455868, baseEnd_455868] using wordTrace_append hprefix tailTrace_455868
  have hstable : (prefixWord ++ tailWord_455868).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455868).length < 2 ^ (prefixWord ++ tailWord_455868).sum := by decide
  have hdescent : baseEnd_455868 < baseStart_455868 := by decide
  rcases family_descends (prefixWord ++ tailWord_455868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455929 : List Nat := [1, 2, 1, 3, 1, 1, 3, 7]
def baseStart_455929 : Nat := 118140960795 + 455929 * 2 ^ 59
def prefixEnd_455929 : Nat := 4983230072969 + 3 ^ 40 * 455929 * 2
def baseEnd_455929 : Nat := 138732279303023353713023

theorem tailTrace_455929 : CollatzResearch.WordTrace tailWord_455929 prefixEnd_455929 138732279303023353713023 := by
  unfold tailWord_455929
  simp only [CollatzResearch.WordTrace]
  refine ⟨16629096765254574319042841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11086064510169716212695227 16629096765254574319042841)
  ·
    refine ⟨12471822573940930739282131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16629096765254574319042841 12471822573940930739282131)
    ·
      refine ⟨18707733860911396108923197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12471822573940930739282131 18707733860911396108923197)
      ·
        refine ⟨7015400197841773540846199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18707733860911396108923197 7015400197841773540846199)
        ·
          refine ⟨10523100296762660311269299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7015400197841773540846199 10523100296762660311269299)
          ·
            refine ⟨15784650445143990466903949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10523100296762660311269299 15784650445143990466903949)
            ·
              refine ⟨5919243916928996425088981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15784650445143990466903949 5919243916928996425088981)
              ·
                refine ⟨138732279303023353713023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5919243916928996425088981 138732279303023353713023)
                ·
                  rfl

theorem cell19_455929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 7].length) (baseStart_455929 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_455929 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_455929 prefixEnd_455929 := by exact prefixLift 455929
  have htrace : WordTrace (prefixWord ++ tailWord_455929) baseStart_455929 baseEnd_455929 := by
    simpa [prefixWord, tailWord_455929, baseEnd_455929] using wordTrace_append hprefix tailTrace_455929
  have hstable : (prefixWord ++ tailWord_455929).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455929).length < 2 ^ (prefixWord ++ tailWord_455929).sum := by decide
  have hdescent : baseEnd_455929 < baseStart_455929 := by decide
  rcases family_descends (prefixWord ++ tailWord_455929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455948 : List Nat := [2, 2, 1, 2, 2, 10]
def baseStart_455948 : Nat := 118140960795 + 455948 * 2 ^ 59
def prefixEnd_455948 : Nat := 4983230072969 + 3 ^ 40 * 455948 * 2
def baseEnd_455948 : Nat := 15415340079426326587861

theorem tailTrace_455948 : CollatzResearch.WordTrace tailWord_455948 prefixEnd_455948 15415340079426326587861 := by
  unfold tailWord_455948
  simp only [CollatzResearch.WordTrace]
  refine ⟨8314894876092870281992249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11086526501457160375989665 8314894876092870281992249)
  ·
    refine ⟨6236171157069652711494187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8314894876092870281992249 6236171157069652711494187)
    ·
      refine ⟨9354256735604479067241281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6236171157069652711494187 9354256735604479067241281)
      ·
        refine ⟨7015692551703359300430961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9354256735604479067241281 7015692551703359300430961)
        ·
          refine ⟨5261769413777519475323221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7015692551703359300430961 5261769413777519475323221)
          ·
            refine ⟨15415340079426326587861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5261769413777519475323221 15415340079426326587861)
            ·
              rfl

theorem cell19_455948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 10].length) (baseStart_455948 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_455948 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_455948 prefixEnd_455948 := by exact prefixLift 455948
  have htrace : WordTrace (prefixWord ++ tailWord_455948) baseStart_455948 baseEnd_455948 := by
    simpa [prefixWord, tailWord_455948, baseEnd_455948] using wordTrace_append hprefix tailTrace_455948
  have hstable : (prefixWord ++ tailWord_455948).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455948).length < 2 ^ (prefixWord ++ tailWord_455948).sum := by decide
  have hdescent : baseEnd_455948 < baseStart_455948 := by decide
  rcases family_descends (prefixWord ++ tailWord_455948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_455984 : List Nat := [2, 1, 1, 1, 2, 2, 7, 3]
def baseStart_455984 : Nat := 118140960795 + 455984 * 2 ^ 59
def prefixEnd_455984 : Nat := 4983230072969 + 3 ^ 40 * 455984 * 2
def baseEnd_455984 : Nat := 138749014968799522490651

theorem tailTrace_455984 : CollatzResearch.WordTrace tailWord_455984 prefixEnd_455984 138749014968799522490651 := by
  unfold tailWord_455984
  simp only [CollatzResearch.WordTrace]
  refine ⟨8315551390027659356147503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11087401853370212474863337 8315551390027659356147503)
  ·
    refine ⟨12473327085041489034221255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8315551390027659356147503 12473327085041489034221255)
    ·
      refine ⟨18709990627562233551331883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12473327085041489034221255 18709990627562233551331883)
      ·
        refine ⟨28064985941343350326997825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18709990627562233551331883 28064985941343350326997825)
        ·
          refine ⟨21048739456007512745248369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28064985941343350326997825 21048739456007512745248369)
          ·
            refine ⟨15786554592005634558936277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21048739456007512745248369 15786554592005634558936277)
            ·
              refine ⟨369997373250132059975069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 15786554592005634558936277 369997373250132059975069)
              ·
                refine ⟨138749014968799522490651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 369997373250132059975069 138749014968799522490651)
                ·
                  rfl

theorem cell19_455984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 7, 3].length) (baseStart_455984 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_455984 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_455984 prefixEnd_455984 := by exact prefixLift 455984
  have htrace : WordTrace (prefixWord ++ tailWord_455984) baseStart_455984 baseEnd_455984 := by
    simpa [prefixWord, tailWord_455984, baseEnd_455984] using wordTrace_append hprefix tailTrace_455984
  have hstable : (prefixWord ++ tailWord_455984).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_455984).length < 2 ^ (prefixWord ++ tailWord_455984).sum := by decide
  have hdescent : baseEnd_455984 < baseStart_455984 := by decide
  rcases family_descends (prefixWord ++ tailWord_455984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456024 : List Nat := [2, 1, 2, 2, 1, 1, 4, 6]
def baseStart_456024 : Nat := 118140960795 + 456024 * 2 ^ 59
def prefixEnd_456024 : Nat := 4983230072969 + 3 ^ 40 * 456024 * 2
def baseEnd_456024 : Nat := 138761186362091281601653

theorem tailTrace_456024 : CollatzResearch.WordTrace tailWord_456024 prefixEnd_456024 138761186362091281601653 := by
  unfold tailWord_456024
  simp only [CollatzResearch.WordTrace]
  refine ⟨8316280849955202771875563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11088374466606937029167417 8316280849955202771875563)
  ·
    refine ⟨12474421274932804157813345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8316280849955202771875563 12474421274932804157813345)
    ·
      refine ⟨9355815956199603118360009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12474421274932804157813345 9355815956199603118360009)
      ·
        refine ⟨7016861967149702338770007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9355815956199603118360009 7016861967149702338770007)
        ·
          refine ⟨10525292950724553508155011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7016861967149702338770007 10525292950724553508155011)
          ·
            refine ⟨15787939426086830262232517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10525292950724553508155011 15787939426086830262232517)
            ·
              refine ⟨2960238642391280674168597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15787939426086830262232517 2960238642391280674168597)
              ·
                refine ⟨138761186362091281601653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2960238642391280674168597 138761186362091281601653)
                ·
                  rfl

theorem cell19_456024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 6].length) (baseStart_456024 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_456024 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_456024 prefixEnd_456024 := by exact prefixLift 456024
  have htrace : WordTrace (prefixWord ++ tailWord_456024) baseStart_456024 baseEnd_456024 := by
    simpa [prefixWord, tailWord_456024, baseEnd_456024] using wordTrace_append hprefix tailTrace_456024
  have hstable : (prefixWord ++ tailWord_456024).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456024).length < 2 ^ (prefixWord ++ tailWord_456024).sum := by decide
  have hdescent : baseEnd_456024 < baseStart_456024 := by decide
  rcases family_descends (prefixWord ++ tailWord_456024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456098 : List Nat := [3, 3, 1, 2, 1, 2, 2, 5]
def baseStart_456098 : Nat := 118140960795 + 456098 * 2 ^ 59
def prefixEnd_456098 : Nat := 4983230072969 + 3 ^ 40 * 456098 * 2
def baseEnd_456098 : Nat := 138783703439681035957007

theorem tailTrace_456098 : CollatzResearch.WordTrace tailWord_456098 prefixEnd_456098 138783703439681035957007 := by
  unfold tailWord_456098
  simp only [CollatzResearch.WordTrace]
  refine ⟨4158815175410579045486237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11090173801094877454629965 4158815175410579045486237)
  ·
    refine ⟨1559555690778967142057339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4158815175410579045486237 1559555690778967142057339)
    ·
      refine ⟨2339333536168450713086009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1559555690778967142057339 2339333536168450713086009)
      ·
        refine ⟨1754500152126338034814507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2339333536168450713086009 1754500152126338034814507)
        ·
          refine ⟨2631750228189507052221761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1754500152126338034814507 2631750228189507052221761)
          ·
            refine ⟨1973812671142130289166321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2631750228189507052221761 1973812671142130289166321)
            ·
              refine ⟨1480359503356597716874741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1973812671142130289166321 1480359503356597716874741)
              ·
                refine ⟨138783703439681035957007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1480359503356597716874741 138783703439681035957007)
                ·
                  rfl

theorem cell19_456098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 5].length) (baseStart_456098 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_456098 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_456098 prefixEnd_456098 := by exact prefixLift 456098
  have htrace : WordTrace (prefixWord ++ tailWord_456098) baseStart_456098 baseEnd_456098 := by
    simpa [prefixWord, tailWord_456098, baseEnd_456098] using wordTrace_append hprefix tailTrace_456098
  have hstable : (prefixWord ++ tailWord_456098).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456098).length < 2 ^ (prefixWord ++ tailWord_456098).sum := by decide
  have hdescent : baseEnd_456098 < baseStart_456098 := by decide
  rcases family_descends (prefixWord ++ tailWord_456098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456176 : List Nat := [2, 1, 1, 1, 3, 5, 6]
def baseStart_456176 : Nat := 118140960795 + 456176 * 2 ^ 59
def prefixEnd_456176 : Nat := 4983230072969 + 3 ^ 40 * 456176 * 2
def baseEnd_456176 : Nat := 46269145885533322074487

theorem tailTrace_456176 : CollatzResearch.WordTrace tailWord_456176 prefixEnd_456176 46269145885533322074487 := by
  unfold tailWord_456176
  simp only [CollatzResearch.WordTrace]
  refine ⟨8319052797679867751642191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11092070396906490335522921 8319052797679867751642191)
  ·
    refine ⟨12478579196519801627463287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8319052797679867751642191 12478579196519801627463287)
    ·
      refine ⟨18717868794779702441194931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12478579196519801627463287 18717868794779702441194931)
      ·
        refine ⟨28076803192169553661792397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18717868794779702441194931 28076803192169553661792397)
        ·
          refine ⟨10528801197063582623172149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28076803192169553661792397 10528801197063582623172149)
          ·
            refine ⟨987075112224710870922389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10528801197063582623172149 987075112224710870922389)
            ·
              refine ⟨46269145885533322074487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 987075112224710870922389 46269145885533322074487)
              ·
                rfl

theorem cell19_456176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 6].length) (baseStart_456176 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_456176 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_456176 prefixEnd_456176 := by exact prefixLift 456176
  have htrace : WordTrace (prefixWord ++ tailWord_456176) baseStart_456176 baseEnd_456176 := by
    simpa [prefixWord, tailWord_456176, baseEnd_456176] using wordTrace_append hprefix tailTrace_456176
  have hstable : (prefixWord ++ tailWord_456176).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456176).length < 2 ^ (prefixWord ++ tailWord_456176).sum := by decide
  have hdescent : baseEnd_456176 < baseStart_456176 := by decide
  rcases family_descends (prefixWord ++ tailWord_456176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456290 : List Nat := [3, 3, 2, 11]
def baseStart_456290 : Nat := 118140960795 + 456290 * 2 ^ 59
def prefixEnd_456290 : Nat := 4983230072969 + 3 ^ 40 * 456290 * 2
def baseEnd_456290 : Nat := 1714100322561499749257

theorem tailTrace_456290 : CollatzResearch.WordTrace tailWord_456290 prefixEnd_456290 1714100322561499749257 := by
  unfold tailWord_456290
  simp only [CollatzResearch.WordTrace]
  refine ⟨4160565879236683243233581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11094842344631155315289549 4160565879236683243233581)
  ·
    refine ⟨1560212204713756216212593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4160565879236683243233581 1560212204713756216212593)
    ·
      refine ⟨1170159153535317162159445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1560212204713756216212593 1170159153535317162159445)
      ·
        refine ⟨1714100322561499749257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 11 1170159153535317162159445 1714100322561499749257)
        ·
          rfl

theorem cell19_456290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 11].length) (baseStart_456290 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_456290 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_456290 prefixEnd_456290 := by exact prefixLift 456290
  have htrace : WordTrace (prefixWord ++ tailWord_456290) baseStart_456290 baseEnd_456290 := by
    simpa [prefixWord, tailWord_456290, baseEnd_456290] using wordTrace_append hprefix tailTrace_456290
  have hstable : (prefixWord ++ tailWord_456290).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456290).length < 2 ^ (prefixWord ++ tailWord_456290).sum := by decide
  have hdescent : baseEnd_456290 < baseStart_456290 := by decide
  rcases family_descends (prefixWord ++ tailWord_456290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456324 : List Nat := [2, 3, 2, 1, 4, 1, 3, 3]
def baseStart_456324 : Nat := 118140960795 + 456324 * 2 ^ 59
def prefixEnd_456324 : Nat := 4983230072969 + 3 ^ 40 * 456324 * 2
def baseEnd_456324 : Nat := 138852471811779474934169

theorem tailTrace_456324 : CollatzResearch.WordTrace tailWord_456324 prefixEnd_456324 138852471811779474934169 := by
  unfold tailWord_456324
  simp only [CollatzResearch.WordTrace]
  refine ⟨8321751799411778389836013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11095669065882371186448017 8321751799411778389836013)
  ·
    refine ⟨3120656924779416896188505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8321751799411778389836013 3120656924779416896188505)
    ·
      refine ⟨2340492693584562672141379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3120656924779416896188505 2340492693584562672141379)
      ·
        refine ⟨3510739040376844008212069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2340492693584562672141379 3510739040376844008212069)
        ·
          refine ⟨658263570070658251539763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3510739040376844008212069 658263570070658251539763)
          ·
            refine ⟨987395355105987377309645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 658263570070658251539763 987395355105987377309645)
            ·
              refine ⟨370273258164745266491117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 987395355105987377309645 370273258164745266491117)
              ·
                refine ⟨138852471811779474934169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 370273258164745266491117 138852471811779474934169)
                ·
                  rfl

theorem cell19_456324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 3, 3].length) (baseStart_456324 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_456324 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_456324 prefixEnd_456324 := by exact prefixLift 456324
  have htrace : WordTrace (prefixWord ++ tailWord_456324) baseStart_456324 baseEnd_456324 := by
    simpa [prefixWord, tailWord_456324, baseEnd_456324] using wordTrace_append hprefix tailTrace_456324
  have hstable : (prefixWord ++ tailWord_456324).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456324).length < 2 ^ (prefixWord ++ tailWord_456324).sum := by decide
  have hdescent : baseEnd_456324 < baseStart_456324 := by decide
  rcases family_descends (prefixWord ++ tailWord_456324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456402 : List Nat := [3, 2, 2, 2, 2, 3, 5]
def baseStart_456402 : Nat := 118140960795 + 456402 * 2 ^ 59
def prefixEnd_456402 : Nat := 4983230072969 + 3 ^ 40 * 456402 * 2
def baseEnd_456402 : Nat := 46292068676232801733541

theorem tailTrace_456402 : CollatzResearch.WordTrace tailWord_456402 prefixEnd_456402 46292068676232801733541 := by
  unfold tailWord_456402
  simp only [CollatzResearch.WordTrace]
  refine ⟨4161587123135244025252865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11097565661693984067340973 4161587123135244025252865)
  ·
    refine ⟨3121190342351433018939649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4161587123135244025252865 3121190342351433018939649)
    ·
      refine ⟨2340892756763574764204737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3121190342351433018939649 2340892756763574764204737)
      ·
        refine ⟨1755669567572681073153553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2340892756763574764204737 1755669567572681073153553)
        ·
          refine ⟨1316752175679510804865165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1755669567572681073153553 1316752175679510804865165)
          ·
            refine ⟨493782065879816551824437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1316752175679510804865165 493782065879816551824437)
            ·
              refine ⟨46292068676232801733541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 493782065879816551824437 46292068676232801733541)
              ·
                rfl

theorem cell19_456402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 5].length) (baseStart_456402 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_456402 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_456402 prefixEnd_456402 := by exact prefixLift 456402
  have htrace : WordTrace (prefixWord ++ tailWord_456402) baseStart_456402 baseEnd_456402 := by
    simpa [prefixWord, tailWord_456402, baseEnd_456402] using wordTrace_append hprefix tailTrace_456402
  have hstable : (prefixWord ++ tailWord_456402).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456402).length < 2 ^ (prefixWord ++ tailWord_456402).sum := by decide
  have hdescent : baseEnd_456402 < baseStart_456402 := by decide
  rcases family_descends (prefixWord ++ tailWord_456402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456497 : List Nat := [1, 2, 2, 3, 2, 3, 3, 3]
def baseStart_456497 : Nat := 118140960795 + 456497 * 2 ^ 59
def prefixEnd_456497 : Nat := 4983230072969 + 3 ^ 40 * 456497 * 2
def baseEnd_456497 : Nat := 138905113087766333089253

theorem tailTrace_456497 : CollatzResearch.WordTrace tailWord_456497 prefixEnd_456497 138905113087766333089253 := by
  unfold tailWord_456497
  simp only [CollatzResearch.WordTrace]
  refine ⟨16649813427196807325719745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11099875618131204883813163 16649813427196807325719745)
  ·
    refine ⟨12487360070397605494289809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16649813427196807325719745 12487360070397605494289809)
    ·
      refine ⟨9365520052798204120717357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12487360070397605494289809 9365520052798204120717357)
      ·
        refine ⟨3512070019799326545269009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9365520052798204120717357 3512070019799326545269009)
        ·
          refine ⟨2634052514849494908951757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3512070019799326545269009 2634052514849494908951757)
          ·
            refine ⟨987769693068560590856909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2634052514849494908951757 987769693068560590856909)
            ·
              refine ⟨370413634900710221571341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 987769693068560590856909 370413634900710221571341)
              ·
                refine ⟨138905113087766333089253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 370413634900710221571341 138905113087766333089253)
                ·
                  rfl

theorem cell19_456497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 3, 3].length) (baseStart_456497 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_456497 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_456497 prefixEnd_456497 := by exact prefixLift 456497
  have htrace : WordTrace (prefixWord ++ tailWord_456497) baseStart_456497 baseEnd_456497 := by
    simpa [prefixWord, tailWord_456497, baseEnd_456497] using wordTrace_append hprefix tailTrace_456497
  have hstable : (prefixWord ++ tailWord_456497).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456497).length < 2 ^ (prefixWord ++ tailWord_456497).sum := by decide
  have hdescent : baseEnd_456497 < baseStart_456497 := by decide
  rcases family_descends (prefixWord ++ tailWord_456497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456556 : List Nat := [2, 2, 1, 1, 4, 3, 1, 5]
def baseStart_456556 : Nat := 118140960795 + 456556 * 2 ^ 59
def prefixEnd_456556 : Nat := 4983230072969 + 3 ^ 40 * 456556 * 2
def baseEnd_456556 : Nat := 138923065892871677777981

theorem tailTrace_456556 : CollatzResearch.WordTrace tailWord_456556 prefixEnd_456556 138923065892871677777981 := by
  unfold tailWord_456556
  simp only [CollatzResearch.WordTrace]
  refine ⟨8325982666991530201058761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11101310222655373601411681 8325982666991530201058761)
  ·
    refine ⟨6244487000243647650794071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8325982666991530201058761 6244487000243647650794071)
    ·
      refine ⟨9366730500365471476191107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6244487000243647650794071 9366730500365471476191107)
      ·
        refine ⟨14050095750548207214286661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9366730500365471476191107 14050095750548207214286661)
        ·
          refine ⟨2634392953227788852678749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14050095750548207214286661 2634392953227788852678749)
          ·
            refine ⟨987897357460420819754531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2634392953227788852678749 987897357460420819754531)
            ·
              refine ⟨1481846036190631229631797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 987897357460420819754531 1481846036190631229631797)
              ·
                refine ⟨138923065892871677777981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1481846036190631229631797 138923065892871677777981)
                ·
                  rfl

theorem cell19_456556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 5].length) (baseStart_456556 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_456556 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_456556 prefixEnd_456556 := by exact prefixLift 456556
  have htrace : WordTrace (prefixWord ++ tailWord_456556) baseStart_456556 baseEnd_456556 := by
    simpa [prefixWord, tailWord_456556, baseEnd_456556] using wordTrace_append hprefix tailTrace_456556
  have hstable : (prefixWord ++ tailWord_456556).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456556).length < 2 ^ (prefixWord ++ tailWord_456556).sum := by decide
  have hdescent : baseEnd_456556 < baseStart_456556 := by decide
  rcases family_descends (prefixWord ++ tailWord_456556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456590 : List Nat := [4, 1, 1, 5, 1, 1, 2, 4]
def baseStart_456590 : Nat := 118140960795 + 456590 * 2 ^ 59
def prefixEnd_456590 : Nat := 4983230072969 + 3 ^ 40 * 456590 * 2
def baseEnd_456590 : Nat := 138933411577169673022333

theorem tailTrace_456590 : CollatzResearch.WordTrace tailWord_456590 prefixEnd_456590 138933411577169673022333 := by
  unfold tailWord_456590
  simp only [CollatzResearch.WordTrace]
  refine ⟨2081650676982485526106903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11102136943906589472570149 2081650676982485526106903)
  ·
    refine ⟨3122476015473728289160355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2081650676982485526106903 3122476015473728289160355)
    ·
      refine ⟨4683714023210592433740533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3122476015473728289160355 4683714023210592433740533)
      ·
        refine ⟨439098189675993040663175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4683714023210592433740533 439098189675993040663175)
        ·
          refine ⟨658647284513989560994763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 439098189675993040663175 658647284513989560994763)
          ·
            refine ⟨987970926770984341492145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 658647284513989560994763 987970926770984341492145)
            ·
              refine ⟨740978195078238256119109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 987970926770984341492145 740978195078238256119109)
              ·
                refine ⟨138933411577169673022333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 740978195078238256119109 138933411577169673022333)
                ·
                  rfl

theorem cell19_456590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 4].length) (baseStart_456590 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_456590 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_456590 prefixEnd_456590 := by exact prefixLift 456590
  have htrace : WordTrace (prefixWord ++ tailWord_456590) baseStart_456590 baseEnd_456590 := by
    simpa [prefixWord, tailWord_456590, baseEnd_456590] using wordTrace_append hprefix tailTrace_456590
  have hstable : (prefixWord ++ tailWord_456590).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456590).length < 2 ^ (prefixWord ++ tailWord_456590).sum := by decide
  have hdescent : baseEnd_456590 < baseStart_456590 := by decide
  rcases family_descends (prefixWord ++ tailWord_456590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456628 : List Nat := [2, 5, 2, 1, 3, 6]
def baseStart_456628 : Nat := 118140960795 + 456628 * 2 ^ 59
def prefixEnd_456628 : Nat := 4983230072969 + 3 ^ 40 * 456628 * 2
def baseEnd_456628 : Nat := 15438330488977427130865

theorem tailTrace_456628 : CollatzResearch.WordTrace tailWord_456628 prefixEnd_456628 15438330488977427130865 := by
  unfold tailWord_456628
  simp only [CollatzResearch.WordTrace]
  refine ⟨8327295694861108349369269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11103060926481477799159025 8327295694861108349369269)
  ·
    refine ⟨780683971393228907753369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8327295694861108349369269 780683971393228907753369)
    ·
      refine ⟨585512978544921680815027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 780683971393228907753369 585512978544921680815027)
      ·
        refine ⟨878269467817382521222541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 585512978544921680815027 878269467817382521222541)
        ·
          refine ⟨329351050431518445458453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 878269467817382521222541 329351050431518445458453)
          ·
            refine ⟨15438330488977427130865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 329351050431518445458453 15438330488977427130865)
            ·
              rfl

theorem cell19_456628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 6].length) (baseStart_456628 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_456628 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_456628 prefixEnd_456628 := by exact prefixLift 456628
  have htrace : WordTrace (prefixWord ++ tailWord_456628) baseStart_456628 baseEnd_456628 := by
    simpa [prefixWord, tailWord_456628, baseEnd_456628] using wordTrace_append hprefix tailTrace_456628
  have hstable : (prefixWord ++ tailWord_456628).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456628).length < 2 ^ (prefixWord ++ tailWord_456628).sum := by decide
  have hdescent : baseEnd_456628 < baseStart_456628 := by decide
  rcases family_descends (prefixWord ++ tailWord_456628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456630 : List Nat := [5, 1, 4, 9]
def baseStart_456630 : Nat := 118140960795 + 456630 * 2 ^ 59
def prefixEnd_456630 : Nat := 4983230072969 + 3 ^ 40 * 456630 * 2
def baseEnd_456630 : Nat := 1715377567536560890535

theorem tailTrace_456630 : CollatzResearch.WordTrace tailWord_456630 prefixEnd_456630 1715377567536560890535 := by
  unfold tailWord_456630
  simp only [CollatzResearch.WordTrace]
  refine ⟨1040916520982185690019459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11103109557143314026874229 1040916520982185690019459)
  ·
    refine ⟨1561374781473278535029189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1040916520982185690019459 1561374781473278535029189)
    ·
      refine ⟨292757771526239725317973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1561374781473278535029189 292757771526239725317973)
      ·
        refine ⟨1715377567536560890535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 9 292757771526239725317973 1715377567536560890535)
        ·
          rfl

theorem cell19_456630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 9].length) (baseStart_456630 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_456630 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_456630 prefixEnd_456630 := by exact prefixLift 456630
  have htrace : WordTrace (prefixWord ++ tailWord_456630) baseStart_456630 baseEnd_456630 := by
    simpa [prefixWord, tailWord_456630, baseEnd_456630] using wordTrace_append hprefix tailTrace_456630
  have hstable : (prefixWord ++ tailWord_456630).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456630).length < 2 ^ (prefixWord ++ tailWord_456630).sum := by decide
  have hdescent : baseEnd_456630 < baseStart_456630 := by decide
  rcases family_descends (prefixWord ++ tailWord_456630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456672 : List Nat := [2, 1, 1, 3, 1, 1, 1, 9]
def baseStart_456672 : Nat := 118140960795 + 456672 * 2 ^ 59
def prefixEnd_456672 : Nat := 4983230072969 + 3 ^ 40 * 456672 * 2
def baseEnd_456672 : Nat := 138958362933417779199887

theorem tailTrace_456672 : CollatzResearch.WordTrace tailWord_456672 prefixEnd_456672 138958362933417779199887 := by
  unfold tailWord_456672
  simp only [CollatzResearch.WordTrace]
  refine ⟨8328098100781406106670135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11104130801041874808893513 8328098100781406106670135)
  ·
    refine ⟨12492147151172109160005203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8328098100781406106670135 12492147151172109160005203)
    ·
      refine ⟨18738220726758163740007805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12492147151172109160005203 18738220726758163740007805)
      ·
        refine ⟨7026832772534311402502927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18738220726758163740007805 7026832772534311402502927)
        ·
          refine ⟨10540249158801467103754391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7026832772534311402502927 10540249158801467103754391)
          ·
            refine ⟨15810373738202200655631587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10540249158801467103754391 15810373738202200655631587)
            ·
              refine ⟨23715560607303300983447381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15810373738202200655631587 23715560607303300983447381)
              ·
                refine ⟨138958362933417779199887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23715560607303300983447381 138958362933417779199887)
                ·
                  rfl

theorem cell19_456672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 9].length) (baseStart_456672 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_456672 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_456672 prefixEnd_456672 := by exact prefixLift 456672
  have htrace : WordTrace (prefixWord ++ tailWord_456672) baseStart_456672 baseEnd_456672 := by
    simpa [prefixWord, tailWord_456672, baseEnd_456672] using wordTrace_append hprefix tailTrace_456672
  have hstable : (prefixWord ++ tailWord_456672).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456672).length < 2 ^ (prefixWord ++ tailWord_456672).sum := by decide
  have hdescent : baseEnd_456672 < baseStart_456672 := by decide
  rcases family_descends (prefixWord ++ tailWord_456672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456689 : List Nat := [1, 2, 2, 2, 5, 1, 6]
def baseStart_456689 : Nat := 118140960795 + 456689 * 2 ^ 59
def prefixEnd_456689 : Nat := 4983230072969 + 3 ^ 40 * 456689 * 2
def baseEnd_456689 : Nat := 46321178591855592274021

theorem tailTrace_456689 : CollatzResearch.WordTrace tailWord_456689 prefixEnd_456689 46321178591855592274021 := by
  unfold tailWord_456689
  simp only [CollatzResearch.WordTrace]
  refine ⟨16656816242501224116709121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11104544161667482744472747 16656816242501224116709121)
  ·
    refine ⟨12492612181875918087531841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16656816242501224116709121 12492612181875918087531841)
    ·
      refine ⟨9369459136406938565648881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12492612181875918087531841 9369459136406938565648881)
      ·
        refine ⟨7027094352305203924236661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9369459136406938565648881 7027094352305203924236661)
        ·
          refine ⟨658790095528612867897187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7027094352305203924236661 658790095528612867897187)
          ·
            refine ⟨988185143292919301845781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 658790095528612867897187 988185143292919301845781)
            ·
              refine ⟨46321178591855592274021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 988185143292919301845781 46321178591855592274021)
              ·
                rfl

theorem cell19_456689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 6].length) (baseStart_456689 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_456689 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_456689 prefixEnd_456689 := by exact prefixLift 456689
  have htrace : WordTrace (prefixWord ++ tailWord_456689) baseStart_456689 baseEnd_456689 := by
    simpa [prefixWord, tailWord_456689, baseEnd_456689] using wordTrace_append hprefix tailTrace_456689
  have hstable : (prefixWord ++ tailWord_456689).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456689).length < 2 ^ (prefixWord ++ tailWord_456689).sum := by decide
  have hdescent : baseEnd_456689 < baseStart_456689 := by decide
  rcases family_descends (prefixWord ++ tailWord_456689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456717 : List Nat := [1, 7, 1, 2, 2, 1, 2, 3]
def baseStart_456717 : Nat := 118140960795 + 456717 * 2 ^ 59
def prefixEnd_456717 : Nat := 4983230072969 + 3 ^ 40 * 456717 * 2
def baseEnd_456717 : Nat := 138972055750871008199765

theorem tailTrace_456717 : CollatzResearch.WordTrace tailWord_456717 prefixEnd_456717 138972055750871008199765 := by
  unfold tailWord_456717
  simp only [CollatzResearch.WordTrace]
  refine ⟨16657837486399784898728405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11105224990933189932485603 16657837486399784898728405)
  ·
    refine ⟨390418066087494958563947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 16657837486399784898728405 390418066087494958563947)
    ·
      refine ⟨585627099131242437845921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390418066087494958563947 585627099131242437845921)
      ·
        refine ⟨439220324348431828384441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 585627099131242437845921 439220324348431828384441)
        ·
          refine ⟨329415243261323871288331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 439220324348431828384441 329415243261323871288331)
          ·
            refine ⟨494122864891985806932497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 329415243261323871288331 494122864891985806932497)
            ·
              refine ⟨370592148668989355199373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 494122864891985806932497 370592148668989355199373)
              ·
                refine ⟨138972055750871008199765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 370592148668989355199373 138972055750871008199765)
                ·
                  rfl

theorem cell19_456717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 2, 3].length) (baseStart_456717 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_456717 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_456717 prefixEnd_456717 := by exact prefixLift 456717
  have htrace : WordTrace (prefixWord ++ tailWord_456717) baseStart_456717 baseEnd_456717 := by
    simpa [prefixWord, tailWord_456717, baseEnd_456717] using wordTrace_append hprefix tailTrace_456717
  have hstable : (prefixWord ++ tailWord_456717).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456717).length < 2 ^ (prefixWord ++ tailWord_456717).sum := by decide
  have hdescent : baseEnd_456717 < baseStart_456717 := by decide
  rcases family_descends (prefixWord ++ tailWord_456717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456746 : List Nat := [3, 1, 4, 1, 2, 1, 7]
def baseStart_456746 : Nat := 118140960795 + 456746 * 2 ^ 59
def prefixEnd_456746 : Nat := 4983230072969 + 3 ^ 40 * 456746 * 2
def baseEnd_456746 : Nat := 46326960003669177851747

theorem tailTrace_456746 : CollatzResearch.WordTrace tailWord_456746 prefixEnd_456746 46326960003669177851747 := by
  unfold tailWord_456746
  simp only [CollatzResearch.WordTrace]
  refine ⟨4164723800823680712883523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11105930135529815234356061 4164723800823680712883523)
  ·
    refine ⟨6247085701235521069325285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4164723800823680712883523 6247085701235521069325285)
    ·
      refine ⟨1171328568981660200498491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6247085701235521069325285 1171328568981660200498491)
      ·
        refine ⟨1756992853472490300747737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1171328568981660200498491 1756992853472490300747737)
        ·
          refine ⟨1317744640104367725560803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1756992853472490300747737 1317744640104367725560803)
          ·
            refine ⟨1976616960156551588341205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1317744640104367725560803 1976616960156551588341205)
            ·
              refine ⟨46326960003669177851747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1976616960156551588341205 46326960003669177851747)
              ·
                rfl

theorem cell19_456746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 7].length) (baseStart_456746 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_456746 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_456746 prefixEnd_456746 := by exact prefixLift 456746
  have htrace : WordTrace (prefixWord ++ tailWord_456746) baseStart_456746 baseEnd_456746 := by
    simpa [prefixWord, tailWord_456746, baseEnd_456746] using wordTrace_append hprefix tailTrace_456746
  have hstable : (prefixWord ++ tailWord_456746).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456746).length < 2 ^ (prefixWord ++ tailWord_456746).sum := by decide
  have hdescent : baseEnd_456746 < baseStart_456746 := by decide
  rcases family_descends (prefixWord ++ tailWord_456746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456765 : List Nat := [1, 4, 1, 3, 1, 1, 4, 4]
def baseStart_456765 : Nat := 118140960795 + 456765 * 2 ^ 59
def prefixEnd_456765 : Nat := 4983230072969 + 3 ^ 40 * 456765 * 2
def baseEnd_456765 : Nat := 138986661422821119132967

theorem tailTrace_456765 : CollatzResearch.WordTrace tailWord_456765 prefixEnd_456765 138986661422821119132967 := by
  unfold tailWord_456765
  simp only [CollatzResearch.WordTrace]
  refine ⟨16659588190225889096475749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11106392126817259397650499 16659588190225889096475749)
  ·
    refine ⟨3123672785667354205589203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16659588190225889096475749 3123672785667354205589203)
    ·
      refine ⟨4685509178501031308383805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3123672785667354205589203 4685509178501031308383805)
      ·
        refine ⟨1757065941937886740643927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4685509178501031308383805 1757065941937886740643927)
        ·
          refine ⟨2635598912906830110965891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1757065941937886740643927 2635598912906830110965891)
          ·
            refine ⟨3953398369360245166448837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2635598912906830110965891 3953398369360245166448837)
            ·
              refine ⟨741262194255045968709157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3953398369360245166448837 741262194255045968709157)
              ·
                refine ⟨138986661422821119132967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 741262194255045968709157 138986661422821119132967)
                ·
                  rfl

theorem cell19_456765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 4].length) (baseStart_456765 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_456765 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_456765 prefixEnd_456765 := by exact prefixLift 456765
  have htrace : WordTrace (prefixWord ++ tailWord_456765) baseStart_456765 baseEnd_456765 := by
    simpa [prefixWord, tailWord_456765, baseEnd_456765] using wordTrace_append hprefix tailTrace_456765
  have hstable : (prefixWord ++ tailWord_456765).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456765).length < 2 ^ (prefixWord ++ tailWord_456765).sum := by decide
  have hdescent : baseEnd_456765 < baseStart_456765 := by decide
  rcases family_descends (prefixWord ++ tailWord_456765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456767 : List Nat := [1, 1, 2, 2, 3, 1, 3, 6]
def baseStart_456767 : Nat := 118140960795 + 456767 * 2 ^ 59
def prefixEnd_456767 : Nat := 4983230072969 + 3 ^ 40 * 456767 * 2
def baseEnd_456767 : Nat := 138987269992485707088517

theorem tailTrace_456767 : CollatzResearch.WordTrace tailWord_456767 prefixEnd_456767 138987269992485707088517 := by
  unfold tailWord_456767
  simp only [CollatzResearch.WordTrace]
  refine ⟨16659661136218643438048555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11106440757479095625365703 16659661136218643438048555)
  ·
    refine ⟨24989491704327965157072833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16659661136218643438048555 24989491704327965157072833)
    ·
      refine ⟨18742118778245973867804625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24989491704327965157072833 18742118778245973867804625)
      ·
        refine ⟨14056589083684480400853469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18742118778245973867804625 14056589083684480400853469)
        ·
          refine ⟨5271220906381680150320051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14056589083684480400853469 5271220906381680150320051)
          ·
            refine ⟨7906831359572520225480077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5271220906381680150320051 7906831359572520225480077)
            ·
              refine ⟨2965061759839695084555029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7906831359572520225480077 2965061759839695084555029)
              ·
                refine ⟨138987269992485707088517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2965061759839695084555029 138987269992485707088517)
                ·
                  rfl

theorem cell19_456767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 6].length) (baseStart_456767 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_456767 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_456767 prefixEnd_456767 := by exact prefixLift 456767
  have htrace : WordTrace (prefixWord ++ tailWord_456767) baseStart_456767 baseEnd_456767 := by
    simpa [prefixWord, tailWord_456767, baseEnd_456767] using wordTrace_append hprefix tailTrace_456767
  have hstable : (prefixWord ++ tailWord_456767).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456767).length < 2 ^ (prefixWord ++ tailWord_456767).sum := by decide
  have hdescent : baseEnd_456767 < baseStart_456767 := by decide
  rcases family_descends (prefixWord ++ tailWord_456767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456805 : List Nat := [1, 3, 1, 3, 2, 9]
def baseStart_456805 : Nat := 118140960795 + 456805 * 2 ^ 59
def prefixEnd_456805 : Nat := 4983230072969 + 3 ^ 40 * 456805 * 2
def baseEnd_456805 : Nat := 15444314757345875360441

theorem tailTrace_456805 : CollatzResearch.WordTrace tailWord_456805 prefixEnd_456805 15444314757345875360441 := by
  unfold tailWord_456805
  simp only [CollatzResearch.WordTrace]
  refine ⟨16661047110080975927931869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11107364740053983951954579 16661047110080975927931869)
  ·
    refine ⟨6247892666280365972974451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16661047110080975927931869 6247892666280365972974451)
    ·
      refine ⟨9371838999420548959461677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6247892666280365972974451 9371838999420548959461677)
      ·
        refine ⟨3514439624782705859798129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9371838999420548959461677 3514439624782705859798129)
        ·
          refine ⟨2635829718587029394848597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3514439624782705859798129 2635829718587029394848597)
          ·
            refine ⟨15444314757345875360441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2635829718587029394848597 15444314757345875360441)
            ·
              rfl

theorem cell19_456805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 9].length) (baseStart_456805 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_456805 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_456805 prefixEnd_456805 := by exact prefixLift 456805
  have htrace : WordTrace (prefixWord ++ tailWord_456805) baseStart_456805 baseEnd_456805 := by
    simpa [prefixWord, tailWord_456805, baseEnd_456805] using wordTrace_append hprefix tailTrace_456805
  have hstable : (prefixWord ++ tailWord_456805).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456805).length < 2 ^ (prefixWord ++ tailWord_456805).sum := by decide
  have hdescent : baseEnd_456805 < baseStart_456805 := by decide
  rcases family_descends (prefixWord ++ tailWord_456805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456841 : List Nat := [1, 2, 1, 1, 4, 2, 5, 3]
def baseStart_456841 : Nat := 118140960795 + 456841 * 2 ^ 59
def prefixEnd_456841 : Nat := 4983230072969 + 3 ^ 40 * 456841 * 2
def baseEnd_456841 : Nat := 139009787070075461443871

theorem tailTrace_456841 : CollatzResearch.WordTrace tailWord_456841 prefixEnd_456841 139009787070075461443871 := by
  unfold tailWord_456841
  simp only [CollatzResearch.WordTrace]
  refine ⟨16662360137950554076242377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11108240091967036050828251 16662360137950554076242377)
  ·
    refine ⟨12496770103462915557181783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16662360137950554076242377 12496770103462915557181783)
    ·
      refine ⟨18745155155194373335772675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12496770103462915557181783 18745155155194373335772675)
      ·
        refine ⟨28117732732791560003659013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18745155155194373335772675 28117732732791560003659013)
        ·
          refine ⟨5272074887398417500686065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28117732732791560003659013 5272074887398417500686065)
          ·
            refine ⟨3954056165548813125514549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5272074887398417500686065 3954056165548813125514549)
            ·
              refine ⟨370692765520201230516989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3954056165548813125514549 370692765520201230516989)
              ·
                refine ⟨139009787070075461443871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 370692765520201230516989 139009787070075461443871)
                ·
                  rfl

theorem cell19_456841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 5, 3].length) (baseStart_456841 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_456841 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_456841 prefixEnd_456841 := by exact prefixLift 456841
  have htrace : WordTrace (prefixWord ++ tailWord_456841) baseStart_456841 baseEnd_456841 := by
    simpa [prefixWord, tailWord_456841, baseEnd_456841] using wordTrace_append hprefix tailTrace_456841
  have hstable : (prefixWord ++ tailWord_456841).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456841).length < 2 ^ (prefixWord ++ tailWord_456841).sum := by decide
  have hdescent : baseEnd_456841 < baseStart_456841 := by decide
  rcases family_descends (prefixWord ++ tailWord_456841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456894 : List Nat := [4, 2, 1, 1, 4, 2, 2, 3]
def baseStart_456894 : Nat := 118140960795 + 456894 * 2 ^ 59
def prefixEnd_456894 : Nat := 4983230072969 + 3 ^ 40 * 456894 * 2
def baseEnd_456894 : Nat := 139025914166187042265949

theorem tailTrace_456894 : CollatzResearch.WordTrace tailWord_456894 prefixEnd_456894 139025914166187042265949 := by
  unfold tailWord_456894
  simp only [CollatzResearch.WordTrace]
  refine ⟨2083036650844818015990217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11109528804505696085281157 2083036650844818015990217)
  ·
    refine ⟨1562277488133613511992663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2083036650844818015990217 1562277488133613511992663)
    ·
      refine ⟨2343416232200420267988995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1562277488133613511992663 2343416232200420267988995)
      ·
        refine ⟨3515124348300630401983493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2343416232200420267988995 3515124348300630401983493)
        ·
          refine ⟨659085815306368200371905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3515124348300630401983493 659085815306368200371905)
          ·
            refine ⟨494314361479776150278929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 659085815306368200371905 494314361479776150278929)
            ·
              refine ⟨370735771109832112709197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 494314361479776150278929 370735771109832112709197)
              ·
                refine ⟨139025914166187042265949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 370735771109832112709197 139025914166187042265949)
                ·
                  rfl

theorem cell19_456894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 2, 3].length) (baseStart_456894 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_456894 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_456894 prefixEnd_456894 := by exact prefixLift 456894
  have htrace : WordTrace (prefixWord ++ tailWord_456894) baseStart_456894 baseEnd_456894 := by
    simpa [prefixWord, tailWord_456894, baseEnd_456894] using wordTrace_append hprefix tailTrace_456894
  have hstable : (prefixWord ++ tailWord_456894).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456894).length < 2 ^ (prefixWord ++ tailWord_456894).sum := by decide
  have hdescent : baseEnd_456894 < baseStart_456894 := by decide
  rcases family_descends (prefixWord ++ tailWord_456894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456896 : List Nat := [2, 1, 1, 2, 5, 3, 2, 3]
def baseStart_456896 : Nat := 118140960795 + 456896 * 2 ^ 59
def prefixEnd_456896 : Nat := 4983230072969 + 3 ^ 40 * 456896 * 2
def baseEnd_456896 : Nat := 139026522735851630221499

theorem tailTrace_456896 : CollatzResearch.WordTrace tailWord_456896 prefixEnd_456896 139026522735851630221499 := by
  unfold tailWord_456896
  simp only [CollatzResearch.WordTrace]
  refine ⟨8332183076375649234747271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11109577435167532312996361 8332183076375649234747271)
  ·
    refine ⟨12498274614563473852120907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8332183076375649234747271 12498274614563473852120907)
    ·
      refine ⟨18747411921845210778181361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12498274614563473852120907 18747411921845210778181361)
      ·
        refine ⟨14060558941383908083636021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18747411921845210778181361 14060558941383908083636021)
        ·
          refine ⟨1318177400754741382840877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14060558941383908083636021 1318177400754741382840877)
          ·
            refine ⟨494316525283028018565329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1318177400754741382840877 494316525283028018565329)
            ·
              refine ⟨370737393962271013923997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 494316525283028018565329 370737393962271013923997)
              ·
                refine ⟨139026522735851630221499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 370737393962271013923997 139026522735851630221499)
                ·
                  rfl

theorem cell19_456896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 2, 3].length) (baseStart_456896 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_456896 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_456896 prefixEnd_456896 := by exact prefixLift 456896
  have htrace : WordTrace (prefixWord ++ tailWord_456896) baseStart_456896 baseEnd_456896 := by
    simpa [prefixWord, tailWord_456896, baseEnd_456896] using wordTrace_append hprefix tailTrace_456896
  have hstable : (prefixWord ++ tailWord_456896).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456896).length < 2 ^ (prefixWord ++ tailWord_456896).sum := by decide
  have hdescent : baseEnd_456896 < baseStart_456896 := by decide
  rcases family_descends (prefixWord ++ tailWord_456896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456930 : List Nat := [3, 3, 4, 1, 1, 1, 2, 4]
def baseStart_456930 : Nat := 118140960795 + 456930 * 2 ^ 59
def prefixEnd_456930 : Nat := 4983230072969 + 3 ^ 40 * 456930 * 2
def baseEnd_456930 : Nat := 139036868420149625465851

theorem tailTrace_456930 : CollatzResearch.WordTrace tailWord_456930 prefixEnd_456930 139036868420149625465851 := by
  unfold tailWord_456930
  simp only [CollatzResearch.WordTrace]
  refine ⟨4166401558657030569058061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11110404156418748184154829 4166401558657030569058061)
  ·
    refine ⟨1562400584496386463396773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4166401558657030569058061 1562400584496386463396773)
    ·
      refine ⟨292950109593072461886895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1562400584496386463396773 292950109593072461886895)
      ·
        refine ⟨439425164389608692830343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292950109593072461886895 439425164389608692830343)
        ·
          refine ⟨659137746584413039245515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 439425164389608692830343 659137746584413039245515)
          ·
            refine ⟨988706619876619558868273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 659137746584413039245515 988706619876619558868273)
            ·
              refine ⟨741529964907464669151205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 988706619876619558868273 741529964907464669151205)
              ·
                refine ⟨139036868420149625465851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 741529964907464669151205 139036868420149625465851)
                ·
                  rfl

theorem cell19_456930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 4].length) (baseStart_456930 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_456930 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_456930 prefixEnd_456930 := by exact prefixLift 456930
  have htrace : WordTrace (prefixWord ++ tailWord_456930) baseStart_456930 baseEnd_456930 := by
    simpa [prefixWord, tailWord_456930, baseEnd_456930] using wordTrace_append hprefix tailTrace_456930
  have hstable : (prefixWord ++ tailWord_456930).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456930).length < 2 ^ (prefixWord ++ tailWord_456930).sum := by decide
  have hdescent : baseEnd_456930 < baseStart_456930 := by decide
  rcases family_descends (prefixWord ++ tailWord_456930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456936 : List Nat := [2, 1, 4, 1, 2, 3, 2, 4]
def baseStart_456936 : Nat := 118140960795 + 456936 * 2 ^ 59
def prefixEnd_456936 : Nat := 4983230072969 + 3 ^ 40 * 456936 * 2
def baseEnd_456936 : Nat := 139038694129143389332501

theorem tailTrace_456936 : CollatzResearch.WordTrace tailWord_456936 prefixEnd_456936 139038694129143389332501 := by
  unfold tailWord_456936
  simp only [CollatzResearch.WordTrace]
  refine ⟨8332912536303192650475331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11110550048404256867300441 8332912536303192650475331)
  ·
    refine ⟨12499368804454788975712997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8332912536303192650475331 12499368804454788975712997)
    ·
      refine ⟨2343631650835272932946187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12499368804454788975712997 2343631650835272932946187)
      ·
        refine ⟨3515447476252909399419281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2343631650835272932946187 3515447476252909399419281)
        ·
          refine ⟨2636585607189682049564461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3515447476252909399419281 2636585607189682049564461)
          ·
            refine ⟨988719602696130768586673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2636585607189682049564461 988719602696130768586673)
            ·
              refine ⟨741539702022098076440005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 988719602696130768586673 741539702022098076440005)
              ·
                refine ⟨139038694129143389332501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 741539702022098076440005 139038694129143389332501)
                ·
                  rfl

theorem cell19_456936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 4].length) (baseStart_456936 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_456936 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_456936 prefixEnd_456936 := by exact prefixLift 456936
  have htrace : WordTrace (prefixWord ++ tailWord_456936) baseStart_456936 baseEnd_456936 := by
    simpa [prefixWord, tailWord_456936, baseEnd_456936] using wordTrace_append hprefix tailTrace_456936
  have hstable : (prefixWord ++ tailWord_456936).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456936).length < 2 ^ (prefixWord ++ tailWord_456936).sum := by decide
  have hdescent : baseEnd_456936 < baseStart_456936 := by decide
  rcases family_descends (prefixWord ++ tailWord_456936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_456989 : List Nat := [1, 4, 2, 3, 3, 1, 1, 4]
def baseStart_456989 : Nat := 118140960795 + 456989 * 2 ^ 59
def prefixEnd_456989 : Nat := 4983230072969 + 3 ^ 40 * 456989 * 2
def baseEnd_456989 : Nat := 139054821225254970154579

theorem tailTrace_456989 : CollatzResearch.WordTrace tailWord_456989 prefixEnd_456989 139054821225254970154579 := by
  unfold tailWord_456989
  simp only [CollatzResearch.WordTrace]
  refine ⟨16667758141414375352630021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11111838760942916901753347 16667758141414375352630021)
  ·
    refine ⟨3125204651515195378618129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16667758141414375352630021 3125204651515195378618129)
    ·
      refine ⟨2343903488636396533963597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3125204651515195378618129 2343903488636396533963597)
      ·
        refine ⟨878963808238648700236349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2343903488636396533963597 878963808238648700236349)
        ·
          refine ⟨329611428089493262588631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 878963808238648700236349 329611428089493262588631)
          ·
            refine ⟨494417142134239893882947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 329611428089493262588631 494417142134239893882947)
            ·
              refine ⟨741625713201359840824421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 494417142134239893882947 741625713201359840824421)
              ·
                refine ⟨139054821225254970154579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 741625713201359840824421 139054821225254970154579)
                ·
                  rfl

theorem cell19_456989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 4].length) (baseStart_456989 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_456989 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_456989 prefixEnd_456989 := by exact prefixLift 456989
  have htrace : WordTrace (prefixWord ++ tailWord_456989) baseStart_456989 baseEnd_456989 := by
    simpa [prefixWord, tailWord_456989, baseEnd_456989] using wordTrace_append hprefix tailTrace_456989
  have hstable : (prefixWord ++ tailWord_456989).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_456989).length < 2 ^ (prefixWord ++ tailWord_456989).sum := by decide
  have hdescent : baseEnd_456989 < baseStart_456989 := by decide
  rcases family_descends (prefixWord ++ tailWord_456989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457010 : List Nat := [3, 2, 1, 1, 5, 1, 3, 3]
def baseStart_457010 : Nat := 118140960795 + 457010 * 2 ^ 59
def prefixEnd_457010 : Nat := 4983230072969 + 3 ^ 40 * 457010 * 2
def baseEnd_457010 : Nat := 139061211206733143687855

theorem tailTrace_457010 : CollatzResearch.WordTrace tailWord_457010 prefixEnd_457010 139061211206733143687855 := by
  unfold tailWord_457010
  simp only [CollatzResearch.WordTrace]
  refine ⟨4167131018584573984786121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11112349382892197292762989 4167131018584573984786121)
  ·
    refine ⟨3125348263938430488589591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4167131018584573984786121 3125348263938430488589591)
    ·
      refine ⟨4688022395907645732884387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3125348263938430488589591 4688022395907645732884387)
      ·
        refine ⟨7032033593861468599326581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4688022395907645732884387 7032033593861468599326581)
        ·
          refine ⟨659253149424512681186867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7032033593861468599326581 659253149424512681186867)
          ·
            refine ⟨988879724136769021780301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 659253149424512681186867 988879724136769021780301)
            ·
              refine ⟨370829896551288383167613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 988879724136769021780301 370829896551288383167613)
              ·
                refine ⟨139061211206733143687855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 370829896551288383167613 139061211206733143687855)
                ·
                  rfl

theorem cell19_457010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 3, 3].length) (baseStart_457010 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_457010 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_457010 prefixEnd_457010 := by exact prefixLift 457010
  have htrace : WordTrace (prefixWord ++ tailWord_457010) baseStart_457010 baseEnd_457010 := by
    simpa [prefixWord, tailWord_457010, baseEnd_457010] using wordTrace_append hprefix tailTrace_457010
  have hstable : (prefixWord ++ tailWord_457010).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457010).length < 2 ^ (prefixWord ++ tailWord_457010).sum := by decide
  have hdescent : baseEnd_457010 < baseStart_457010 := by decide
  rcases family_descends (prefixWord ++ tailWord_457010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457183 : List Nat := [1, 1, 2, 3, 3, 3, 3, 3]
def baseStart_457183 : Nat := 118140960795 + 457183 * 2 ^ 59
def prefixEnd_457183 : Nat := 4983230072969 + 3 ^ 40 * 457183 * 2
def baseEnd_457183 : Nat := 139113852482720001842939

theorem tailTrace_457183 : CollatzResearch.WordTrace tailWord_457183 prefixEnd_457183 139113852482720001842939 := by
  unfold tailWord_457183
  simp only [CollatzResearch.WordTrace]
  refine ⟨16674833902711546485192203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11116555935141030990128135 16674833902711546485192203)
  ·
    refine ⟨25012250854067319727788305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16674833902711546485192203 25012250854067319727788305)
    ·
      refine ⟨18759188140550489795841229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25012250854067319727788305 18759188140550489795841229)
      ·
        refine ⟨7034695552706433673440461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18759188140550489795841229 7034695552706433673440461)
        ·
          refine ⟨2638010832264912627540173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7034695552706433673440461 2638010832264912627540173)
          ·
            refine ⟨989254062099342235327565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2638010832264912627540173 989254062099342235327565)
            ·
              refine ⟨370970273287253338247837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 989254062099342235327565 370970273287253338247837)
              ·
                refine ⟨139113852482720001842939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 370970273287253338247837 139113852482720001842939)
                ·
                  rfl

theorem cell19_457183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 3, 3].length) (baseStart_457183 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_457183 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_457183 prefixEnd_457183 := by exact prefixLift 457183
  have htrace : WordTrace (prefixWord ++ tailWord_457183) baseStart_457183 baseEnd_457183 := by
    simpa [prefixWord, tailWord_457183, baseEnd_457183] using wordTrace_append hprefix tailTrace_457183
  have hstable : (prefixWord ++ tailWord_457183).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457183).length < 2 ^ (prefixWord ++ tailWord_457183).sum := by decide
  have hdescent : baseEnd_457183 < baseStart_457183 := by decide
  rcases family_descends (prefixWord ++ tailWord_457183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457202 : List Nat := [3, 2, 1, 4, 2, 1, 6]
def baseStart_457202 : Nat := 118140960795 + 457202 * 2 ^ 59
def prefixEnd_457202 : Nat := 4983230072969 + 3 ^ 40 * 457202 * 2
def baseEnd_457202 : Nat := 46373211298177862473555

theorem tailTrace_457202 : CollatzResearch.WordTrace tailWord_457202 prefixEnd_457202 46373211298177862473555 := by
  unfold tailWord_457202
  simp only [CollatzResearch.WordTrace]
  refine ⟨4168881722410678182533465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11117017926428475153422573 4168881722410678182533465)
  ·
    refine ⟨3126661291808008636900099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4168881722410678182533465 3126661291808008636900099)
    ·
      refine ⟨4689991937712012955350149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3126661291808008636900099 4689991937712012955350149)
      ·
        refine ⟨879373488321002429128153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4689991937712012955350149 879373488321002429128153)
        ·
          refine ⟨659530116240751821846115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 879373488321002429128153 659530116240751821846115)
          ·
            refine ⟨989295174361127732769173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 659530116240751821846115 989295174361127732769173)
            ·
              refine ⟨46373211298177862473555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 989295174361127732769173 46373211298177862473555)
              ·
                rfl

theorem cell19_457202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 6].length) (baseStart_457202 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_457202 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_457202 prefixEnd_457202 := by exact prefixLift 457202
  have htrace : WordTrace (prefixWord ++ tailWord_457202) baseStart_457202 baseEnd_457202 := by
    simpa [prefixWord, tailWord_457202, baseEnd_457202] using wordTrace_append hprefix tailTrace_457202
  have hstable : (prefixWord ++ tailWord_457202).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457202).length < 2 ^ (prefixWord ++ tailWord_457202).sum := by decide
  have hdescent : baseEnd_457202 < baseStart_457202 := by decide
  rcases family_descends (prefixWord ++ tailWord_457202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457236 : List Nat := [2, 4, 3, 1, 1, 3, 2, 3]
def baseStart_457236 : Nat := 118140960795 + 457236 * 2 ^ 59
def prefixEnd_457236 : Nat := 4983230072969 + 3 ^ 40 * 457236 * 2
def baseEnd_457236 : Nat := 139129979578831582665017

theorem tailTrace_457236 : CollatzResearch.WordTrace tailWord_457236 prefixEnd_457236 139129979578831582665017 := by
  unfold tailWord_457236
  simp only [CollatzResearch.WordTrace]
  refine ⟨8338383485759768268435781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11117844647679691024581041 8338383485759768268435781)
  ·
    refine ⟨1563446903579956550331709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8338383485759768268435781 1563446903579956550331709)
    ·
      refine ⟨586292588842483706374391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1563446903579956550331709 586292588842483706374391)
      ·
        refine ⟨879438883263725559561587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 586292588842483706374391 879438883263725559561587)
        ·
          refine ⟨1319158324895588339342381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 879438883263725559561587 1319158324895588339342381)
          ·
            refine ⟨494684371835845627253393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1319158324895588339342381 494684371835845627253393)
            ·
              refine ⟨371013278876884220440045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 494684371835845627253393 371013278876884220440045)
              ·
                refine ⟨139129979578831582665017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 371013278876884220440045 139129979578831582665017)
                ·
                  rfl

theorem cell19_457236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 2, 3].length) (baseStart_457236 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_457236 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_457236 prefixEnd_457236 := by exact prefixLift 457236
  have htrace : WordTrace (prefixWord ++ tailWord_457236) baseStart_457236 baseEnd_457236 := by
    simpa [prefixWord, tailWord_457236, baseEnd_457236] using wordTrace_append hprefix tailTrace_457236
  have hstable : (prefixWord ++ tailWord_457236).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457236).length < 2 ^ (prefixWord ++ tailWord_457236).sum := by decide
  have hdescent : baseEnd_457236 < baseStart_457236 := by decide
  rcases family_descends (prefixWord ++ tailWord_457236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457240 : List Nat := [2, 1, 2, 3, 3, 1, 4, 3]
def baseStart_457240 : Nat := 118140960795 + 457240 * 2 ^ 59
def prefixEnd_457240 : Nat := 4983230072969 + 3 ^ 40 * 457240 * 2
def baseEnd_457240 : Nat := 139131196718160758576117

theorem tailTrace_457240 : CollatzResearch.WordTrace tailWord_457240 prefixEnd_457240 139131196718160758576117 := by
  unfold tailWord_457240
  simp only [CollatzResearch.WordTrace]
  refine ⟨8338456431752522610008587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11117941909003363480011449 8338456431752522610008587)
  ·
    refine ⟨12507684647628783915012881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8338456431752522610008587 12507684647628783915012881)
    ·
      refine ⟨9380763485721587936259661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12507684647628783915012881 9380763485721587936259661)
      ·
        refine ⟨3517786307145595476097373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9380763485721587936259661 3517786307145595476097373)
        ·
          refine ⟨1319169865179598303536515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3517786307145595476097373 1319169865179598303536515)
          ·
            refine ⟨1978754797769397455304773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1319169865179598303536515 1978754797769397455304773)
            ·
              refine ⟨371016524581762022869645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1978754797769397455304773 371016524581762022869645)
              ·
                refine ⟨139131196718160758576117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 371016524581762022869645 139131196718160758576117)
                ·
                  rfl

theorem cell19_457240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 4, 3].length) (baseStart_457240 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_457240 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_457240 prefixEnd_457240 := by exact prefixLift 457240
  have htrace : WordTrace (prefixWord ++ tailWord_457240) baseStart_457240 baseEnd_457240 := by
    simpa [prefixWord, tailWord_457240, baseEnd_457240] using wordTrace_append hprefix tailTrace_457240
  have hstable : (prefixWord ++ tailWord_457240).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457240).length < 2 ^ (prefixWord ++ tailWord_457240).sum := by decide
  have hdescent : baseEnd_457240 < baseStart_457240 := by decide
  rcases family_descends (prefixWord ++ tailWord_457240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457255 : List Nat := [1, 1, 7, 2, 2, 1, 5]
def baseStart_457255 : Nat := 118140960795 + 457255 * 2 ^ 59
def prefixEnd_457255 : Nat := 4983230072969 + 3 ^ 40 * 457255 * 2
def baseEnd_457255 : Nat := 46378586996881722747581

theorem tailTrace_457255 : CollatzResearch.WordTrace tailWord_457255 prefixEnd_457255 46378586996881722747581 := by
  unfold tailWord_457255
  simp only [CollatzResearch.WordTrace]
  refine ⟨16677459958450702781813219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11118306638967135187875479 16677459958450702781813219)
  ·
    refine ⟨25016189937676054172719829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16677459958450702781813219 25016189937676054172719829)
    ·
      refine ⟨586316951664282519673121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 25016189937676054172719829 586316951664282519673121)
      ·
        refine ⟨439737713748211889754841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 586316951664282519673121 439737713748211889754841)
        ·
          refine ⟨329803285311158917316131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 439737713748211889754841 329803285311158917316131)
          ·
            refine ⟨494704927966738375974197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 329803285311158917316131 494704927966738375974197)
            ·
              refine ⟨46378586996881722747581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 494704927966738375974197 46378586996881722747581)
              ·
                rfl

theorem cell19_457255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 5].length) (baseStart_457255 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_457255 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_457255 prefixEnd_457255 := by exact prefixLift 457255
  have htrace : WordTrace (prefixWord ++ tailWord_457255) baseStart_457255 baseEnd_457255 := by
    simpa [prefixWord, tailWord_457255, baseEnd_457255] using wordTrace_append hprefix tailTrace_457255
  have hstable : (prefixWord ++ tailWord_457255).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457255).length < 2 ^ (prefixWord ++ tailWord_457255).sum := by decide
  have hdescent : baseEnd_457255 < baseStart_457255 := by decide
  rcases family_descends (prefixWord ++ tailWord_457255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457314 : List Nat := [3, 3, 2, 3, 2, 6]
def baseStart_457314 : Nat := 118140960795 + 457314 * 2 ^ 59
def prefixEnd_457314 : Nat := 4983230072969 + 3 ^ 40 * 457314 * 2
def baseEnd_457314 : Nat := 15461523755083390325719

theorem tailTrace_457314 : CollatzResearch.WordTrace tailWord_457314 prefixEnd_457314 15461523755083390325719 := by
  unfold tailWord_457314
  simp only [CollatzResearch.WordTrace]
  refine ⟨4169902966309238964552749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11119741243491303905473997 4169902966309238964552749)
  ·
    refine ⟨1563713612365964611707281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4169902966309238964552749 1563713612365964611707281)
    ·
      refine ⟨1172785209274473458780461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1563713612365964611707281 1172785209274473458780461)
      ·
        refine ⟨439794453477927547042673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1172785209274473458780461 439794453477927547042673)
        ·
          refine ⟨329845840108445660282005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 439794453477927547042673 329845840108445660282005)
          ·
            refine ⟨15461523755083390325719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 329845840108445660282005 15461523755083390325719)
            ·
              rfl

theorem cell19_457314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 6].length) (baseStart_457314 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_457314 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_457314 prefixEnd_457314 := by exact prefixLift 457314
  have htrace : WordTrace (prefixWord ++ tailWord_457314) baseStart_457314 baseEnd_457314 := by
    simpa [prefixWord, tailWord_457314, baseEnd_457314] using wordTrace_append hprefix tailTrace_457314
  have hstable : (prefixWord ++ tailWord_457314).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457314).length < 2 ^ (prefixWord ++ tailWord_457314).sum := by decide
  have hdescent : baseEnd_457314 < baseStart_457314 := by decide
  rcases family_descends (prefixWord ++ tailWord_457314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457333 : List Nat := [1, 3, 4, 2, 2, 2, 1, 4]
def baseStart_457333 : Nat := 118140960795 + 457333 * 2 ^ 59
def prefixEnd_457333 : Nat := 4983230072969 + 3 ^ 40 * 457333 * 2
def baseEnd_457333 : Nat := 139159495207564098509197

theorem tailTrace_457333 : CollatzResearch.WordTrace tailWord_457333 prefixEnd_457333 139159495207564098509197 := by
  unfold tailWord_457333
  simp only [CollatzResearch.WordTrace]
  refine ⟨16680304852168122103152653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11120203234778748068768435 16680304852168122103152653)
  ·
    refine ⟨6255114319563045788682245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16680304852168122103152653 6255114319563045788682245)
    ·
      refine ⟨1172833934918071085377921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6255114319563045788682245 1172833934918071085377921)
      ·
        refine ⟨879625451188553314033441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1172833934918071085377921 879625451188553314033441)
        ·
          refine ⟨659719088391414985525081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 879625451188553314033441 659719088391414985525081)
          ·
            refine ⟨494789316293561239143811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 659719088391414985525081 494789316293561239143811)
            ·
              refine ⟨742183974440341858715717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 494789316293561239143811 742183974440341858715717)
              ·
                refine ⟨139159495207564098509197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 742183974440341858715717 139159495207564098509197)
                ·
                  rfl

theorem cell19_457333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 4].length) (baseStart_457333 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_457333 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_457333 prefixEnd_457333 := by exact prefixLift 457333
  have htrace : WordTrace (prefixWord ++ tailWord_457333) baseStart_457333 baseEnd_457333 := by
    simpa [prefixWord, tailWord_457333, baseEnd_457333] using wordTrace_append hprefix tailTrace_457333
  have hstable : (prefixWord ++ tailWord_457333).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457333).length < 2 ^ (prefixWord ++ tailWord_457333).sum := by decide
  have hdescent : baseEnd_457333 < baseStart_457333 := by decide
  rcases family_descends (prefixWord ++ tailWord_457333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457337 : List Nat := [1, 2, 1, 3, 3, 2, 3, 4]
def baseStart_457337 : Nat := 118140960795 + 457337 * 2 ^ 59
def prefixEnd_457337 : Nat := 4983230072969 + 3 ^ 40 * 457337 * 2
def baseEnd_457337 : Nat := 139160712346893274420297

theorem tailTrace_457337 : CollatzResearch.WordTrace tailWord_457337 prefixEnd_457337 139160712346893274420297 := by
  unfold tailWord_457337
  simp only [CollatzResearch.WordTrace]
  refine ⟨16680450744153630786298265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11120300496102420524198843 16680450744153630786298265)
  ·
    refine ⟨12510338058115223089723699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16680450744153630786298265 12510338058115223089723699)
    ·
      refine ⟨18765507087172834634585549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12510338058115223089723699 18765507087172834634585549)
      ·
        refine ⟨7037065157689812987969581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18765507087172834634585549 7037065157689812987969581)
        ·
          refine ⟨2638899434133679870488593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7037065157689812987969581 2638899434133679870488593)
          ·
            refine ⟨1979174575600259902866445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2638899434133679870488593 1979174575600259902866445)
            ·
              refine ⟨742190465850097463574917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1979174575600259902866445 742190465850097463574917)
              ·
                refine ⟨139160712346893274420297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 742190465850097463574917 139160712346893274420297)
                ·
                  rfl

theorem cell19_457337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 4].length) (baseStart_457337 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_457337 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_457337 prefixEnd_457337 := by exact prefixLift 457337
  have htrace : WordTrace (prefixWord ++ tailWord_457337) baseStart_457337 baseEnd_457337 := by
    simpa [prefixWord, tailWord_457337, baseEnd_457337] using wordTrace_append hprefix tailTrace_457337
  have hstable : (prefixWord ++ tailWord_457337).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457337).length < 2 ^ (prefixWord ++ tailWord_457337).sum := by decide
  have hdescent : baseEnd_457337 < baseStart_457337 := by decide
  rcases family_descends (prefixWord ++ tailWord_457337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457339 : List Nat := [1, 1, 1, 1, 1, 4, 2, 8]
def baseStart_457339 : Nat := 118140960795 + 457339 * 2 ^ 59
def prefixEnd_457339 : Nat := 4983230072969 + 3 ^ 40 * 457339 * 2
def baseEnd_457339 : Nat := 139161320916557862375847

theorem tailTrace_457339 : CollatzResearch.WordTrace tailWord_457339 prefixEnd_457339 139161320916557862375847 := by
  unfold tailWord_457339
  simp only [CollatzResearch.WordTrace]
  refine ⟨16680523690146385127871071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11120349126764256751914047 16680523690146385127871071)
  ·
    refine ⟨25020785535219577691806607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16680523690146385127871071 25020785535219577691806607)
    ·
      refine ⟨37531178302829366537709911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25020785535219577691806607 37531178302829366537709911)
      ·
        refine ⟨56296767454244049806564867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37531178302829366537709911 56296767454244049806564867)
        ·
          refine ⟨84445151181366074709847301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56296767454244049806564867 84445151181366074709847301)
          ·
            refine ⟨15833465846506139008096369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84445151181366074709847301 15833465846506139008096369)
            ·
              refine ⟨11875099384879604256072277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15833465846506139008096369 11875099384879604256072277)
              ·
                refine ⟨139161320916557862375847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11875099384879604256072277 139161320916557862375847)
                ·
                  rfl

theorem cell19_457339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 8].length) (baseStart_457339 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_457339 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_457339 prefixEnd_457339 := by exact prefixLift 457339
  have htrace : WordTrace (prefixWord ++ tailWord_457339) baseStart_457339 baseEnd_457339 := by
    simpa [prefixWord, tailWord_457339, baseEnd_457339] using wordTrace_append hprefix tailTrace_457339
  have hstable : (prefixWord ++ tailWord_457339).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457339).length < 2 ^ (prefixWord ++ tailWord_457339).sum := by decide
  have hdescent : baseEnd_457339 < baseStart_457339 := by decide
  rcases family_descends (prefixWord ++ tailWord_457339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457409 : List Nat := [1, 2, 6, 2, 1, 1, 1, 5]
def baseStart_457409 : Nat := 118140960795 + 457409 * 2 ^ 59
def prefixEnd_457409 : Nat := 4983230072969 + 3 ^ 40 * 457409 * 2
def baseEnd_457409 : Nat := 139182620854818440820101

theorem tailTrace_457409 : CollatzResearch.WordTrace tailWord_457409 prefixEnd_457409 139182620854818440820101 := by
  unfold tailWord_457409
  simp only [CollatzResearch.WordTrace]
  refine ⟨16683076799892787082919281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11122051199928524721946187 16683076799892787082919281)
  ·
    refine ⟨12512307599919590312189461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16683076799892787082919281 12512307599919590312189461)
    ·
      refine ⟨586514418746230795883881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 12512307599919590312189461 586514418746230795883881)
      ·
        refine ⟨439885814059673096912911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 586514418746230795883881 439885814059673096912911)
        ·
          refine ⟨659828721089509645369367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 439885814059673096912911 659828721089509645369367)
          ·
            refine ⟨989743081634264468054051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 659828721089509645369367 989743081634264468054051)
            ·
              refine ⟨1484614622451396702081077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 989743081634264468054051 1484614622451396702081077)
              ·
                refine ⟨139182620854818440820101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1484614622451396702081077 139182620854818440820101)
                ·
                  rfl

theorem cell19_457409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 5].length) (baseStart_457409 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_457409 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_457409 prefixEnd_457409 := by exact prefixLift 457409
  have htrace : WordTrace (prefixWord ++ tailWord_457409) baseStart_457409 baseEnd_457409 := by
    simpa [prefixWord, tailWord_457409, baseEnd_457409] using wordTrace_append hprefix tailTrace_457409
  have hstable : (prefixWord ++ tailWord_457409).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457409).length < 2 ^ (prefixWord ++ tailWord_457409).sum := by decide
  have hdescent : baseEnd_457409 < baseStart_457409 := by decide
  rcases family_descends (prefixWord ++ tailWord_457409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457428 : List Nat := [2, 4, 1, 3, 3, 1, 5]
def baseStart_457428 : Nat := 118140960795 + 457428 * 2 ^ 59
def prefixEnd_457428 : Nat := 4983230072969 + 3 ^ 40 * 457428 * 2
def baseEnd_457428 : Nat := 46396134088877342132609

theorem tailTrace_457428 : CollatzResearch.WordTrace tailWord_457428 prefixEnd_457428 46396134088877342132609 := by
  unfold tailWord_457428
  simp only [CollatzResearch.WordTrace]
  refine ⟨8341884893411976663930469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11122513191215968885240625 8341884893411976663930469)
  ·
    refine ⟨1564103417514745624486963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8341884893411976663930469 1564103417514745624486963)
    ·
      refine ⟨2346155126272118436730445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1564103417514745624486963 2346155126272118436730445)
      ·
        refine ⟨879808172352044413773917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2346155126272118436730445 879808172352044413773917)
        ·
          refine ⟨329928064632016655165219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 879808172352044413773917 329928064632016655165219)
          ·
            refine ⟨494892096948024982747829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 329928064632016655165219 494892096948024982747829)
            ·
              refine ⟨46396134088877342132609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 494892096948024982747829 46396134088877342132609)
              ·
                rfl

theorem cell19_457428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 5].length) (baseStart_457428 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_457428 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_457428 prefixEnd_457428 := by exact prefixLift 457428
  have htrace : WordTrace (prefixWord ++ tailWord_457428) baseStart_457428 baseEnd_457428 := by
    simpa [prefixWord, tailWord_457428, baseEnd_457428] using wordTrace_append hprefix tailTrace_457428
  have hstable : (prefixWord ++ tailWord_457428).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457428).length < 2 ^ (prefixWord ++ tailWord_457428).sum := by decide
  have hdescent : baseEnd_457428 < baseStart_457428 := by decide
  rcases family_descends (prefixWord ++ tailWord_457428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457432 : List Nat := [2, 1, 2, 2, 3, 4, 5]
def baseStart_457432 : Nat := 118140960795 + 457432 * 2 ^ 59
def prefixEnd_457432 : Nat := 4983230072969 + 3 ^ 40 * 457432 * 2
def baseEnd_457432 : Nat := 46396539801987067436309

theorem tailTrace_457432 : CollatzResearch.WordTrace tailWord_457432 prefixEnd_457432 46396539801987067436309 := by
  unfold tailWord_457432
  simp only [CollatzResearch.WordTrace]
  refine ⟨8341957839404731005503275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11122610452539641340671033 8341957839404731005503275)
  ·
    refine ⟨12512936759107096508254913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8341957839404731005503275 12512936759107096508254913)
    ·
      refine ⟨9384702569330322381191185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12512936759107096508254913 9384702569330322381191185)
      ·
        refine ⟨7038526926997741785893389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9384702569330322381191185 7038526926997741785893389)
        ·
          refine ⟨2639447597624153169710021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7038526926997741785893389 2639447597624153169710021)
          ·
            refine ⟨494896424554528719320629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2639447597624153169710021 494896424554528719320629)
            ·
              refine ⟨46396539801987067436309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 494896424554528719320629 46396539801987067436309)
              ·
                rfl

theorem cell19_457432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 5].length) (baseStart_457432 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_457432 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_457432 prefixEnd_457432 := by exact prefixLift 457432
  have htrace : WordTrace (prefixWord ++ tailWord_457432) baseStart_457432 baseEnd_457432 := by
    simpa [prefixWord, tailWord_457432, baseEnd_457432] using wordTrace_append hprefix tailTrace_457432
  have hstable : (prefixWord ++ tailWord_457432).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457432).length < 2 ^ (prefixWord ++ tailWord_457432).sum := by decide
  have hdescent : baseEnd_457432 < baseStart_457432 := by decide
  rcases family_descends (prefixWord ++ tailWord_457432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457506 : List Nat := [3, 3, 1, 1, 2, 4, 1, 4]
def baseStart_457506 : Nat := 118140960795 + 457506 * 2 ^ 59
def prefixEnd_457506 : Nat := 4983230072969 + 3 ^ 40 * 457506 * 2
def baseEnd_457506 : Nat := 139212136483550956664281

theorem tailTrace_457506 : CollatzResearch.WordTrace tailWord_457506 prefixEnd_457506 139212136483550956664281 := by
  unfold tailWord_457506
  simp only [CollatzResearch.WordTrace]
  refine ⟨4171653670135343162300093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11124409787027581766133581 4171653670135343162300093)
  ·
    refine ⟨1564370126300753685862535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4171653670135343162300093 1564370126300753685862535)
    ·
      refine ⟨2346555189451130528793803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1564370126300753685862535 2346555189451130528793803)
      ·
        refine ⟨3519832784176695793190705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2346555189451130528793803 3519832784176695793190705)
        ·
          refine ⟨2639874588132521844893029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3519832784176695793190705 2639874588132521844893029)
          ·
            refine ⟨494976485274847845917443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2639874588132521844893029 494976485274847845917443)
            ·
              refine ⟨742464727912271768876165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 494976485274847845917443 742464727912271768876165)
              ·
                refine ⟨139212136483550956664281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 742464727912271768876165 139212136483550956664281)
                ·
                  rfl

theorem cell19_457506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 4].length) (baseStart_457506 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_457506 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_457506 prefixEnd_457506 := by exact prefixLift 457506
  have htrace : WordTrace (prefixWord ++ tailWord_457506) baseStart_457506 baseEnd_457506 := by
    simpa [prefixWord, tailWord_457506, baseEnd_457506] using wordTrace_append hprefix tailTrace_457506
  have hstable : (prefixWord ++ tailWord_457506).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457506).length < 2 ^ (prefixWord ++ tailWord_457506).sum := by decide
  have hdescent : baseEnd_457506 < baseStart_457506 := by decide
  rcases family_descends (prefixWord ++ tailWord_457506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457525 : List Nat := [1, 3, 3, 1, 3, 2, 3, 3]
def baseStart_457525 : Nat := 118140960795 + 457525 * 2 ^ 59
def prefixEnd_457525 : Nat := 4983230072969 + 3 ^ 40 * 457525 * 2
def baseEnd_457525 : Nat := 139217917895364542242007

theorem tailTrace_457525 : CollatzResearch.WordTrace tailWord_457525 prefixEnd_457525 139217917895364542242007 := by
  unfold tailWord_457525
  simp only [CollatzResearch.WordTrace]
  refine ⟨16687307667472538894142029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11124871778315025929428019 16687307667472538894142029)
  ·
    refine ⟨6257740375302202085303261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16687307667472538894142029 6257740375302202085303261)
    ·
      refine ⟨2346652640738325781988723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6257740375302202085303261 2346652640738325781988723)
      ·
        refine ⟨3519978961107488672983085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2346652640738325781988723 3519978961107488672983085)
        ·
          refine ⟨1319992110415308252368657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3519978961107488672983085 1319992110415308252368657)
          ·
            refine ⟨989994082811481189276493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1319992110415308252368657 989994082811481189276493)
            ·
              refine ⟨371247781054305445978685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 989994082811481189276493 371247781054305445978685)
              ·
                refine ⟨139217917895364542242007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 371247781054305445978685 139217917895364542242007)
                ·
                  rfl

theorem cell19_457525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 3, 3].length) (baseStart_457525 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_457525 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_457525 prefixEnd_457525 := by exact prefixLift 457525
  have htrace : WordTrace (prefixWord ++ tailWord_457525) baseStart_457525 baseEnd_457525 := by
    simpa [prefixWord, tailWord_457525, baseEnd_457525] using wordTrace_append hprefix tailTrace_457525
  have hstable : (prefixWord ++ tailWord_457525).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457525).length < 2 ^ (prefixWord ++ tailWord_457525).sum := by decide
  have hdescent : baseEnd_457525 < baseStart_457525 := by decide
  rcases family_descends (prefixWord ++ tailWord_457525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457527 : List Nat := [1, 1, 3, 1, 2, 1, 7, 3]
def baseStart_457527 : Nat := 118140960795 + 457527 * 2 ^ 59
def prefixEnd_457527 : Nat := 4983230072969 + 3 ^ 40 * 457527 * 2
def baseEnd_457527 : Nat := 139218526465029130197557

theorem tailTrace_457527 : CollatzResearch.WordTrace tailWord_457527 prefixEnd_457527 139218526465029130197557 := by
  unfold tailWord_457527
  simp only [CollatzResearch.WordTrace]
  refine ⟨16687380613465293235714835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11124920408976862157143223 16687380613465293235714835)
  ·
    refine ⟨25031070920197939853572253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16687380613465293235714835 25031070920197939853572253)
    ·
      refine ⟨9386651595074227445089595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25031070920197939853572253 9386651595074227445089595)
      ·
        refine ⟨14079977392611341167634393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9386651595074227445089595 14079977392611341167634393)
        ·
          refine ⟨10559983044458505875725795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14079977392611341167634393 10559983044458505875725795)
          ·
            refine ⟨15839974566687758813588693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10559983044458505875725795 15839974566687758813588693)
            ·
              refine ⟨371249403906744347193485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 15839974566687758813588693 371249403906744347193485)
              ·
                refine ⟨139218526465029130197557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 371249403906744347193485 139218526465029130197557)
                ·
                  rfl

theorem cell19_457527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 7, 3].length) (baseStart_457527 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_457527 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_457527 prefixEnd_457527 := by exact prefixLift 457527
  have htrace : WordTrace (prefixWord ++ tailWord_457527) baseStart_457527 baseEnd_457527 := by
    simpa [prefixWord, tailWord_457527, baseEnd_457527] using wordTrace_append hprefix tailTrace_457527
  have hstable : (prefixWord ++ tailWord_457527).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457527).length < 2 ^ (prefixWord ++ tailWord_457527).sum := by decide
  have hdescent : baseEnd_457527 < baseStart_457527 := by decide
  rcases family_descends (prefixWord ++ tailWord_457527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457542 : List Nat := [6, 1, 1, 2, 2, 1, 6]
def baseStart_457542 : Nat := 118140960795 + 457542 * 2 ^ 59
def prefixEnd_457542 : Nat := 4983230072969 + 3 ^ 40 * 457542 * 2
def baseEnd_457542 : Nat := 46407696912504513288061

theorem tailTrace_457542 : CollatzResearch.WordTrace tailWord_457542 prefixEnd_457542 46407696912504513288061 := by
  unfold tailWord_457542
  simp only [CollatzResearch.WordTrace]
  refine ⟨521497740887842212422215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11125285138940633865007253 521497740887842212422215)
  ·
    refine ⟨782246611331763318633323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 521497740887842212422215 782246611331763318633323)
    ·
      refine ⟨1173369916997644977949985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 782246611331763318633323 1173369916997644977949985)
      ·
        refine ⟨880027437748233733462489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1173369916997644977949985 880027437748233733462489)
        ·
          refine ⟨660020578311175300096867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 880027437748233733462489 660020578311175300096867)
          ·
            refine ⟨990030867466762950145301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 660020578311175300096867 990030867466762950145301)
            ·
              refine ⟨46407696912504513288061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 990030867466762950145301 46407696912504513288061)
              ·
                rfl

theorem cell19_457542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 6].length) (baseStart_457542 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_457542 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_457542 prefixEnd_457542 := by exact prefixLift 457542
  have htrace : WordTrace (prefixWord ++ tailWord_457542) baseStart_457542 baseEnd_457542 := by
    simpa [prefixWord, tailWord_457542, baseEnd_457542] using wordTrace_append hprefix tailTrace_457542
  have hstable : (prefixWord ++ tailWord_457542).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457542).length < 2 ^ (prefixWord ++ tailWord_457542).sum := by decide
  have hdescent : baseEnd_457542 < baseStart_457542 := by decide
  rcases family_descends (prefixWord ++ tailWord_457542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457567 : List Nat := [1, 1, 2, 3, 1, 3, 2, 6]
def baseStart_457567 : Nat := 118140960795 + 457567 * 2 ^ 59
def prefixEnd_457567 : Nat := 4983230072969 + 3 ^ 40 * 457567 * 2
def baseEnd_457567 : Nat := 139230697858320889308559

theorem tailTrace_457567 : CollatzResearch.WordTrace tailWord_457567 prefixEnd_457567 139230697858320889308559 := by
  unfold tailWord_457567
  simp only [CollatzResearch.WordTrace]
  refine ⟨16688839533320380067170955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11125893022213586711447303 16688839533320380067170955)
  ·
    refine ⟨25033259299980570100756433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16688839533320380067170955 25033259299980570100756433)
    ·
      refine ⟨18774944474985427575567325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25033259299980570100756433 18774944474985427575567325)
      ·
        refine ⟨7040604178119535340837747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18774944474985427575567325 7040604178119535340837747)
        ·
          refine ⟨10560906267179303011256621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7040604178119535340837747 10560906267179303011256621)
          ·
            refine ⟨3960339850192238629221233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10560906267179303011256621 3960339850192238629221233)
            ·
              refine ⟨2970254887644178971915925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3960339850192238629221233 2970254887644178971915925)
              ·
                refine ⟨139230697858320889308559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2970254887644178971915925 139230697858320889308559)
                ·
                  rfl

theorem cell19_457567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 6].length) (baseStart_457567 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_457567 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_457567 prefixEnd_457567 := by exact prefixLift 457567
  have htrace : WordTrace (prefixWord ++ tailWord_457567) baseStart_457567 baseEnd_457567 := by
    simpa [prefixWord, tailWord_457567, baseEnd_457567] using wordTrace_append hprefix tailTrace_457567
  have hstable : (prefixWord ++ tailWord_457567).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457567).length < 2 ^ (prefixWord ++ tailWord_457567).sum := by decide
  have hdescent : baseEnd_457567 < baseStart_457567 := by decide
  rcases family_descends (prefixWord ++ tailWord_457567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457582 : List Nat := [4, 1, 2, 3, 2, 1, 1, 5]
def baseStart_457582 : Nat := 118140960795 + 457582 * 2 ^ 59
def prefixEnd_457582 : Nat := 4983230072969 + 3 ^ 40 * 457582 * 2
def baseEnd_457582 : Nat := 139235262130805298975185

theorem tailTrace_457582 : CollatzResearch.WordTrace tailWord_457582 prefixEnd_457582 139235262130805298975185 := by
  unfold tailWord_457582
  simp only [CollatzResearch.WordTrace]
  refine ⟨2086173328533254703620875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11126257752177358419311333 2086173328533254703620875)
  ·
    refine ⟨3129259992799882055431313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2086173328533254703620875 3129259992799882055431313)
    ·
      refine ⟨2346944994599911541573485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3129259992799882055431313 2346944994599911541573485)
      ·
        refine ⟨880104372974966828090057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2346944994599911541573485 880104372974966828090057)
        ·
          refine ⟨660078279731225121067543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 880104372974966828090057 660078279731225121067543)
          ·
            refine ⟨990117419596837681601315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 660078279731225121067543 990117419596837681601315)
            ·
              refine ⟨1485176129395256522401973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 990117419596837681601315 1485176129395256522401973)
              ·
                refine ⟨139235262130805298975185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1485176129395256522401973 139235262130805298975185)
                ·
                  rfl

theorem cell19_457582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_457582 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_457582 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_457582 prefixEnd_457582 := by exact prefixLift 457582
  have htrace : WordTrace (prefixWord ++ tailWord_457582) baseStart_457582 baseEnd_457582 := by
    simpa [prefixWord, tailWord_457582, baseEnd_457582] using wordTrace_append hprefix tailTrace_457582
  have hstable : (prefixWord ++ tailWord_457582).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457582).length < 2 ^ (prefixWord ++ tailWord_457582).sum := by decide
  have hdescent : baseEnd_457582 < baseStart_457582 := by decide
  rcases family_descends (prefixWord ++ tailWord_457582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457584 : List Nat := [2, 1, 1, 1, 4, 1, 6, 3]
def baseStart_457584 : Nat := 118140960795 + 457584 * 2 ^ 59
def prefixEnd_457584 : Nat := 4983230072969 + 3 ^ 40 * 457584 * 2
def baseEnd_457584 : Nat := 139235870700469886930735

theorem tailTrace_457584 : CollatzResearch.WordTrace tailWord_457584 prefixEnd_457584 139235870700469886930735 := by
  unfold tailWord_457584
  simp only [CollatzResearch.WordTrace]
  refine ⟨8344729787129395985269903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11126306382839194647026537 8344729787129395985269903)
  ·
    refine ⟨12517094680694093977904855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8344729787129395985269903 12517094680694093977904855)
    ·
      refine ⟨18775642021041140966857283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12517094680694093977904855 18775642021041140966857283)
      ·
        refine ⟨28163463031561711450285925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18775642021041140966857283 28163463031561711450285925)
        ·
          refine ⟨5280649318417820896928611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28163463031561711450285925 5280649318417820896928611)
          ·
            refine ⟨7920973977626731345392917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5280649318417820896928611 7920973977626731345392917)
            ·
              refine ⟨371295655201253031815293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7920973977626731345392917 371295655201253031815293)
              ·
                refine ⟨139235870700469886930735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 371295655201253031815293 139235870700469886930735)
                ·
                  rfl

theorem cell19_457584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 6, 3].length) (baseStart_457584 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_457584 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_457584 prefixEnd_457584 := by exact prefixLift 457584
  have htrace : WordTrace (prefixWord ++ tailWord_457584) baseStart_457584 baseEnd_457584 := by
    simpa [prefixWord, tailWord_457584, baseEnd_457584] using wordTrace_append hprefix tailTrace_457584
  have hstable : (prefixWord ++ tailWord_457584).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457584).length < 2 ^ (prefixWord ++ tailWord_457584).sum := by decide
  have hdescent : baseEnd_457584 < baseStart_457584 := by decide
  rcases family_descends (prefixWord ++ tailWord_457584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457605 : List Nat := [1, 3, 1, 1, 3, 3, 7]
def baseStart_457605 : Nat := 118140960795 + 457605 * 2 ^ 59
def prefixEnd_457605 : Nat := 4983230072969 + 3 ^ 40 * 457605 * 2
def baseEnd_457605 : Nat := 46414086893982686821337

theorem tailTrace_457605 : CollatzResearch.WordTrace tailWord_457605 prefixEnd_457605 46414086893982686821337 := by
  unfold tailWord_457605
  simp only [CollatzResearch.WordTrace]
  refine ⟨16690225507182712557054269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11126817004788475038036179 16690225507182712557054269)
  ·
    refine ⟨6258834565193517208895351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16690225507182712557054269 6258834565193517208895351)
    ·
      refine ⟨9388251847790275813343027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6258834565193517208895351 9388251847790275813343027)
      ·
        refine ⟨14082377771685413720014541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9388251847790275813343027 14082377771685413720014541)
        ·
          refine ⟨5280891664382030145005453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14082377771685413720014541 5280891664382030145005453)
          ·
            refine ⟨1980334374143261304377045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5280891664382030145005453 1980334374143261304377045)
            ·
              refine ⟨46414086893982686821337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1980334374143261304377045 46414086893982686821337)
              ·
                rfl

theorem cell19_457605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 7].length) (baseStart_457605 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_457605 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_457605 prefixEnd_457605 := by exact prefixLift 457605
  have htrace : WordTrace (prefixWord ++ tailWord_457605) baseStart_457605 baseEnd_457605 := by
    simpa [prefixWord, tailWord_457605, baseEnd_457605] using wordTrace_append hprefix tailTrace_457605
  have hstable : (prefixWord ++ tailWord_457605).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457605).length < 2 ^ (prefixWord ++ tailWord_457605).sum := by decide
  have hdescent : baseEnd_457605 < baseStart_457605 := by decide
  rcases family_descends (prefixWord ++ tailWord_457605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457654 : List Nat := [5, 1, 4, 1, 2, 6]
def baseStart_457654 : Nat := 118140960795 + 457654 * 2 ^ 59
def prefixEnd_457654 : Nat := 4983230072969 + 3 ^ 40 * 457654 * 2
def baseEnd_457654 : Nat := 15473018959858940597221

theorem tailTrace_457654 : CollatzResearch.WordTrace tailWord_457654 prefixEnd_457654 15473018959858940597221 := by
  unfold tailWord_457654
  simp only [CollatzResearch.WordTrace]
  refine ⟨1043250792750324620349251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11128008456003462617058677 1043250792750324620349251)
  ·
    refine ⟨1564876189125486930523877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1043250792750324620349251 1564876189125486930523877)
    ·
      refine ⟨293414285461028799473227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1564876189125486930523877 293414285461028799473227)
      ·
        refine ⟨440121428191543199209841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293414285461028799473227 440121428191543199209841)
        ·
          refine ⟨330091071143657399407381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 440121428191543199209841 330091071143657399407381)
          ·
            refine ⟨15473018959858940597221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 330091071143657399407381 15473018959858940597221)
            ·
              rfl

theorem cell19_457654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 6].length) (baseStart_457654 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_457654 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_457654 prefixEnd_457654 := by exact prefixLift 457654
  have htrace : WordTrace (prefixWord ++ tailWord_457654) baseStart_457654 baseEnd_457654 := by
    simpa [prefixWord, tailWord_457654, baseEnd_457654] using wordTrace_append hprefix tailTrace_457654
  have hstable : (prefixWord ++ tailWord_457654).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457654).length < 2 ^ (prefixWord ++ tailWord_457654).sum := by decide
  have hdescent : baseEnd_457654 < baseStart_457654 := by decide
  rcases family_descends (prefixWord ++ tailWord_457654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457679 : List Nat := [1, 1, 2, 1, 1, 8, 1, 4]
def baseStart_457679 : Nat := 118140960795 + 457679 * 2 ^ 59
def prefixEnd_457679 : Nat := 4983230072969 + 3 ^ 40 * 457679 * 2
def baseEnd_457679 : Nat := 139264777759537814819365

theorem tailTrace_457679 : CollatzResearch.WordTrace tailWord_457679 prefixEnd_457679 139264777759537814819365 := by
  unfold tailWord_457679
  simp only [CollatzResearch.WordTrace]
  refine ⟨16692924508914623195248091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11128616339276415463498727 16692924508914623195248091)
  ·
    refine ⟨25039386763371934792872137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16692924508914623195248091 25039386763371934792872137)
    ·
      refine ⟨18779540072528951094654103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25039386763371934792872137 18779540072528951094654103)
      ·
        refine ⟨28169310108793426641981155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18779540072528951094654103 28169310108793426641981155)
        ·
          refine ⟨42253965163190139962971733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28169310108793426641981155 42253965163190139962971733)
          ·
            refine ⟨495163654256134452691075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 42253965163190139962971733 495163654256134452691075)
            ·
              refine ⟨742745481384201679036613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 495163654256134452691075 742745481384201679036613)
              ·
                refine ⟨139264777759537814819365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 742745481384201679036613 139264777759537814819365)
                ·
                  rfl

theorem cell19_457679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 4].length) (baseStart_457679 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_457679 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_457679 prefixEnd_457679 := by exact prefixLift 457679
  have htrace : WordTrace (prefixWord ++ tailWord_457679) baseStart_457679 baseEnd_457679 := by
    simpa [prefixWord, tailWord_457679, baseEnd_457679] using wordTrace_append hprefix tailTrace_457679
  have hstable : (prefixWord ++ tailWord_457679).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457679).length < 2 ^ (prefixWord ++ tailWord_457679).sum := by decide
  have hdescent : baseEnd_457679 < baseStart_457679 := by decide
  rcases family_descends (prefixWord ++ tailWord_457679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457795 : List Nat := [1, 1, 1, 3, 1, 2, 6, 4]
def baseStart_457795 : Nat := 118140960795 + 457795 * 2 ^ 59
def prefixEnd_457795 : Nat := 4983230072969 + 3 ^ 40 * 457795 * 2
def baseEnd_457795 : Nat := 139300074800083916241271

theorem tailTrace_457795 : CollatzResearch.WordTrace tailWord_457795 prefixEnd_457795 139300074800083916241271 := by
  unfold tailWord_457795
  simp only [CollatzResearch.WordTrace]
  refine ⟨16697155376494375006470839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11131436917662916670980559 16697155376494375006470839)
  ·
    refine ⟨25045733064741562509706259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16697155376494375006470839 25045733064741562509706259)
    ·
      refine ⟨37568599597112343764559389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25045733064741562509706259 37568599597112343764559389)
      ·
        refine ⟨14088224848917128911709771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37568599597112343764559389 14088224848917128911709771)
        ·
          refine ⟨21132337273375693367564657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14088224848917128911709771 21132337273375693367564657)
          ·
            refine ⟨15849252955031770025673493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21132337273375693367564657 15849252955031770025673493)
            ·
              refine ⟨742933732267114219953445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15849252955031770025673493 742933732267114219953445)
              ·
                refine ⟨139300074800083916241271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 742933732267114219953445 139300074800083916241271)
                ·
                  rfl

theorem cell19_457795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 4].length) (baseStart_457795 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_457795 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_457795 prefixEnd_457795 := by exact prefixLift 457795
  have htrace : WordTrace (prefixWord ++ tailWord_457795) baseStart_457795 baseEnd_457795 := by
    simpa [prefixWord, tailWord_457795, baseEnd_457795] using wordTrace_append hprefix tailTrace_457795
  have hstable : (prefixWord ++ tailWord_457795).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457795).length < 2 ^ (prefixWord ++ tailWord_457795).sum := by decide
  have hdescent : baseEnd_457795 < baseStart_457795 := by decide
  rcases family_descends (prefixWord ++ tailWord_457795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457922 : List Nat := [3, 5, 1, 1, 2, 1, 1, 5]
def baseStart_457922 : Nat := 118140960795 + 457922 * 2 ^ 59
def prefixEnd_457922 : Nat := 4983230072969 + 3 ^ 40 * 457922 * 2
def baseEnd_457922 : Nat := 139338718973785251418703

theorem tailTrace_457922 : CollatzResearch.WordTrace tailWord_457922 prefixEnd_457922 139338718973785251418703 := by
  unfold tailWord_457922
  simp only [CollatzResearch.WordTrace]
  refine ⟨4175446861758568924086005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11134524964689517130896013 4175446861758568924086005)
  ·
    refine ⟨391448143289865836633063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4175446861758568924086005 391448143289865836633063)
    ·
      refine ⟨587172214934798754949595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391448143289865836633063 587172214934798754949595)
      ·
        refine ⟨880758322402198132424393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 587172214934798754949595 880758322402198132424393)
        ·
          refine ⟨660568741801648599318295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 880758322402198132424393 660568741801648599318295)
          ·
            refine ⟨990853112702472898977443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 660568741801648599318295 990853112702472898977443)
            ·
              refine ⟨1486279669053709348466165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 990853112702472898977443 1486279669053709348466165)
              ·
                refine ⟨139338718973785251418703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1486279669053709348466165 139338718973785251418703)
                ·
                  rfl

theorem cell19_457922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 5].length) (baseStart_457922 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_457922 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_457922 prefixEnd_457922 := by exact prefixLift 457922
  have htrace : WordTrace (prefixWord ++ tailWord_457922) baseStart_457922 baseEnd_457922 := by
    simpa [prefixWord, tailWord_457922, baseEnd_457922] using wordTrace_append hprefix tailTrace_457922
  have hstable : (prefixWord ++ tailWord_457922).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457922).length < 2 ^ (prefixWord ++ tailWord_457922).sum := by decide
  have hdescent : baseEnd_457922 < baseStart_457922 := by decide
  rcases family_descends (prefixWord ++ tailWord_457922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457966 : List Nat := [4, 1, 2, 1, 1, 1, 3, 6]
def baseStart_457966 : Nat := 118140960795 + 457966 * 2 ^ 59
def prefixEnd_457966 : Nat := 4983230072969 + 3 ^ 40 * 457966 * 2
def baseEnd_457966 : Nat := 139352107506406186440805

theorem tailTrace_457966 : CollatzResearch.WordTrace tailWord_457966 prefixEnd_457966 139352107506406186440805 := by
  unfold tailWord_457966
  simp only [CollatzResearch.WordTrace]
  refine ⟨2087924032359358901368219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11135594839249914140630501 2087924032359358901368219)
  ·
    refine ⟨3131886048539038352052329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2087924032359358901368219 3131886048539038352052329)
    ·
      refine ⟨2348914536404278764039247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3131886048539038352052329 2348914536404278764039247)
      ·
        refine ⟨3523371804606418146058871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2348914536404278764039247 3523371804606418146058871)
        ·
          refine ⟨5285057706909627219088307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3523371804606418146058871 5285057706909627219088307)
          ·
            refine ⟨7927586560364440828632461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5285057706909627219088307 7927586560364440828632461)
            ·
              refine ⟨2972844960136665310737173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7927586560364440828632461 2972844960136665310737173)
              ·
                refine ⟨139352107506406186440805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2972844960136665310737173 139352107506406186440805)
                ·
                  rfl

theorem cell19_457966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_457966 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_457966 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_457966 prefixEnd_457966 := by exact prefixLift 457966
  have htrace : WordTrace (prefixWord ++ tailWord_457966) baseStart_457966 baseEnd_457966 := by
    simpa [prefixWord, tailWord_457966, baseEnd_457966] using wordTrace_append hprefix tailTrace_457966
  have hstable : (prefixWord ++ tailWord_457966).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457966).length < 2 ^ (prefixWord ++ tailWord_457966).sum := by decide
  have hdescent : baseEnd_457966 < baseStart_457966 := by decide
  rcases family_descends (prefixWord ++ tailWord_457966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_457985 : List Nat := [1, 2, 4, 1, 1, 3, 2, 5]
def baseStart_457985 : Nat := 118140960795 + 457985 * 2 ^ 59
def prefixEnd_457985 : Nat := 4983230072969 + 3 ^ 40 * 457985 * 2
def baseEnd_457985 : Nat := 139357888918219772018531

theorem tailTrace_457985 : CollatzResearch.WordTrace tailWord_457985 prefixEnd_457985 139357888918219772018531 := by
  unfold tailWord_457985
  simp only [CollatzResearch.WordTrace]
  refine ⟨16704085245806037455887409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11136056830537358303924939 16704085245806037455887409)
  ·
    refine ⟨12528063934354528091915557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16704085245806037455887409 12528063934354528091915557)
    ·
      refine ⟨2349011987691474017234167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12528063934354528091915557 2349011987691474017234167)
      ·
        refine ⟨3523517981537211025851251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2349011987691474017234167 3523517981537211025851251)
        ·
          refine ⟨5285276972305816538776877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3523517981537211025851251 5285276972305816538776877)
          ·
            refine ⟨1981978864614681202041329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5285276972305816538776877 1981978864614681202041329)
            ·
              refine ⟨1486484148461010901530997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1981978864614681202041329 1486484148461010901530997)
              ·
                refine ⟨139357888918219772018531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1486484148461010901530997 139357888918219772018531)
                ·
                  rfl

theorem cell19_457985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 5].length) (baseStart_457985 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_457985 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_457985 prefixEnd_457985 := by exact prefixLift 457985
  have htrace : WordTrace (prefixWord ++ tailWord_457985) baseStart_457985 baseEnd_457985 := by
    simpa [prefixWord, tailWord_457985, baseEnd_457985] using wordTrace_append hprefix tailTrace_457985
  have hstable : (prefixWord ++ tailWord_457985).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_457985).length < 2 ^ (prefixWord ++ tailWord_457985).sum := by decide
  have hdescent : baseEnd_457985 < baseStart_457985 := by decide
  rcases family_descends (prefixWord ++ tailWord_457985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458002 : List Nat := [3, 2, 4, 2, 8]
def baseStart_458002 : Nat := 118140960795 + 458002 * 2 ^ 59
def prefixEnd_458002 : Nat := 4983230072969 + 3 ^ 40 * 458002 * 2
def baseEnd_458002 : Nat := 5161594880013658134841

theorem tailTrace_458002 : CollatzResearch.WordTrace tailWord_458002 prefixEnd_458002 5161594880013658134841 := by
  unfold tailWord_458002
  simp only [CollatzResearch.WordTrace]
  refine ⟨4176176321686112339814065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11136470191162966239504173 4176176321686112339814065)
  ·
    refine ⟨3132132241264584254860549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4176176321686112339814065 3132132241264584254860549)
    ·
      refine ⟨587274795237109547786353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3132132241264584254860549 587274795237109547786353)
      ·
        refine ⟨440456096427832160839765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 587274795237109547786353 440456096427832160839765)
        ·
          refine ⟨5161594880013658134841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 440456096427832160839765 5161594880013658134841)
          ·
            rfl

theorem cell19_458002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 8].length) (baseStart_458002 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_458002 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_458002 prefixEnd_458002 := by exact prefixLift 458002
  have htrace : WordTrace (prefixWord ++ tailWord_458002) baseStart_458002 baseEnd_458002 := by
    simpa [prefixWord, tailWord_458002, baseEnd_458002] using wordTrace_append hprefix tailTrace_458002
  have hstable : (prefixWord ++ tailWord_458002).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458002).length < 2 ^ (prefixWord ++ tailWord_458002).sum := by decide
  have hdescent : baseEnd_458002 < baseStart_458002 := by decide
  rcases family_descends (prefixWord ++ tailWord_458002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458021 : List Nat := [1, 3, 1, 2, 4, 3, 1, 4]
def baseStart_458021 : Nat := 118140960795 + 458021 * 2 ^ 59
def prefixEnd_458021 : Nat := 4983230072969 + 3 ^ 40 * 458021 * 2
def baseEnd_458021 : Nat := 139368843172182355218433

theorem tailTrace_458021 : CollatzResearch.WordTrace tailWord_458021 prefixEnd_458021 139368843172182355218433 := by
  unfold tailWord_458021
  simp only [CollatzResearch.WordTrace]
  refine ⟨16705398273675615604197917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11136932182450410402798611 16705398273675615604197917)
  ·
    refine ⟨6264524352628355851574219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16705398273675615604197917 6264524352628355851574219)
    ·
      refine ⟨9396786528942533777361329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6264524352628355851574219 9396786528942533777361329)
      ·
        refine ⟨7047589896706900333020997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9396786528942533777361329 7047589896706900333020997)
        ·
          refine ⟨1321423105632543812441437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7047589896706900333020997 1321423105632543812441437)
          ·
            refine ⟨495533664612203929665539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1321423105632543812441437 495533664612203929665539)
            ·
              refine ⟨743300496918305894498309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 495533664612203929665539 743300496918305894498309)
              ·
                refine ⟨139368843172182355218433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 743300496918305894498309 139368843172182355218433)
                ·
                  rfl

theorem cell19_458021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 4].length) (baseStart_458021 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_458021 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_458021 prefixEnd_458021 := by exact prefixLift 458021
  have htrace : WordTrace (prefixWord ++ tailWord_458021) baseStart_458021 baseEnd_458021 := by
    simpa [prefixWord, tailWord_458021, baseEnd_458021] using wordTrace_append hprefix tailTrace_458021
  have hstable : (prefixWord ++ tailWord_458021).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458021).length < 2 ^ (prefixWord ++ tailWord_458021).sum := by decide
  have hdescent : baseEnd_458021 < baseStart_458021 := by decide
  rcases family_descends (prefixWord ++ tailWord_458021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458114 : List Nat := [3, 4, 2, 1, 1, 3, 5]
def baseStart_458114 : Nat := 118140960795 + 458114 * 2 ^ 59
def prefixEnd_458114 : Nat := 4983230072969 + 3 ^ 40 * 458114 * 2
def baseEnd_458114 : Nat := 46465713887195231717171

theorem tailTrace_458114 : CollatzResearch.WordTrace tailWord_458114 prefixEnd_458114 46465713887195231717171 := by
  unfold tailWord_458114
  simp only [CollatzResearch.WordTrace]
  refine ⟨4177197565584673121833349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11139193508225794991555597 4177197565584673121833349)
  ·
    refine ⟨783224543547126210343753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4177197565584673121833349 783224543547126210343753)
    ·
      refine ⟨587418407660344657757815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 783224543547126210343753 587418407660344657757815)
      ·
        refine ⟨881127611490516986636723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 587418407660344657757815 881127611490516986636723)
        ·
          refine ⟨1321691417235775479955085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 881127611490516986636723 1321691417235775479955085)
          ·
            refine ⟨495634281463415804983157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1321691417235775479955085 495634281463415804983157)
            ·
              refine ⟨46465713887195231717171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 495634281463415804983157 46465713887195231717171)
              ·
                rfl

theorem cell19_458114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 5].length) (baseStart_458114 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_458114 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_458114 prefixEnd_458114 := by exact prefixLift 458114
  have htrace : WordTrace (prefixWord ++ tailWord_458114) baseStart_458114 baseEnd_458114 := by
    simpa [prefixWord, tailWord_458114, baseEnd_458114] using wordTrace_append hprefix tailTrace_458114
  have hstable : (prefixWord ++ tailWord_458114).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458114).length < 2 ^ (prefixWord ++ tailWord_458114).sum := by decide
  have hdescent : baseEnd_458114 < baseStart_458114 := by decide
  rcases family_descends (prefixWord ++ tailWord_458114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458137 : List Nat := [1, 2, 1, 2, 1, 6, 2, 4]
def baseStart_458137 : Nat := 118140960795 + 458137 * 2 ^ 59
def prefixEnd_458137 : Nat := 4983230072969 + 3 ^ 40 * 458137 * 2
def baseEnd_458137 : Nat := 139404140212728456640339

theorem tailTrace_458137 : CollatzResearch.WordTrace tailWord_458137 prefixEnd_458137 139404140212728456640339 := by
  unfold tailWord_458137
  simp only [CollatzResearch.WordTrace]
  refine ⟨16709629141255367415420665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11139752760836911610280443 16709629141255367415420665)
  ·
    refine ⟨12532221855941525561565499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16709629141255367415420665 12532221855941525561565499)
    ·
      refine ⟨18798332783912288342348249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12532221855941525561565499 18798332783912288342348249)
      ·
        refine ⟨14098749587934216256761187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18798332783912288342348249 14098749587934216256761187)
        ·
          refine ⟨21148124381901324385141781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14098749587934216256761187 21148124381901324385141781)
          ·
            refine ⟨991318330401624580553521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 21148124381901324385141781 991318330401624580553521)
            ·
              refine ⟨743488747801218435415141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 991318330401624580553521 743488747801218435415141)
              ·
                refine ⟨139404140212728456640339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 743488747801218435415141 139404140212728456640339)
                ·
                  rfl

theorem cell19_458137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 4].length) (baseStart_458137 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_458137 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_458137 prefixEnd_458137 := by exact prefixLift 458137
  have htrace : WordTrace (prefixWord ++ tailWord_458137) baseStart_458137 baseEnd_458137 := by
    simpa [prefixWord, tailWord_458137, baseEnd_458137] using wordTrace_append hprefix tailTrace_458137
  have hstable : (prefixWord ++ tailWord_458137).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458137).length < 2 ^ (prefixWord ++ tailWord_458137).sum := by decide
  have hdescent : baseEnd_458137 < baseStart_458137 := by decide
  rcases family_descends (prefixWord ++ tailWord_458137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458211 : List Nat := [1, 1, 1, 6, 2, 2, 3, 3]
def baseStart_458211 : Nat := 118140960795 + 458211 * 2 ^ 59
def prefixEnd_458211 : Nat := 4983230072969 + 3 ^ 40 * 458211 * 2
def baseEnd_458211 : Nat := 139426657290318210995693

theorem tailTrace_458211 : CollatzResearch.WordTrace tailWord_458211 prefixEnd_458211 139426657290318210995693 := by
  unfold tailWord_458211
  simp only [CollatzResearch.WordTrace]
  refine ⟨16712328142987278053614487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11141552095324852035742991 16712328142987278053614487)
  ·
    refine ⟨25068492214480917080421731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16712328142987278053614487 25068492214480917080421731)
    ·
      refine ⟨37602738321721375620632597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25068492214480917080421731 37602738321721375620632597)
      ·
        refine ⟨1762628358830689482217153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 37602738321721375620632597 1762628358830689482217153)
        ·
          refine ⟨1321971269123017111662865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1762628358830689482217153 1321971269123017111662865)
          ·
            refine ⟨991478451842262833747149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1321971269123017111662865 991478451842262833747149)
            ·
              refine ⟨371804419440848562655181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 991478451842262833747149 371804419440848562655181)
              ·
                refine ⟨139426657290318210995693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 371804419440848562655181 139426657290318210995693)
                ·
                  rfl

theorem cell19_458211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 3, 3].length) (baseStart_458211 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_458211 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_458211 prefixEnd_458211 := by exact prefixLift 458211
  have htrace : WordTrace (prefixWord ++ tailWord_458211) baseStart_458211 baseEnd_458211 := by
    simpa [prefixWord, tailWord_458211, baseEnd_458211] using wordTrace_append hprefix tailTrace_458211
  have hstable : (prefixWord ++ tailWord_458211).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458211).length < 2 ^ (prefixWord ++ tailWord_458211).sum := by decide
  have hdescent : baseEnd_458211 < baseStart_458211 := by decide
  rcases family_descends (prefixWord ++ tailWord_458211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458234 : List Nat := [3, 1, 1, 1, 1, 2, 10]
def baseStart_458234 : Nat := 118140960795 + 458234 * 2 ^ 59
def prefixEnd_458234 : Nat := 4983230072969 + 3 ^ 40 * 458234 * 2
def baseEnd_458234 : Nat := 46477885280486990828173

theorem tailTrace_458234 : CollatzResearch.WordTrace tailWord_458234 prefixEnd_458234 46477885280486990828173 := by
  unfold tailWord_458234
  simp only [CollatzResearch.WordTrace]
  refine ⟨4178291755475988245425439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11142111347935968654467837 4178291755475988245425439)
  ·
    refine ⟨6267437633213982368138159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4178291755475988245425439 6267437633213982368138159)
    ·
      refine ⟨9401156449820973552207239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6267437633213982368138159 9401156449820973552207239)
      ·
        refine ⟨14101734674731460328310859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9401156449820973552207239 14101734674731460328310859)
        ·
          refine ⟨21152602012097190492466289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14101734674731460328310859 21152602012097190492466289)
          ·
            refine ⟨15864451509072892869349717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21152602012097190492466289 15864451509072892869349717)
            ·
              refine ⟨46477885280486990828173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15864451509072892869349717 46477885280486990828173)
              ·
                rfl

theorem cell19_458234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 10].length) (baseStart_458234 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_458234 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_458234 prefixEnd_458234 := by exact prefixLift 458234
  have htrace : WordTrace (prefixWord ++ tailWord_458234) baseStart_458234 baseEnd_458234 := by
    simpa [prefixWord, tailWord_458234, baseEnd_458234] using wordTrace_append hprefix tailTrace_458234
  have hstable : (prefixWord ++ tailWord_458234).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458234).length < 2 ^ (prefixWord ++ tailWord_458234).sum := by decide
  have hdescent : baseEnd_458234 < baseStart_458234 := by decide
  rcases family_descends (prefixWord ++ tailWord_458234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458291 : List Nat := [1, 1, 1, 2, 4, 3, 7]
def baseStart_458291 : Nat := 118140960795 + 458291 * 2 ^ 59
def prefixEnd_458291 : Nat := 4983230072969 + 3 ^ 40 * 458291 * 2
def baseEnd_458291 : Nat := 46483666692300576405899

theorem tailTrace_458291 : CollatzResearch.WordTrace tailWord_458291 prefixEnd_458291 46483666692300576405899 := by
  unfold tailWord_458291
  simp only [CollatzResearch.WordTrace]
  refine ⟨16715245982697451716526727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11143497321798301144351151 16715245982697451716526727)
  ·
    refine ⟨25072868974046177574790091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16715245982697451716526727 25072868974046177574790091)
    ·
      refine ⟨37609303461069266362185137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25072868974046177574790091 37609303461069266362185137)
      ·
        refine ⟨28206977595801949771638853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37609303461069266362185137 28206977595801949771638853)
        ·
          refine ⟨5288808299212865582182285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28206977595801949771638853 5288808299212865582182285)
          ·
            refine ⟨1983303112204824593318357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5288808299212865582182285 1983303112204824593318357)
            ·
              refine ⟨46483666692300576405899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1983303112204824593318357 46483666692300576405899)
              ·
                rfl

theorem cell19_458291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 7].length) (baseStart_458291 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_458291 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_458291 prefixEnd_458291 := by exact prefixLift 458291
  have htrace : WordTrace (prefixWord ++ tailWord_458291) baseStart_458291 baseEnd_458291 := by
    simpa [prefixWord, tailWord_458291, baseEnd_458291] using wordTrace_append hprefix tailTrace_458291
  have hstable : (prefixWord ++ tailWord_458291).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458291).length < 2 ^ (prefixWord ++ tailWord_458291).sum := by decide
  have hdescent : baseEnd_458291 < baseStart_458291 := by decide
  rcases family_descends (prefixWord ++ tailWord_458291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458365 : List Nat := [1, 4, 1, 1, 4, 1, 3, 4]
def baseStart_458365 : Nat := 118140960795 + 458365 * 2 ^ 59
def prefixEnd_458365 : Nat := 4983230072969 + 3 ^ 40 * 458365 * 2
def baseEnd_458365 : Nat := 139473517154491483573051

theorem tailTrace_458365 : CollatzResearch.WordTrace tailWord_458365 prefixEnd_458365 139473517154491483573051 := by
  unfold tailWord_458365
  simp only [CollatzResearch.WordTrace]
  refine ⟨16717944984429362354720549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11145296656286241569813699 16717944984429362354720549)
  ·
    refine ⟨3134614684580505441510103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16717944984429362354720549 3134614684580505441510103)
    ·
      refine ⟨4701922026870758162265155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3134614684580505441510103 4701922026870758162265155)
      ·
        refine ⟨7052883040306137243397733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4701922026870758162265155 7052883040306137243397733)
        ·
          refine ⟨1322415570057400733137075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7052883040306137243397733 1322415570057400733137075)
          ·
            refine ⟨1983623355086101099705613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1322415570057400733137075 1983623355086101099705613)
            ·
              refine ⟨743858758157287912389605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1983623355086101099705613 743858758157287912389605)
              ·
                refine ⟨139473517154491483573051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 743858758157287912389605 139473517154491483573051)
                ·
                  rfl

theorem cell19_458365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 4].length) (baseStart_458365 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_458365 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_458365 prefixEnd_458365 := by exact prefixLift 458365
  have htrace : WordTrace (prefixWord ++ tailWord_458365) baseStart_458365 baseEnd_458365 := by
    simpa [prefixWord, tailWord_458365, baseEnd_458365] using wordTrace_append hprefix tailTrace_458365
  have hstable : (prefixWord ++ tailWord_458365).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458365).length < 2 ^ (prefixWord ++ tailWord_458365).sum := by decide
  have hdescent : baseEnd_458365 < baseStart_458365 := by decide
  rcases family_descends (prefixWord ++ tailWord_458365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458382 : List Nat := [4, 1, 1, 3, 1, 3, 3, 3]
def baseStart_458382 : Nat := 118140960795 + 458382 * 2 ^ 59
def prefixEnd_458382 : Nat := 4983230072969 + 3 ^ 40 * 458382 * 2
def baseEnd_458382 : Nat := 139478689996640481195227

theorem tailTrace_458382 : CollatzResearch.WordTrace tailWord_458382 prefixEnd_458382 139478689996640481195227 := by
  unfold tailWord_458382
  simp only [CollatzResearch.WordTrace]
  refine ⟨2089820628170971782261175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11145710016911849505392933 2089820628170971782261175)
  ·
    refine ⟨3134730942256457673391763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2089820628170971782261175 3134730942256457673391763)
    ·
      refine ⟨4702096413384686510087645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3134730942256457673391763 4702096413384686510087645)
      ·
        refine ⟨1763286155019257441282867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4702096413384686510087645 1763286155019257441282867)
        ·
          refine ⟨2644929232528886161924301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1763286155019257441282867 2644929232528886161924301)
          ·
            refine ⟨991848462198332310721613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2644929232528886161924301 991848462198332310721613)
            ·
              refine ⟨371943173324374616520605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 991848462198332310721613 371943173324374616520605)
              ·
                refine ⟨139478689996640481195227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 371943173324374616520605 139478689996640481195227)
                ·
                  rfl

theorem cell19_458382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 3, 3].length) (baseStart_458382 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_458382 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_458382 prefixEnd_458382 := by exact prefixLift 458382
  have htrace : WordTrace (prefixWord ++ tailWord_458382) baseStart_458382 baseEnd_458382 := by
    simpa [prefixWord, tailWord_458382, baseEnd_458382] using wordTrace_append hprefix tailTrace_458382
  have hstable : (prefixWord ++ tailWord_458382).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458382).length < 2 ^ (prefixWord ++ tailWord_458382).sum := by decide
  have hdescent : baseEnd_458382 < baseStart_458382 := by decide
  rcases family_descends (prefixWord ++ tailWord_458382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458454 : List Nat := [5, 2, 1, 3, 2, 1, 5]
def baseStart_458454 : Nat := 118140960795 + 458454 * 2 ^ 59
def prefixEnd_458454 : Nat := 4983230072969 + 3 ^ 40 * 458454 * 2
def baseEnd_458454 : Nat := 46500199501521882531677

theorem tailTrace_458454 : CollatzResearch.WordTrace tailWord_458454 prefixEnd_458454 46500199501521882531677 := by
  unfold tailWord_458454
  simp only [CollatzResearch.WordTrace]
  refine ⟨1045074442569183159669401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11147460720737953703140277 1045074442569183159669401)
  ·
    refine ⟨783805831926887369752051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1045074442569183159669401 783805831926887369752051)
    ·
      refine ⟨1175708747890331054628077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 783805831926887369752051 1175708747890331054628077)
      ·
        refine ⟨440890780458874145485529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1175708747890331054628077 440890780458874145485529)
        ·
          refine ⟨330668085344155609114147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 440890780458874145485529 330668085344155609114147)
          ·
            refine ⟨496002128016233413671221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 330668085344155609114147 496002128016233413671221)
            ·
              refine ⟨46500199501521882531677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 496002128016233413671221 46500199501521882531677)
              ·
                rfl

theorem cell19_458454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 5].length) (baseStart_458454 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_458454 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_458454 prefixEnd_458454 := by exact prefixLift 458454
  have htrace : WordTrace (prefixWord ++ tailWord_458454) baseStart_458454 baseEnd_458454 := by
    simpa [prefixWord, tailWord_458454, baseEnd_458454] using wordTrace_append hprefix tailTrace_458454
  have hstable : (prefixWord ++ tailWord_458454).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458454).length < 2 ^ (prefixWord ++ tailWord_458454).sum := by decide
  have hdescent : baseEnd_458454 < baseStart_458454 := by decide
  rcases family_descends (prefixWord ++ tailWord_458454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458481 : List Nat := [1, 2, 2, 2, 2, 3, 1, 6]
def baseStart_458481 : Nat := 118140960795 + 458481 * 2 ^ 59
def prefixEnd_458481 : Nat := 4983230072969 + 3 ^ 40 * 458481 * 2
def baseEnd_458481 : Nat := 139508814195037584994957

theorem tailTrace_458481 : CollatzResearch.WordTrace tailWord_458481 prefixEnd_458481 139508814195037584994957 := by
  unfold tailWord_458481
  simp only [CollatzResearch.WordTrace]
  refine ⟨16722175852009114165943297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11148117234672742777295531 16722175852009114165943297)
  ·
    refine ⟨12541631889006835624457473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16722175852009114165943297 12541631889006835624457473)
    ·
      refine ⟨9406223916755126718343105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12541631889006835624457473 9406223916755126718343105)
      ·
        refine ⟨7054667937566345038757329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9406223916755126718343105 7054667937566345038757329)
        ·
          refine ⟨5291000953174758779067997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7054667937566345038757329 5291000953174758779067997)
          ·
            refine ⟨1984125357440534542150499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5291000953174758779067997 1984125357440534542150499)
            ·
              refine ⟨2976188036160801813225749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1984125357440534542150499 2976188036160801813225749)
              ·
                refine ⟨139508814195037584994957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2976188036160801813225749 139508814195037584994957)
                ·
                  rfl

theorem cell19_458481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 6].length) (baseStart_458481 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_458481 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_458481 prefixEnd_458481 := by exact prefixLift 458481
  have htrace : WordTrace (prefixWord ++ tailWord_458481) baseStart_458481 baseEnd_458481 := by
    simpa [prefixWord, tailWord_458481, baseEnd_458481] using wordTrace_append hprefix tailTrace_458481
  have hstable : (prefixWord ++ tailWord_458481).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458481).length < 2 ^ (prefixWord ++ tailWord_458481).sum := by decide
  have hdescent : baseEnd_458481 < baseStart_458481 := by decide
  rcases family_descends (prefixWord ++ tailWord_458481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458498 : List Nat := [3, 4, 1, 1, 1, 1, 1, 7]
def baseStart_458498 : Nat := 118140960795 + 458498 * 2 ^ 59
def prefixEnd_458498 : Nat := 4983230072969 + 3 ^ 40 * 458498 * 2
def baseEnd_458498 : Nat := 139513987037186582617133

theorem tailTrace_458498 : CollatzResearch.WordTrace tailWord_458498 prefixEnd_458498 139513987037186582617133 := by
  unfold tailWord_458498
  simp only [CollatzResearch.WordTrace]
  refine ⟨4180698973236881517328037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11148530595298350712874765 4180698973236881517328037)
  ·
    refine ⟨783881057481915284499007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4180698973236881517328037 783881057481915284499007)
    ·
      refine ⟨1175821586222872926748511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 783881057481915284499007 1175821586222872926748511)
      ·
        refine ⟨1763732379334309390122767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1175821586222872926748511 1763732379334309390122767)
        ·
          refine ⟨2645598569001464085184151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1763732379334309390122767 2645598569001464085184151)
          ·
            refine ⟨3968397853502196127776227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2645598569001464085184151 3968397853502196127776227)
            ·
              refine ⟨5952596780253294191664341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3968397853502196127776227 5952596780253294191664341)
              ·
                refine ⟨139513987037186582617133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5952596780253294191664341 139513987037186582617133)
                ·
                  rfl

theorem cell19_458498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 7].length) (baseStart_458498 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_458498 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_458498 prefixEnd_458498 := by exact prefixLift 458498
  have htrace : WordTrace (prefixWord ++ tailWord_458498) baseStart_458498 baseEnd_458498 := by
    simpa [prefixWord, tailWord_458498, baseEnd_458498] using wordTrace_append hprefix tailTrace_458498
  have hstable : (prefixWord ++ tailWord_458498).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458498).length < 2 ^ (prefixWord ++ tailWord_458498).sum := by decide
  have hdescent : baseEnd_458498 < baseStart_458498 := by decide
  rcases family_descends (prefixWord ++ tailWord_458498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458519 : List Nat := [1, 1, 3, 4, 2, 8]
def baseStart_458519 : Nat := 118140960795 + 458519 * 2 ^ 59
def prefixEnd_458519 : Nat := 4983230072969 + 3 ^ 40 * 458519 * 2
def baseEnd_458519 : Nat := 15502264113184972905601

theorem tailTrace_458519 : CollatzResearch.WordTrace tailWord_458519 prefixEnd_458519 15502264113184972905601 := by
  unfold tailWord_458519
  simp only [CollatzResearch.WordTrace]
  refine ⟨16723561825871446655826611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11149041217247631103884407 16723561825871446655826611)
  ·
    refine ⟨25085342738807169983739917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16723561825871446655826611 25085342738807169983739917)
    ·
      refine ⟨9407003527052688743902469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25085342738807169983739917 9407003527052688743902469)
      ·
        refine ⟨1763813161322379139481713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9407003527052688743902469 1763813161322379139481713)
        ·
          refine ⟨1322859870991784354611285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1763813161322379139481713 1322859870991784354611285)
          ·
            refine ⟨15502264113184972905601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1322859870991784354611285 15502264113184972905601)
            ·
              rfl

theorem cell19_458519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 8].length) (baseStart_458519 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_458519 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_458519 prefixEnd_458519 := by exact prefixLift 458519
  have htrace : WordTrace (prefixWord ++ tailWord_458519) baseStart_458519 baseEnd_458519 := by
    simpa [prefixWord, tailWord_458519, baseEnd_458519] using wordTrace_append hprefix tailTrace_458519
  have hstable : (prefixWord ++ tailWord_458519).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458519).length < 2 ^ (prefixWord ++ tailWord_458519).sum := by decide
  have hdescent : baseEnd_458519 < baseStart_458519 := by decide
  rcases family_descends (prefixWord ++ tailWord_458519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458536 : List Nat := [2, 1, 5, 1, 1, 2, 3, 4]
def baseStart_458536 : Nat := 118140960795 + 458536 * 2 ^ 59
def prefixEnd_458536 : Nat := 4983230072969 + 3 ^ 40 * 458536 * 2
def baseEnd_458536 : Nat := 139525549860813753772585

theorem tailTrace_458536 : CollatzResearch.WordTrace tailWord_458536 prefixEnd_458536 139525549860813753772585 := by
  unfold tailWord_458536
  simp only [CollatzResearch.WordTrace]
  refine ⟨8362090933404929279597731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11149454577873239039463641 8362090933404929279597731)
  ·
    refine ⟨12543136400107393919396597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8362090933404929279597731 12543136400107393919396597)
    ·
      refine ⟨1175919037510068179943431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12543136400107393919396597 1175919037510068179943431)
      ·
        refine ⟨1763878556265102269915147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1175919037510068179943431 1763878556265102269915147)
        ·
          refine ⟨2645817834397653404872721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1763878556265102269915147 2645817834397653404872721)
          ·
            refine ⟨1984363375798240053654541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2645817834397653404872721 1984363375798240053654541)
            ·
              refine ⟨744136265924340020120453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1984363375798240053654541 744136265924340020120453)
              ·
                refine ⟨139525549860813753772585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 744136265924340020120453 139525549860813753772585)
                ·
                  rfl

theorem cell19_458536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 4].length) (baseStart_458536 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_458536 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_458536 prefixEnd_458536 := by exact prefixLift 458536
  have htrace : WordTrace (prefixWord ++ tailWord_458536) baseStart_458536 baseEnd_458536 := by
    simpa [prefixWord, tailWord_458536, baseEnd_458536] using wordTrace_append hprefix tailTrace_458536
  have hstable : (prefixWord ++ tailWord_458536).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458536).length < 2 ^ (prefixWord ++ tailWord_458536).sum := by decide
  have hdescent : baseEnd_458536 < baseStart_458536 := by decide
  rcases family_descends (prefixWord ++ tailWord_458536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458631 : List Nat := [1, 1, 4, 2, 4, 2, 5]
def baseStart_458631 : Nat := 118140960795 + 458631 * 2 ^ 59
def prefixEnd_458631 : Nat := 4983230072969 + 3 ^ 40 * 458631 * 2
def baseEnd_458631 : Nat := 46518152306627227220405

theorem tailTrace_458631 : CollatzResearch.WordTrace tailWord_458631 prefixEnd_458631 46518152306627227220405 := by
  unfold tailWord_458631
  simp only [CollatzResearch.WordTrace]
  refine ⟨16727646801465689783903747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11151764534310459855935831 16727646801465689783903747)
  ·
    refine ⟨25091470202198534675855621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16727646801465689783903747 25091470202198534675855621)
    ·
      refine ⟨4704650662912225251722929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25091470202198534675855621 4704650662912225251722929)
      ·
        refine ⟨3528487997184168938792197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4704650662912225251722929 3528487997184168938792197)
        ·
          refine ⟨661591499472031676023537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3528487997184168938792197 661591499472031676023537)
          ·
            refine ⟨496193624604023757017653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 661591499472031676023537 496193624604023757017653)
            ·
              refine ⟨46518152306627227220405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 496193624604023757017653 46518152306627227220405)
              ·
                rfl

theorem cell19_458631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 5].length) (baseStart_458631 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_458631 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_458631 prefixEnd_458631 := by exact prefixLift 458631
  have htrace : WordTrace (prefixWord ++ tailWord_458631) baseStart_458631 baseEnd_458631 := by
    simpa [prefixWord, tailWord_458631, baseEnd_458631] using wordTrace_append hprefix tailTrace_458631
  have hstable : (prefixWord ++ tailWord_458631).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458631).length < 2 ^ (prefixWord ++ tailWord_458631).sum := by decide
  have hdescent : baseEnd_458631 < baseStart_458631 := by decide
  rcases family_descends (prefixWord ++ tailWord_458631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458648 : List Nat := [2, 1, 2, 6, 1, 1, 2, 4]
def baseStart_458648 : Nat := 118140960795 + 458648 * 2 ^ 59
def prefixEnd_458648 : Nat := 4983230072969 + 3 ^ 40 * 458648 * 2
def baseEnd_458648 : Nat := 139559629762030679283391

theorem tailTrace_458648 : CollatzResearch.WordTrace tailWord_458648 prefixEnd_458648 139559629762030679283391 := by
  unfold tailWord_458648
  simp only [CollatzResearch.WordTrace]
  refine ⟨8364133421202050843636299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11152177894936067791515065 8364133421202050843636299)
  ·
    refine ⟨12546200131803076265454449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8364133421202050843636299 12546200131803076265454449)
    ·
      refine ⟨9409650098852307199090837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12546200131803076265454449 9409650098852307199090837)
      ·
        refine ⟨441077348383701899957383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 9409650098852307199090837 441077348383701899957383)
        ·
          refine ⟨661616022575552849936075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 441077348383701899957383 661616022575552849936075)
          ·
            refine ⟨992424033863329274904113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 661616022575552849936075 992424033863329274904113)
            ·
              refine ⟨744318025397496956178085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 992424033863329274904113 744318025397496956178085)
              ·
                refine ⟨139559629762030679283391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 744318025397496956178085 139559629762030679283391)
                ·
                  rfl

theorem cell19_458648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 4].length) (baseStart_458648 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_458648 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_458648 prefixEnd_458648 := by exact prefixLift 458648
  have htrace : WordTrace (prefixWord ++ tailWord_458648) baseStart_458648 baseEnd_458648 := by
    simpa [prefixWord, tailWord_458648, baseEnd_458648] using wordTrace_append hprefix tailTrace_458648
  have hstable : (prefixWord ++ tailWord_458648).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458648).length < 2 ^ (prefixWord ++ tailWord_458648).sum := by decide
  have hdescent : baseEnd_458648 < baseStart_458648 := by decide
  rcases family_descends (prefixWord ++ tailWord_458648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458650 : List Nat := [3, 1, 1, 4, 2, 2, 2, 4]
def baseStart_458650 : Nat := 118140960795 + 458650 * 2 ^ 59
def prefixEnd_458650 : Nat := 4983230072969 + 3 ^ 40 * 458650 * 2
def baseEnd_458650 : Nat := 139560238331695267238941

theorem tailTrace_458650 : CollatzResearch.WordTrace tailWord_458650 prefixEnd_458650 139560238331695267238941 := by
  unfold tailWord_458650
  simp only [CollatzResearch.WordTrace]
  refine ⟨4182084947099214007211351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11152226525597904019230269 4182084947099214007211351)
  ·
    refine ⟨6273127420648821010817027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4182084947099214007211351 6273127420648821010817027)
    ·
      refine ⟨9409691130973231516225541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6273127420648821010817027 9409691130973231516225541)
      ·
        refine ⟨1764317087057480909292289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9409691130973231516225541 1764317087057480909292289)
        ·
          refine ⟨1323237815293110681969217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1764317087057480909292289 1323237815293110681969217)
          ·
            refine ⟨992428361469833011476913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1323237815293110681969217 992428361469833011476913)
            ·
              refine ⟨744321271102374758607685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 992428361469833011476913 744321271102374758607685)
              ·
                refine ⟨139560238331695267238941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 744321271102374758607685 139560238331695267238941)
                ·
                  rfl

theorem cell19_458650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 4].length) (baseStart_458650 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_458650 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_458650 prefixEnd_458650 := by exact prefixLift 458650
  have htrace : WordTrace (prefixWord ++ tailWord_458650) baseStart_458650 baseEnd_458650 := by
    simpa [prefixWord, tailWord_458650, baseEnd_458650] using wordTrace_append hprefix tailTrace_458650
  have hstable : (prefixWord ++ tailWord_458650).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458650).length < 2 ^ (prefixWord ++ tailWord_458650).sum := by decide
  have hdescent : baseEnd_458650 < baseStart_458650 := by decide
  rcases family_descends (prefixWord ++ tailWord_458650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458722 : List Nat := [3, 3, 3, 1, 2, 1, 3, 3]
def baseStart_458722 : Nat := 118140960795 + 458722 * 2 ^ 59
def prefixEnd_458722 : Nat := 4983230072969 + 3 ^ 40 * 458722 * 2
def baseEnd_458722 : Nat := 139582146839620433638745

theorem tailTrace_458722 : CollatzResearch.WordTrace tailWord_458722 prefixEnd_458722 139582146839620433638745 := by
  unfold tailWord_458722
  simp only [CollatzResearch.WordTrace]
  refine ⟨4182741461034003081366605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11153977229424008216977613 4182741461034003081366605)
  ·
    refine ⟨1568528047887751155512477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4182741461034003081366605 1568528047887751155512477)
    ·
      refine ⟨588198017957906683317179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1568528047887751155512477 588198017957906683317179)
      ·
        refine ⟨882297026936860024975769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 588198017957906683317179 882297026936860024975769)
        ·
          refine ⟨661722770202645018731827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 882297026936860024975769 661722770202645018731827)
          ·
            refine ⟨992584155303967528097741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 661722770202645018731827 992584155303967528097741)
            ·
              refine ⟨372219058238987823036653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 992584155303967528097741 372219058238987823036653)
              ·
                refine ⟨139582146839620433638745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 372219058238987823036653 139582146839620433638745)
                ·
                  rfl

theorem cell19_458722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 3, 3].length) (baseStart_458722 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_458722 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_458722 prefixEnd_458722 := by exact prefixLift 458722
  have htrace : WordTrace (prefixWord ++ tailWord_458722) baseStart_458722 baseEnd_458722 := by
    simpa [prefixWord, tailWord_458722, baseEnd_458722] using wordTrace_append hprefix tailTrace_458722
  have hstable : (prefixWord ++ tailWord_458722).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458722).length < 2 ^ (prefixWord ++ tailWord_458722).sum := by decide
  have hdescent : baseEnd_458722 < baseStart_458722 := by decide
  rcases family_descends (prefixWord ++ tailWord_458722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458766 : List Nat := [4, 1, 1, 2, 2, 1, 2, 6]
def baseStart_458766 : Nat := 118140960795 + 458766 * 2 ^ 59
def prefixEnd_458766 : Nat := 4983230072969 + 3 ^ 40 * 458766 * 2
def baseEnd_458766 : Nat := 139595535372241368660847

theorem tailTrace_458766 : CollatzResearch.WordTrace tailWord_458766 prefixEnd_458766 139595535372241368660847 := by
  unfold tailWord_458766
  simp only [CollatzResearch.WordTrace]
  refine ⟨2091571331997075980008519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11155047103984405226712101 2091571331997075980008519)
  ·
    refine ⟨3137356997995613970012779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2091571331997075980008519 3137356997995613970012779)
    ·
      refine ⟨4706035496993420955019169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3137356997995613970012779 4706035496993420955019169)
      ·
        refine ⟨3529526622745065716264377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4706035496993420955019169 3529526622745065716264377)
        ·
          refine ⟨2647144967058799287198283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3529526622745065716264377 2647144967058799287198283)
          ·
            refine ⟨3970717450588198930797425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2647144967058799287198283 3970717450588198930797425)
            ·
              refine ⟨2978038087941149198098069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3970717450588198930797425 2978038087941149198098069)
              ·
                refine ⟨139595535372241368660847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2978038087941149198098069 139595535372241368660847)
                ·
                  rfl

theorem cell19_458766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_458766 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_458766 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_458766 prefixEnd_458766 := by exact prefixLift 458766
  have htrace : WordTrace (prefixWord ++ tailWord_458766) baseStart_458766 baseEnd_458766 := by
    simpa [prefixWord, tailWord_458766, baseEnd_458766] using wordTrace_append hprefix tailTrace_458766
  have hstable : (prefixWord ++ tailWord_458766).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458766).length < 2 ^ (prefixWord ++ tailWord_458766).sum := by decide
  have hdescent : baseEnd_458766 < baseStart_458766 := by decide
  rcases family_descends (prefixWord ++ tailWord_458766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458781 : List Nat := [1, 4, 2, 2, 2, 3, 2, 3]
def baseStart_458781 : Nat := 118140960795 + 458781 * 2 ^ 59
def prefixEnd_458781 : Nat := 4983230072969 + 3 ^ 40 * 458781 * 2
def baseEnd_458781 : Nat := 139600099644725778327473

theorem tailTrace_458781 : CollatzResearch.WordTrace tailWord_458781 prefixEnd_458781 139600099644725778327473 := by
  unfold tailWord_458781
  simp only [CollatzResearch.WordTrace]
  refine ⟨16733117750922265401864197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11155411833948176934576131 16733117750922265401864197)
  ·
    refine ⟨3137459578297924762849537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16733117750922265401864197 3137459578297924762849537)
    ·
      refine ⟨2353094683723443572137153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3137459578297924762849537 2353094683723443572137153)
      ·
        refine ⟨1764821012792582679102865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2353094683723443572137153 1764821012792582679102865)
        ·
          refine ⟨1323615759594437009327149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1764821012792582679102865 1323615759594437009327149)
          ·
            refine ⟨496355909847913878497681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1323615759594437009327149 496355909847913878497681)
            ·
              refine ⟨372266932385935408873261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 496355909847913878497681 372266932385935408873261)
              ·
                refine ⟨139600099644725778327473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 372266932385935408873261 139600099644725778327473)
                ·
                  rfl

theorem cell19_458781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 2, 3].length) (baseStart_458781 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_458781 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_458781 prefixEnd_458781 := by exact prefixLift 458781
  have htrace : WordTrace (prefixWord ++ tailWord_458781) baseStart_458781 baseEnd_458781 := by
    simpa [prefixWord, tailWord_458781, baseEnd_458781] using wordTrace_append hprefix tailTrace_458781
  have hstable : (prefixWord ++ tailWord_458781).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458781).length < 2 ^ (prefixWord ++ tailWord_458781).sum := by decide
  have hdescent : baseEnd_458781 < baseStart_458781 := by decide
  rcases family_descends (prefixWord ++ tailWord_458781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458823 : List Nat := [1, 1, 4, 1, 3, 1, 4, 4]
def baseStart_458823 : Nat := 118140960795 + 458823 * 2 ^ 59
def prefixEnd_458823 : Nat := 4983230072969 + 3 ^ 40 * 458823 * 2
def baseEnd_458823 : Nat := 139612879607682125394025

theorem tailTrace_458823 : CollatzResearch.WordTrace tailWord_458823 prefixEnd_458823 139612879607682125394025 := by
  unfold tailWord_458823
  simp only [CollatzResearch.WordTrace]
  refine ⟨16734649616770106574893123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11156433077846737716595415 16734649616770106574893123)
  ·
    refine ⟨25101974425155159862339685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16734649616770106574893123 25101974425155159862339685)
    ·
      refine ⟨4706620204716592474188691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25101974425155159862339685 4706620204716592474188691)
      ·
        refine ⟨7059930307074888711283037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4706620204716592474188691 7059930307074888711283037)
        ·
          refine ⟨2647473865153083266731139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7059930307074888711283037 2647473865153083266731139)
          ·
            refine ⟨3971210797729624900096709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2647473865153083266731139 3971210797729624900096709)
            ·
              refine ⟨744602024574304668768133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3971210797729624900096709 744602024574304668768133)
              ·
                refine ⟨139612879607682125394025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 744602024574304668768133 139612879607682125394025)
                ·
                  rfl

theorem cell19_458823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 4].length) (baseStart_458823 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_458823 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_458823 prefixEnd_458823 := by exact prefixLift 458823
  have htrace : WordTrace (prefixWord ++ tailWord_458823) baseStart_458823 baseEnd_458823 := by
    simpa [prefixWord, tailWord_458823, baseEnd_458823] using wordTrace_append hprefix tailTrace_458823
  have hstable : (prefixWord ++ tailWord_458823).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458823).length < 2 ^ (prefixWord ++ tailWord_458823).sum := by decide
  have hdescent : baseEnd_458823 < baseStart_458823 := by decide
  rcases family_descends (prefixWord ++ tailWord_458823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458838 : List Nat := [5, 2, 2, 1, 1, 1, 2, 5]
def baseStart_458838 : Nat := 118140960795 + 458838 * 2 ^ 59
def prefixEnd_458838 : Nat := 4983230072969 + 3 ^ 40 * 458838 * 2
def baseEnd_458838 : Nat := 139617443880166535060651

theorem tailTrace_458838 : CollatzResearch.WordTrace tailWord_458838 prefixEnd_458838 139617443880166535060651 := by
  unfold tailWord_458838
  simp only [CollatzResearch.WordTrace]
  refine ⟨1045949794482235258543073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11156797807810509424459445 1045949794482235258543073)
  ·
    refine ⟨784462345861676443907305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1045949794482235258543073 784462345861676443907305)
    ·
      refine ⟨588346759396257332930479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 784462345861676443907305 588346759396257332930479)
      ·
        refine ⟨882520139094385999395719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 588346759396257332930479 882520139094385999395719)
        ·
          refine ⟨1323780208641578999093579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 882520139094385999395719 1323780208641578999093579)
          ·
            refine ⟨1985670312962368498640369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1323780208641578999093579 1985670312962368498640369)
            ·
              refine ⟨1489252734721776373980277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1985670312962368498640369 1489252734721776373980277)
              ·
                refine ⟨139617443880166535060651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1489252734721776373980277 139617443880166535060651)
                ·
                  rfl

theorem cell19_458838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_458838 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_458838 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_458838 prefixEnd_458838 := by exact prefixLift 458838
  have htrace : WordTrace (prefixWord ++ tailWord_458838) baseStart_458838 baseEnd_458838 := by
    simpa [prefixWord, tailWord_458838, baseEnd_458838] using wordTrace_append hprefix tailTrace_458838
  have hstable : (prefixWord ++ tailWord_458838).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458838).length < 2 ^ (prefixWord ++ tailWord_458838).sum := by decide
  have hdescent : baseEnd_458838 < baseStart_458838 := by decide
  rcases family_descends (prefixWord ++ tailWord_458838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458863 : List Nat := [1, 1, 2, 1, 3, 11]
def baseStart_458863 : Nat := 118140960795 + 458863 * 2 ^ 59
def prefixEnd_458863 : Nat := 4983230072969 + 3 ^ 40 * 458863 * 2
def baseEnd_458863 : Nat := 15513894555663764945003

theorem tailTrace_458863 : CollatzResearch.WordTrace tailWord_458863 prefixEnd_458863 15513894555663764945003 := by
  unfold tailWord_458863
  simp only [CollatzResearch.WordTrace]
  refine ⟨16736108536625193406349243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11157405691083462270899495 16736108536625193406349243)
  ·
    refine ⟨25104162804937790109523865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16736108536625193406349243 25104162804937790109523865)
    ·
      refine ⟨18828122103703342582142899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25104162804937790109523865 18828122103703342582142899)
      ·
        refine ⟨28242183155555013873214349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18828122103703342582142899 28242183155555013873214349)
        ·
          refine ⟨10590818683333130202455381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28242183155555013873214349 10590818683333130202455381)
          ·
            refine ⟨15513894555663764945003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 10590818683333130202455381 15513894555663764945003)
            ·
              rfl

theorem cell19_458863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 11].length) (baseStart_458863 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_458863 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_458863 prefixEnd_458863 := by exact prefixLift 458863
  have htrace : WordTrace (prefixWord ++ tailWord_458863) baseStart_458863 baseEnd_458863 := by
    simpa [prefixWord, tailWord_458863, baseEnd_458863] using wordTrace_append hprefix tailTrace_458863
  have hstable : (prefixWord ++ tailWord_458863).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458863).length < 2 ^ (prefixWord ++ tailWord_458863).sum := by decide
  have hdescent : baseEnd_458863 < baseStart_458863 := by decide
  rcases family_descends (prefixWord ++ tailWord_458863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458939 : List Nat := [1, 1, 1, 1, 1, 2, 6, 6]
def baseStart_458939 : Nat := 118140960795 + 458939 * 2 ^ 59
def prefixEnd_458939 : Nat := 4983230072969 + 3 ^ 40 * 458939 * 2
def baseEnd_458939 : Nat := 139648176648228226815931

theorem tailTrace_458939 : CollatzResearch.WordTrace tailWord_458939 prefixEnd_458939 139648176648228226815931 := by
  unfold tailWord_458939
  simp only [CollatzResearch.WordTrace]
  refine ⟨16738880484349858386115871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11159253656233238924077247 16738880484349858386115871)
  ·
    refine ⟨25108320726524787579173807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16738880484349858386115871 25108320726524787579173807)
    ·
      refine ⟨37662481089787181368760711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25108320726524787579173807 37662481089787181368760711)
      ·
        refine ⟨56493721634680772053141067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37662481089787181368760711 56493721634680772053141067)
        ·
          refine ⟨84740582452021158079711601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56493721634680772053141067 84740582452021158079711601)
          ·
            refine ⟨63555436839015868559783701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84740582452021158079711601 63555436839015868559783701)
            ·
              refine ⟨2979161101828868838739861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 63555436839015868559783701 2979161101828868838739861)
              ·
                refine ⟨139648176648228226815931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2979161101828868838739861 139648176648228226815931)
                ·
                  rfl

theorem cell19_458939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 6].length) (baseStart_458939 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_458939 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_458939 prefixEnd_458939 := by exact prefixLift 458939
  have htrace : WordTrace (prefixWord ++ tailWord_458939) baseStart_458939 baseEnd_458939 := by
    simpa [prefixWord, tailWord_458939, baseEnd_458939] using wordTrace_append hprefix tailTrace_458939
  have hstable : (prefixWord ++ tailWord_458939).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458939).length < 2 ^ (prefixWord ++ tailWord_458939).sum := by decide
  have hdescent : baseEnd_458939 < baseStart_458939 := by decide
  rcases family_descends (prefixWord ++ tailWord_458939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458973 : List Nat := [1, 4, 3, 2, 1, 3, 5]
def baseStart_458973 : Nat := 118140960795 + 458973 * 2 ^ 59
def prefixEnd_458973 : Nat := 4983230072969 + 3 ^ 40 * 458973 * 2
def baseEnd_458973 : Nat := 46552840777508740686761

theorem tailTrace_458973 : CollatzResearch.WordTrace tailWord_458973 prefixEnd_458973 46552840777508740686761 := by
  unfold tailWord_458973
  simp only [CollatzResearch.WordTrace]
  refine ⟨16740120566226682192853573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11160080377484454795235715 16740120566226682192853573)
  ·
    refine ⟨3138772606167502911160045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16740120566226682192853573 3138772606167502911160045)
    ·
      refine ⟨1177039727312813591685017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3138772606167502911160045 1177039727312813591685017)
      ·
        refine ⟨882779795484610193763763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1177039727312813591685017 882779795484610193763763)
        ·
          refine ⟨1324169693226915290645645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 882779795484610193763763 1324169693226915290645645)
          ·
            refine ⟨496563634960093233992117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1324169693226915290645645 496563634960093233992117)
            ·
              refine ⟨46552840777508740686761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 496563634960093233992117 46552840777508740686761)
              ·
                rfl

theorem cell19_458973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 5].length) (baseStart_458973 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_458973 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_458973 prefixEnd_458973 := by exact prefixLift 458973
  have htrace : WordTrace (prefixWord ++ tailWord_458973) baseStart_458973 baseEnd_458973 := by
    simpa [prefixWord, tailWord_458973, baseEnd_458973] using wordTrace_append hprefix tailTrace_458973
  have hstable : (prefixWord ++ tailWord_458973).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458973).length < 2 ^ (prefixWord ++ tailWord_458973).sum := by decide
  have hdescent : baseEnd_458973 < baseStart_458973 := by decide
  rcases family_descends (prefixWord ++ tailWord_458973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_458994 : List Nat := [3, 2, 1, 3, 2, 1, 1, 6]
def baseStart_458994 : Nat := 118140960795 + 458994 * 2 ^ 59
def prefixEnd_458994 : Nat := 4983230072969 + 3 ^ 40 * 458994 * 2
def baseEnd_458994 : Nat := 139664912314004395593559

theorem tailTrace_458994 : CollatzResearch.WordTrace tailWord_458994 prefixEnd_458994 139664912314004395593559 := by
  unfold tailWord_458994
  simp only [CollatzResearch.WordTrace]
  refine ⟨4185221624787650694842009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11160590999433735186245357 4185221624787650694842009)
  ·
    refine ⟨3138916218590738021131507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4185221624787650694842009 3138916218590738021131507)
    ·
      refine ⟨4708374327886107031697261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3138916218590738021131507 4708374327886107031697261)
      ·
        refine ⟨1765640372957290136886473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4708374327886107031697261 1765640372957290136886473)
        ·
          refine ⟨1324230279717967602664855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1765640372957290136886473 1324230279717967602664855)
          ·
            refine ⟨1986345419576951403997283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1324230279717967602664855 1986345419576951403997283)
            ·
              refine ⟨2979518129365427105995925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1986345419576951403997283 2979518129365427105995925)
              ·
                refine ⟨139664912314004395593559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2979518129365427105995925 139664912314004395593559)
                ·
                  rfl

theorem cell19_458994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 6].length) (baseStart_458994 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_458994 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_458994 prefixEnd_458994 := by exact prefixLift 458994
  have htrace : WordTrace (prefixWord ++ tailWord_458994) baseStart_458994 baseEnd_458994 := by
    simpa [prefixWord, tailWord_458994, baseEnd_458994] using wordTrace_append hprefix tailTrace_458994
  have hstable : (prefixWord ++ tailWord_458994).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_458994).length < 2 ^ (prefixWord ++ tailWord_458994).sum := by decide
  have hdescent : baseEnd_458994 < baseStart_458994 := by decide
  rcases family_descends (prefixWord ++ tailWord_458994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459034 : List Nat := [3, 1, 1, 3, 11]
def baseStart_459034 : Nat := 118140960795 + 459034 * 2 ^ 59
def prefixEnd_459034 : Nat := 4983230072969 + 3 ^ 40 * 459034 * 2
def baseEnd_459034 : Nat := 5173225322492450174243

theorem tailTrace_459034 : CollatzResearch.WordTrace tailWord_459034 prefixEnd_459034 5173225322492450174243 := by
  unfold tailWord_459034
  simp only [CollatzResearch.WordTrace]
  refine ⟨4185586354751422402706039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11161563612670459740549437 4185586354751422402706039)
  ·
    refine ⟨6278379532127133604059059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4185586354751422402706039 6278379532127133604059059)
    ·
      refine ⟨9417569298190700406088589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6278379532127133604059059 9417569298190700406088589)
      ·
        refine ⟨3531588486821512652283221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9417569298190700406088589 3531588486821512652283221)
        ·
          refine ⟨5173225322492450174243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 3531588486821512652283221 5173225322492450174243)
          ·
            rfl

theorem cell19_459034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 11].length) (baseStart_459034 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_459034 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_459034 prefixEnd_459034 := by exact prefixLift 459034
  have htrace : WordTrace (prefixWord ++ tailWord_459034) baseStart_459034 baseEnd_459034 := by
    simpa [prefixWord, tailWord_459034, baseEnd_459034] using wordTrace_append hprefix tailTrace_459034
  have hstable : (prefixWord ++ tailWord_459034).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459034).length < 2 ^ (prefixWord ++ tailWord_459034).sum := by decide
  have hdescent : baseEnd_459034 < baseStart_459034 := by decide
  rcases family_descends (prefixWord ++ tailWord_459034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459125 : List Nat := [1, 3, 4, 1, 2, 1, 4, 3]
def baseStart_459125 : Nat := 118140960795 + 459125 * 2 ^ 59
def prefixEnd_459125 : Nat := 4983230072969 + 3 ^ 40 * 459125 * 2
def baseEnd_459125 : Nat := 139704773627034906682091

theorem tailTrace_459125 : CollatzResearch.WordTrace tailWord_459125 prefixEnd_459125 139704773627034906682091 := by
  unfold tailWord_459125
  simp only [CollatzResearch.WordTrace]
  refine ⟨16745664461676012152386829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11163776307784008101591219 16745664461676012152386829)
  ·
    refine ⟨6279624173128504557145061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16745664461676012152386829 6279624173128504557145061)
    ·
      refine ⟨1177429532461594604464699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6279624173128504557145061 1177429532461594604464699)
      ·
        refine ⟨1766144298692391906697049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1177429532461594604464699 1766144298692391906697049)
        ·
          refine ⟨1324608224019293930022787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1766144298692391906697049 1324608224019293930022787)
          ·
            refine ⟨1986912336028940895034181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1324608224019293930022787 1986912336028940895034181)
            ·
              refine ⟨372546063005426417818909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1986912336028940895034181 372546063005426417818909)
              ·
                refine ⟨139704773627034906682091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 372546063005426417818909 139704773627034906682091)
                ·
                  rfl

theorem cell19_459125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 4, 3].length) (baseStart_459125 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_459125 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_459125 prefixEnd_459125 := by exact prefixLift 459125
  have htrace : WordTrace (prefixWord ++ tailWord_459125) baseStart_459125 baseEnd_459125 := by
    simpa [prefixWord, tailWord_459125, baseEnd_459125] using wordTrace_append hprefix tailTrace_459125
  have hstable : (prefixWord ++ tailWord_459125).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459125).length < 2 ^ (prefixWord ++ tailWord_459125).sum := by decide
  have hdescent : baseEnd_459125 < baseStart_459125 := by decide
  rcases family_descends (prefixWord ++ tailWord_459125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459148 : List Nat := [2, 2, 1, 2, 1, 4, 7]
def baseStart_459148 : Nat := 118140960795 + 459148 * 2 ^ 59
def prefixEnd_459148 : Nat := 4983230072969 + 3 ^ 40 * 459148 * 2
def baseEnd_459148 : Nat := 46570590726059222723639

theorem tailTrace_459148 : CollatzResearch.WordTrace tailWord_459148 prefixEnd_459148 46570590726059222723639 := by
  unfold tailWord_459148
  simp only [CollatzResearch.WordTrace]
  refine ⟨8373251670296343540237049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11164335560395124720316065 8373251670296343540237049)
  ·
    refine ⟨6279938752722257655177787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8373251670296343540237049 6279938752722257655177787)
    ·
      refine ⟨9419908129083386482766681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6279938752722257655177787 9419908129083386482766681)
      ·
        refine ⟨7064931096812539862075011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9419908129083386482766681 7064931096812539862075011)
        ·
          refine ⟨10597396645218809793112517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7064931096812539862075011 10597396645218809793112517)
          ·
            refine ⟨1987011870978526836208597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10597396645218809793112517 1987011870978526836208597)
            ·
              refine ⟨46570590726059222723639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1987011870978526836208597 46570590726059222723639)
              ·
                rfl

theorem cell19_459148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 7].length) (baseStart_459148 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_459148 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_459148 prefixEnd_459148 := by exact prefixLift 459148
  have htrace : WordTrace (prefixWord ++ tailWord_459148) baseStart_459148 baseEnd_459148 := by
    simpa [prefixWord, tailWord_459148, baseEnd_459148] using wordTrace_append hprefix tailTrace_459148
  have hstable : (prefixWord ++ tailWord_459148).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459148).length < 2 ^ (prefixWord ++ tailWord_459148).sum := by decide
  have hdescent : baseEnd_459148 < baseStart_459148 := by decide
  rcases family_descends (prefixWord ++ tailWord_459148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459186 : List Nat := [3, 2, 1, 1, 1, 1, 3, 7]
def baseStart_459186 : Nat := 118140960795 + 459186 * 2 ^ 59
def prefixEnd_459186 : Nat := 4983230072969 + 3 ^ 40 * 459186 * 2
def baseEnd_459186 : Nat := 139723335001804839326369

theorem tailTrace_459186 : CollatzResearch.WordTrace tailWord_459186 prefixEnd_459186 139723335001804839326369 := by
  unfold tailWord_459186
  simp only [CollatzResearch.WordTrace]
  refine ⟨4186972328613754892589353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11165259542970013046904941 4186972328613754892589353)
  ·
    refine ⟨3140229246460316169442015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4186972328613754892589353 3140229246460316169442015)
    ·
      refine ⟨4710343869690474254163023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3140229246460316169442015 4710343869690474254163023)
      ·
        refine ⟨7065515804535711381244535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4710343869690474254163023 7065515804535711381244535)
        ·
          refine ⟨10598273706803567071866803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7065515804535711381244535 10598273706803567071866803)
          ·
            refine ⟨15897410560205350607800205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10598273706803567071866803 15897410560205350607800205)
            ·
              refine ⟨5961528960077006477925077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15897410560205350607800205 5961528960077006477925077)
              ·
                refine ⟨139723335001804839326369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5961528960077006477925077 139723335001804839326369)
                ·
                  rfl

theorem cell19_459186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 7].length) (baseStart_459186 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_459186 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_459186 prefixEnd_459186 := by exact prefixLift 459186
  have htrace : WordTrace (prefixWord ++ tailWord_459186) baseStart_459186 baseEnd_459186 := by
    simpa [prefixWord, tailWord_459186, baseEnd_459186] using wordTrace_append hprefix tailTrace_459186
  have hstable : (prefixWord ++ tailWord_459186).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459186).length < 2 ^ (prefixWord ++ tailWord_459186).sum := by decide
  have hdescent : baseEnd_459186 < baseStart_459186 := by decide
  rcases family_descends (prefixWord ++ tailWord_459186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459201 : List Nat := [1, 2, 7, 1, 8]
def baseStart_459201 : Nat := 118140960795 + 459201 * 2 ^ 59
def prefixEnd_459201 : Nat := 4983230072969 + 3 ^ 40 * 459201 * 2
def baseEnd_459201 : Nat := 5175107380529231444185

theorem tailTrace_459201 : CollatzResearch.WordTrace tailWord_459201 prefixEnd_459201 5175107380529231444185 := by
  unfold tailWord_459201
  simp only [CollatzResearch.WordTrace]
  refine ⟨16748436409400677132153457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11165624272933784754768971 16748436409400677132153457)
  ·
    refine ⟨12561327307050507849115093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16748436409400677132153457 12561327307050507849115093)
    ·
      refine ⟨294406108758996277713635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 12561327307050507849115093 294406108758996277713635)
      ·
        refine ⟨441609163138494416570453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294406108758996277713635 441609163138494416570453)
        ·
          refine ⟨5175107380529231444185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 441609163138494416570453 5175107380529231444185)
          ·
            rfl

theorem cell19_459201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 8].length) (baseStart_459201 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_459201 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_459201 prefixEnd_459201 := by exact prefixLift 459201
  have htrace : WordTrace (prefixWord ++ tailWord_459201) baseStart_459201 baseEnd_459201 := by
    simpa [prefixWord, tailWord_459201, baseEnd_459201] using wordTrace_append hprefix tailTrace_459201
  have hstable : (prefixWord ++ tailWord_459201).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459201).length < 2 ^ (prefixWord ++ tailWord_459201).sum := by decide
  have hdescent : baseEnd_459201 < baseStart_459201 := by decide
  rcases family_descends (prefixWord ++ tailWord_459201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459218 : List Nat := [3, 2, 2, 4, 1, 2, 1, 4]
def baseStart_459218 : Nat := 118140960795 + 459218 * 2 ^ 59
def prefixEnd_459218 : Nat := 4983230072969 + 3 ^ 40 * 459218 * 2
def baseEnd_459218 : Nat := 139733072116438246615171

theorem tailTrace_459218 : CollatzResearch.WordTrace tailWord_459218 prefixEnd_459218 139733072116438246615171 := by
  unfold tailWord_459218
  simp only [CollatzResearch.WordTrace]
  refine ⟨4187264112584772258880577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11166037633559392690348205 4187264112584772258880577)
  ·
    refine ⟨3140448084438579194160433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4187264112584772258880577 3140448084438579194160433)
    ·
      refine ⟨2355336063328934395620325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3140448084438579194160433 2355336063328934395620325)
      ·
        refine ⟨441625511874175199178811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2355336063328934395620325 441625511874175199178811)
        ·
          refine ⟨662438267811262798768217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 441625511874175199178811 662438267811262798768217)
          ·
            refine ⟨496828700858447099076163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 662438267811262798768217 496828700858447099076163)
            ·
              refine ⟨745243051287670648614245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 496828700858447099076163 745243051287670648614245)
              ·
                refine ⟨139733072116438246615171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 745243051287670648614245 139733072116438246615171)
                ·
                  rfl

theorem cell19_459218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 4].length) (baseStart_459218 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_459218 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_459218 prefixEnd_459218 := by exact prefixLift 459218
  have htrace : WordTrace (prefixWord ++ tailWord_459218) baseStart_459218 baseEnd_459218 := by
    simpa [prefixWord, tailWord_459218, baseEnd_459218] using wordTrace_append hprefix tailTrace_459218
  have hstable : (prefixWord ++ tailWord_459218).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459218).length < 2 ^ (prefixWord ++ tailWord_459218).sum := by decide
  have hdescent : baseEnd_459218 < baseStart_459218 := by decide
  rcases family_descends (prefixWord ++ tailWord_459218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459220 : List Nat := [2, 4, 1, 2, 2, 3, 1, 4]
def baseStart_459220 : Nat := 118140960795 + 459220 * 2 ^ 59
def prefixEnd_459220 : Nat := 4983230072969 + 3 ^ 40 * 459220 * 2
def baseEnd_459220 : Nat := 139733680686102834570721

theorem tailTrace_459220 : CollatzResearch.WordTrace tailWord_459220 prefixEnd_459220 139733680686102834570721 := by
  unfold tailWord_459220
  simp only [CollatzResearch.WordTrace]
  refine ⟨8374564698165921688547557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11166086264221228918063409 8374564698165921688547557)
  ·
    refine ⟨1570230880906110316602667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8374564698165921688547557 1570230880906110316602667)
    ·
      refine ⟨2355346321359165474904001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1570230880906110316602667 2355346321359165474904001)
      ·
        refine ⟨1766509741019374106178001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2355346321359165474904001 1766509741019374106178001)
        ·
          refine ⟨1324882305764530579633501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1766509741019374106178001 1324882305764530579633501)
          ·
            refine ⟨496830864661698967362563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1324882305764530579633501 496830864661698967362563)
            ·
              refine ⟨745246296992548451043845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 496830864661698967362563 745246296992548451043845)
              ·
                refine ⟨139733680686102834570721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 745246296992548451043845 139733680686102834570721)
                ·
                  rfl

theorem cell19_459220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 4].length) (baseStart_459220 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_459220 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_459220 prefixEnd_459220 := by exact prefixLift 459220
  have htrace : WordTrace (prefixWord ++ tailWord_459220) baseStart_459220 baseEnd_459220 := by
    simpa [prefixWord, tailWord_459220, baseEnd_459220] using wordTrace_append hprefix tailTrace_459220
  have hstable : (prefixWord ++ tailWord_459220).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459220).length < 2 ^ (prefixWord ++ tailWord_459220).sum := by decide
  have hdescent : baseEnd_459220 < baseStart_459220 := by decide
  rcases family_descends (prefixWord ++ tailWord_459220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459334 : List Nat := [6, 1, 1, 1, 2, 1, 1, 6]
def baseStart_459334 : Nat := 118140960795 + 459334 * 2 ^ 59
def prefixEnd_459334 : Nat := 4983230072969 + 3 ^ 40 * 459334 * 2
def baseEnd_459334 : Nat := 139768369156984348037077

theorem tailTrace_459334 : CollatzResearch.WordTrace tailWord_459334 prefixEnd_459334 139768369156984348037077 := by
  unfold tailWord_459334
  simp only [CollatzResearch.WordTrace]
  refine ⟨523540228684963776460783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11168858211945893897830037 523540228684963776460783)
  ·
    refine ⟨785310343027445664691175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 523540228684963776460783 785310343027445664691175)
    ·
      refine ⟨1177965514541168497036763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 785310343027445664691175 1177965514541168497036763)
      ·
        refine ⟨1766948271811752745555145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1177965514541168497036763 1766948271811752745555145)
        ·
          refine ⟨1325211203858814559166359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1766948271811752745555145 1325211203858814559166359)
          ·
            refine ⟨1987816805788221838749539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1325211203858814559166359 1987816805788221838749539)
            ·
              refine ⟨2981725208682332758124309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1987816805788221838749539 2981725208682332758124309)
              ·
                refine ⟨139768369156984348037077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2981725208682332758124309 139768369156984348037077)
                ·
                  rfl

theorem cell19_459334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_459334 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_459334 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_459334 prefixEnd_459334 := by exact prefixLift 459334
  have htrace : WordTrace (prefixWord ++ tailWord_459334) baseStart_459334 baseEnd_459334 := by
    simpa [prefixWord, tailWord_459334, baseEnd_459334] using wordTrace_append hprefix tailTrace_459334
  have hstable : (prefixWord ++ tailWord_459334).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459334).length < 2 ^ (prefixWord ++ tailWord_459334).sum := by decide
  have hdescent : baseEnd_459334 < baseStart_459334 := by decide
  rcases family_descends (prefixWord ++ tailWord_459334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459338 : List Nat := [3, 1, 2, 1, 1, 4, 1, 6]
def baseStart_459338 : Nat := 118140960795 + 459338 * 2 ^ 59
def prefixEnd_459338 : Nat := 4983230072969 + 3 ^ 40 * 459338 * 2
def baseEnd_459338 : Nat := 139769586296313523948177

theorem tailTrace_459338 : CollatzResearch.WordTrace tailWord_459338 prefixEnd_459338 139769586296313523948177 := by
  unfold tailWord_459338
  simp only [CollatzResearch.WordTrace]
  refine ⟨4188358302476087382472667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11168955473269566353260445 4188358302476087382472667)
  ·
    refine ⟨6282537453714131073709001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4188358302476087382472667 6282537453714131073709001)
    ·
      refine ⟨4711903090285598305281751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6282537453714131073709001 4711903090285598305281751)
      ·
        refine ⟨7067854635428397457922627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4711903090285598305281751 7067854635428397457922627)
        ·
          refine ⟨10601781953142596186883941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7067854635428397457922627 10601781953142596186883941)
          ·
            refine ⟨1987834116214236785040739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10601781953142596186883941 1987834116214236785040739)
            ·
              refine ⟨2981751174321355177561109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1987834116214236785040739 2981751174321355177561109)
              ·
                refine ⟨139769586296313523948177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2981751174321355177561109 139769586296313523948177)
                ·
                  rfl

theorem cell19_459338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 6].length) (baseStart_459338 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_459338 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_459338 prefixEnd_459338 := by exact prefixLift 459338
  have htrace : WordTrace (prefixWord ++ tailWord_459338) baseStart_459338 baseEnd_459338 := by
    simpa [prefixWord, tailWord_459338, baseEnd_459338] using wordTrace_append hprefix tailTrace_459338
  have hstable : (prefixWord ++ tailWord_459338).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459338).length < 2 ^ (prefixWord ++ tailWord_459338).sum := by decide
  have hdescent : baseEnd_459338 < baseStart_459338 := by decide
  rcases family_descends (prefixWord ++ tailWord_459338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459376 : List Nat := [2, 1, 1, 1, 7, 7]
def baseStart_459376 : Nat := 118140960795 + 459376 * 2 ^ 59
def prefixEnd_459376 : Nat := 4983230072969 + 3 ^ 40 * 459376 * 2
def baseEnd_459376 : Nat := 15531238791104521678181

theorem tailTrace_459376 : CollatzResearch.WordTrace tailWord_459376 prefixEnd_459376 15531238791104521678181 := by
  unfold tailWord_459376
  simp only [CollatzResearch.WordTrace]
  refine ⟨8377409591883341009886991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11169879455844454679849321 8377409591883341009886991)
  ·
    refine ⟨12566114387825011514830487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8377409591883341009886991 12566114387825011514830487)
    ·
      refine ⟨18849171581737517272245731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12566114387825011514830487 18849171581737517272245731)
      ·
        refine ⟨28273757372606275908368597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18849171581737517272245731 28273757372606275908368597)
        ·
          refine ⟨662666188420459591602389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 28273757372606275908368597 662666188420459591602389)
          ·
            refine ⟨15531238791104521678181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 662666188420459591602389 15531238791104521678181)
            ·
              rfl

theorem cell19_459376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 7].length) (baseStart_459376 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_459376 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_459376 prefixEnd_459376 := by exact prefixLift 459376
  have htrace : WordTrace (prefixWord ++ tailWord_459376) baseStart_459376 baseEnd_459376 := by
    simpa [prefixWord, tailWord_459376, baseEnd_459376] using wordTrace_append hprefix tailTrace_459376
  have hstable : (prefixWord ++ tailWord_459376).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459376).length < 2 ^ (prefixWord ++ tailWord_459376).sum := by decide
  have hdescent : baseEnd_459376 < baseStart_459376 := by decide
  rcases family_descends (prefixWord ++ tailWord_459376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459395 : List Nat := [1, 1, 1, 3, 3, 1, 5, 4]
def baseStart_459395 : Nat := 118140960795 + 459395 * 2 ^ 59
def prefixEnd_459395 : Nat := 4983230072969 + 3 ^ 40 * 459395 * 2
def baseEnd_459395 : Nat := 139786930531754280681355

theorem tailTrace_459395 : CollatzResearch.WordTrace tailWord_459395 prefixEnd_459395 139786930531754280681355 := by
  unfold tailWord_459395
  simp only [CollatzResearch.WordTrace]
  refine ⟨16755512170697848264715639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11170341447131898843143759 16755512170697848264715639)
  ·
    refine ⟨25133268256046772397073459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16755512170697848264715639 25133268256046772397073459)
    ·
      refine ⟨37699902384070158595610189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25133268256046772397073459 37699902384070158595610189)
      ·
        refine ⟨14137463394026309473353821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37699902384070158595610189 14137463394026309473353821)
        ·
          refine ⟨5301548772759866052507683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14137463394026309473353821 5301548772759866052507683)
          ·
            refine ⟨7952323159139799078761525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5301548772759866052507683 7952323159139799078761525)
            ·
              refine ⟨745530296169356163633893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7952323159139799078761525 745530296169356163633893)
              ·
                refine ⟨139786930531754280681355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 745530296169356163633893 139786930531754280681355)
                ·
                  rfl

theorem cell19_459395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 4].length) (baseStart_459395 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_459395 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_459395 prefixEnd_459395 := by exact prefixLift 459395
  have htrace : WordTrace (prefixWord ++ tailWord_459395) baseStart_459395 baseEnd_459395 := by
    simpa [prefixWord, tailWord_459395, baseEnd_459395] using wordTrace_append hprefix tailTrace_459395
  have hstable : (prefixWord ++ tailWord_459395).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459395).length < 2 ^ (prefixWord ++ tailWord_459395).sum := by decide
  have hdescent : baseEnd_459395 < baseStart_459395 := by decide
  rcases family_descends (prefixWord ++ tailWord_459395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459410 : List Nat := [3, 2, 3, 1, 2, 2, 3, 3]
def baseStart_459410 : Nat := 118140960795 + 459410 * 2 ^ 59
def prefixEnd_459410 : Nat := 4983230072969 + 3 ^ 40 * 459410 * 2
def baseEnd_459410 : Nat := 139791494804238690347981

theorem tailTrace_459410 : CollatzResearch.WordTrace tailWord_459410 prefixEnd_459410 139791494804238690347981 := by
  unfold tailWord_459410
  simp only [CollatzResearch.WordTrace]
  refine ⟨4189014816410876456627921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11170706177095670551007789 4189014816410876456627921)
  ·
    refine ⟨3141761112308157342470941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4189014816410876456627921 3141761112308157342470941)
    ·
      refine ⟨1178160417115559003426603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3141761112308157342470941 1178160417115559003426603)
      ·
        refine ⟨1767240625673338505139905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1178160417115559003426603 1767240625673338505139905)
        ·
          refine ⟨1325430469255003878854929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1767240625673338505139905 1325430469255003878854929)
          ·
            refine ⟨994072851941252909141197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1325430469255003878854929 994072851941252909141197)
            ·
              refine ⟨372777319477969840927949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 994072851941252909141197 372777319477969840927949)
              ·
                refine ⟨139791494804238690347981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 372777319477969840927949 139791494804238690347981)
                ·
                  rfl

theorem cell19_459410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 3, 3].length) (baseStart_459410 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_459410 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_459410 prefixEnd_459410 := by exact prefixLift 459410
  have htrace : WordTrace (prefixWord ++ tailWord_459410) baseStart_459410 baseEnd_459410 := by
    simpa [prefixWord, tailWord_459410, baseEnd_459410] using wordTrace_append hprefix tailTrace_459410
  have hstable : (prefixWord ++ tailWord_459410).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459410).length < 2 ^ (prefixWord ++ tailWord_459410).sum := by decide
  have hdescent : baseEnd_459410 < baseStart_459410 := by decide
  rcases family_descends (prefixWord ++ tailWord_459410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459452 : List Nat := [2, 2, 2, 3, 1, 1, 2, 6]
def baseStart_459452 : Nat := 118140960795 + 459452 * 2 ^ 59
def prefixEnd_459452 : Nat := 4983230072969 + 3 ^ 40 * 459452 * 2
def baseEnd_459452 : Nat := 139804274767195037414533

theorem tailTrace_459452 : CollatzResearch.WordTrace tailWord_459452 prefixEnd_459452 139804274767195037414533 := by
  unfold tailWord_459452
  simp only [CollatzResearch.WordTrace]
  refine ⟨8378795565745673499770305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11171727420994231333027073 8378795565745673499770305)
  ·
    refine ⟨6284096674309255124827729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8378795565745673499770305 6284096674309255124827729)
    ·
      refine ⟨4713072505731941343620797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6284096674309255124827729 4713072505731941343620797)
      ·
        refine ⟨1767402189649478003857799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4713072505731941343620797 1767402189649478003857799)
        ·
          refine ⟨2651103284474217005786699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1767402189649478003857799 2651103284474217005786699)
          ·
            refine ⟨3976654926711325508680049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2651103284474217005786699 3976654926711325508680049)
            ·
              refine ⟨2982491195033494131510037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3976654926711325508680049 2982491195033494131510037)
              ·
                refine ⟨139804274767195037414533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2982491195033494131510037 139804274767195037414533)
                ·
                  rfl

theorem cell19_459452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 6].length) (baseStart_459452 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_459452 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_459452 prefixEnd_459452 := by exact prefixLift 459452
  have htrace : WordTrace (prefixWord ++ tailWord_459452) baseStart_459452 baseEnd_459452 := by
    simpa [prefixWord, tailWord_459452, baseEnd_459452] using wordTrace_append hprefix tailTrace_459452
  have hstable : (prefixWord ++ tailWord_459452).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459452).length < 2 ^ (prefixWord ++ tailWord_459452).sum := by decide
  have hdescent : baseEnd_459452 < baseStart_459452 := by decide
  rcases family_descends (prefixWord ++ tailWord_459452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459528 : List Nat := [2, 1, 3, 2, 2, 2, 2, 5]
def baseStart_459528 : Nat := 118140960795 + 459528 * 2 ^ 59
def prefixEnd_459528 : Nat := 4983230072969 + 3 ^ 40 * 459528 * 2
def baseEnd_459528 : Nat := 139827400414449379725437

theorem tailTrace_459528 : CollatzResearch.WordTrace tailWord_459528 prefixEnd_459528 139827400414449379725437 := by
  unfold tailWord_459528
  simp only [CollatzResearch.WordTrace]
  refine ⟨8380181539608005989653619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11173575386144007986204825 8380181539608005989653619)
  ·
    refine ⟨12570272309412008984480429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8380181539608005989653619 12570272309412008984480429)
    ·
      refine ⟨4713852116029503369180161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12570272309412008984480429 4713852116029503369180161)
      ·
        refine ⟨3535389087022127526885121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4713852116029503369180161 3535389087022127526885121)
        ·
          refine ⟨2651541815266595645163841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3535389087022127526885121 2651541815266595645163841)
          ·
            refine ⟨1988656361449946733872881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2651541815266595645163841 1988656361449946733872881)
            ·
              refine ⟨1491492271087460050404661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1988656361449946733872881 1491492271087460050404661)
              ·
                refine ⟨139827400414449379725437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1491492271087460050404661 139827400414449379725437)
                ·
                  rfl

theorem cell19_459528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 5].length) (baseStart_459528 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_459528 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_459528 prefixEnd_459528 := by exact prefixLift 459528
  have htrace : WordTrace (prefixWord ++ tailWord_459528) baseStart_459528 baseEnd_459528 := by
    simpa [prefixWord, tailWord_459528, baseEnd_459528] using wordTrace_append hprefix tailTrace_459528
  have hstable : (prefixWord ++ tailWord_459528).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459528).length < 2 ^ (prefixWord ++ tailWord_459528).sum := by decide
  have hdescent : baseEnd_459528 < baseStart_459528 := by decide
  rcases family_descends (prefixWord ++ tailWord_459528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459581 : List Nat := [1, 4, 1, 4, 2, 1, 3, 3]
def baseStart_459581 : Nat := 118140960795 + 459581 * 2 ^ 59
def prefixEnd_459581 : Nat := 4983230072969 + 3 ^ 40 * 459581 * 2
def baseEnd_459581 : Nat := 139843527510560960547515

theorem tailTrace_459581 : CollatzResearch.WordTrace tailWord_459581 prefixEnd_459581 139843527510560960547515 := by
  unfold tailWord_459581
  simp only [CollatzResearch.WordTrace]
  refine ⟨16762296148024002030986597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11174864098682668020657731 16762296148024002030986597)
  ·
    refine ⟨3142930527754500380809987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16762296148024002030986597 3142930527754500380809987)
    ·
      refine ⟨4714395791631750571214981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3142930527754500380809987 4714395791631750571214981)
      ·
        refine ⟨883949210930953232102809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4714395791631750571214981 883949210930953232102809)
        ·
          refine ⟨662961908198214924077107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 883949210930953232102809 662961908198214924077107)
          ·
            refine ⟨994442862297322386115661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 662961908198214924077107 994442862297322386115661)
            ·
              refine ⟨372916073361495894793373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 994442862297322386115661 372916073361495894793373)
              ·
                refine ⟨139843527510560960547515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 372916073361495894793373 139843527510560960547515)
                ·
                  rfl

theorem cell19_459581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 3, 3].length) (baseStart_459581 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_459581 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_459581 prefixEnd_459581 := by exact prefixLift 459581
  have htrace : WordTrace (prefixWord ++ tailWord_459581) baseStart_459581 baseEnd_459581 := by
    simpa [prefixWord, tailWord_459581, baseEnd_459581] using wordTrace_append hprefix tailTrace_459581
  have hstable : (prefixWord ++ tailWord_459581).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459581).length < 2 ^ (prefixWord ++ tailWord_459581).sum := by decide
  have hdescent : baseEnd_459581 < baseStart_459581 := by decide
  rcases family_descends (prefixWord ++ tailWord_459581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459583 : List Nat := [1, 1, 2, 2, 5, 2, 3, 3]
def baseStart_459583 : Nat := 118140960795 + 459583 * 2 ^ 59
def prefixEnd_459583 : Nat := 4983230072969 + 3 ^ 40 * 459583 * 2
def baseEnd_459583 : Nat := 139844136080225548503065

theorem tailTrace_459583 : CollatzResearch.WordTrace tailWord_459583 prefixEnd_459583 139844136080225548503065 := by
  unfold tailWord_459583
  simp only [CollatzResearch.WordTrace]
  refine ⟨16762369094016756372559403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11174912729344504248372935 16762369094016756372559403)
  ·
    refine ⟨25143553641025134558839105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16762369094016756372559403 25143553641025134558839105)
    ·
      refine ⟨18857665230768850919129329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25143553641025134558839105 18857665230768850919129329)
      ·
        refine ⟨14143248923076638189346997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18857665230768850919129329 14143248923076638189346997)
        ·
          refine ⟨1325929586538434830251281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14143248923076638189346997 1325929586538434830251281)
          ·
            refine ⟨994447189903826122688461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1325929586538434830251281 994447189903826122688461)
            ·
              refine ⟨372917696213934796008173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 994447189903826122688461 372917696213934796008173)
              ·
                refine ⟨139844136080225548503065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 372917696213934796008173 139844136080225548503065)
                ·
                  rfl

theorem cell19_459583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 3, 3].length) (baseStart_459583 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_459583 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_459583 prefixEnd_459583 := by exact prefixLift 459583
  have htrace : WordTrace (prefixWord ++ tailWord_459583) baseStart_459583 baseEnd_459583 := by
    simpa [prefixWord, tailWord_459583, baseEnd_459583] using wordTrace_append hprefix tailTrace_459583
  have hstable : (prefixWord ++ tailWord_459583).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459583).length < 2 ^ (prefixWord ++ tailWord_459583).sum := by decide
  have hdescent : baseEnd_459583 < baseStart_459583 := by decide
  rcases family_descends (prefixWord ++ tailWord_459583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459638 : List Nat := [5, 1, 1, 3, 1, 1, 4, 3]
def baseStart_459638 : Nat := 118140960795 + 459638 * 2 ^ 59
def prefixEnd_459638 : Nat := 4983230072969 + 3 ^ 40 * 459638 * 2
def baseEnd_459638 : Nat := 139860871746001717280693

theorem tailTrace_459638 : CollatzResearch.WordTrace tailWord_459638 prefixEnd_459638 139860871746001717280693 := by
  unfold tailWord_459638
  simp only [CollatzResearch.WordTrace]
  refine ⟨1047773444301093797863223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11176250072545000510541045 1047773444301093797863223)
  ·
    refine ⟨1571660166451640696794835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1047773444301093797863223 1571660166451640696794835)
    ·
      refine ⟨2357490249677461045192253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1571660166451640696794835 2357490249677461045192253)
      ·
        refine ⟨884058843629047891947095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2357490249677461045192253 884058843629047891947095)
        ·
          refine ⟨1326088265443571837920643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 884058843629047891947095 1326088265443571837920643)
          ·
            refine ⟨1989132398165357756880965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1326088265443571837920643 1989132398165357756880965)
            ·
              refine ⟨372962324656004579415181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1989132398165357756880965 372962324656004579415181)
              ·
                refine ⟨139860871746001717280693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 372962324656004579415181 139860871746001717280693)
                ·
                  rfl

theorem cell19_459638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_459638 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_459638 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_459638 prefixEnd_459638 := by exact prefixLift 459638
  have htrace : WordTrace (prefixWord ++ tailWord_459638) baseStart_459638 baseEnd_459638 := by
    simpa [prefixWord, tailWord_459638, baseEnd_459638] using wordTrace_append hprefix tailTrace_459638
  have hstable : (prefixWord ++ tailWord_459638).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459638).length < 2 ^ (prefixWord ++ tailWord_459638).sum := by decide
  have hdescent : baseEnd_459638 < baseStart_459638 := by decide
  rcases family_descends (prefixWord ++ tailWord_459638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459716 : List Nat := [2, 3, 3, 3, 1, 7]
def baseStart_459716 : Nat := 118140960795 + 459716 * 2 ^ 59
def prefixEnd_459716 : Nat := 4983230072969 + 3 ^ 40 * 459716 * 2
def baseEnd_459716 : Nat := 15542733995880071949683

theorem tailTrace_459716 : CollatzResearch.WordTrace tailWord_459716 prefixEnd_459716 15542733995880071949683 := by
  unfold tailWord_459716
  simp only [CollatzResearch.WordTrace]
  refine ⟨8383610001267460043575501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11178146668356613391434001 8383610001267460043575501)
  ·
    refine ⟨3143853750475297516340813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8383610001267460043575501 3143853750475297516340813)
    ·
      refine ⟨1178945156428236568627805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3143853750475297516340813 1178945156428236568627805)
      ·
        refine ⟨442104433660588713235427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1178945156428236568627805 442104433660588713235427)
        ·
          refine ⟨663156650490883069853141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 442104433660588713235427 663156650490883069853141)
          ·
            refine ⟨15542733995880071949683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 663156650490883069853141 15542733995880071949683)
            ·
              rfl

theorem cell19_459716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 7].length) (baseStart_459716 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_459716 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_459716 prefixEnd_459716 := by exact prefixLift 459716
  have htrace : WordTrace (prefixWord ++ tailWord_459716) baseStart_459716 baseEnd_459716 := by
    simpa [prefixWord, tailWord_459716, baseEnd_459716] using wordTrace_append hprefix tailTrace_459716
  have hstable : (prefixWord ++ tailWord_459716).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459716).length < 2 ^ (prefixWord ++ tailWord_459716).sum := by decide
  have hdescent : baseEnd_459716 < baseStart_459716 := by decide
  rcases family_descends (prefixWord ++ tailWord_459716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459720 : List Nat := [2, 1, 3, 1, 12]
def baseStart_459720 : Nat := 118140960795 + 459720 * 2 ^ 59
def prefixEnd_459720 : Nat := 4983230072969 + 3 ^ 40 * 459720 * 2
def baseEnd_459720 : Nat := 5180956411194437905861

theorem tailTrace_459720 : CollatzResearch.WordTrace tailWord_459720 prefixEnd_459720 5180956411194437905861 := by
  unfold tailWord_459720
  simp only [CollatzResearch.WordTrace]
  refine ⟨8383682947260214385148307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11178243929680285846864409 8383682947260214385148307)
  ·
    refine ⟨12575524420890321577722461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8383682947260214385148307 12575524420890321577722461)
    ·
      refine ⟨4715821657833870591645923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12575524420890321577722461 4715821657833870591645923)
      ·
        refine ⟨7073732486750805887468885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4715821657833870591645923 7073732486750805887468885)
        ·
          refine ⟨5180956411194437905861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 7073732486750805887468885 5180956411194437905861)
          ·
            rfl

theorem cell19_459720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 12].length) (baseStart_459720 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_459720 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_459720 prefixEnd_459720 := by exact prefixLift 459720
  have htrace : WordTrace (prefixWord ++ tailWord_459720) baseStart_459720 baseEnd_459720 := by
    simpa [prefixWord, tailWord_459720, baseEnd_459720] using wordTrace_append hprefix tailTrace_459720
  have hstable : (prefixWord ++ tailWord_459720).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459720).length < 2 ^ (prefixWord ++ tailWord_459720).sum := by decide
  have hdescent : baseEnd_459720 < baseStart_459720 := by decide
  rcases family_descends (prefixWord ++ tailWord_459720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459733 : List Nat := [1, 3, 2, 3, 4, 1, 1, 4]
def baseStart_459733 : Nat := 118140960795 + 459733 * 2 ^ 59
def prefixEnd_459733 : Nat := 4983230072969 + 3 ^ 40 * 459733 * 2
def baseEnd_459733 : Nat := 139889778805069645169323

theorem tailTrace_459733 : CollatzResearch.WordTrace tailWord_459733 prefixEnd_459733 139889778805069645169323 := by
  unfold tailWord_459733
  simp only [CollatzResearch.WordTrace]
  refine ⟨16767840043473331990519853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11178560028982221327013235 16767840043473331990519853)
  ·
    refine ⟨6287940016302499496444945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16767840043473331990519853 6287940016302499496444945)
    ·
      refine ⟨4715955012226874622333709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6287940016302499496444945 4715955012226874622333709)
      ·
        refine ⟨1768483129585077983375141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4715955012226874622333709 1768483129585077983375141)
        ·
          refine ⟨331590586797202121882839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1768483129585077983375141 331590586797202121882839)
          ·
            refine ⟨497385880195803182824259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 331590586797202121882839 497385880195803182824259)
            ·
              refine ⟨746078820293704774236389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 497385880195803182824259 746078820293704774236389)
              ·
                refine ⟨139889778805069645169323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 746078820293704774236389 139889778805069645169323)
                ·
                  rfl

theorem cell19_459733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 4].length) (baseStart_459733 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_459733 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_459733 prefixEnd_459733 := by exact prefixLift 459733
  have htrace : WordTrace (prefixWord ++ tailWord_459733) baseStart_459733 baseEnd_459733 := by
    simpa [prefixWord, tailWord_459733, baseEnd_459733] using wordTrace_append hprefix tailTrace_459733
  have hstable : (prefixWord ++ tailWord_459733).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459733).length < 2 ^ (prefixWord ++ tailWord_459733).sum := by decide
  have hdescent : baseEnd_459733 < baseStart_459733 := by decide
  rcases family_descends (prefixWord ++ tailWord_459733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459737 : List Nat := [1, 2, 1, 2, 5, 1, 3, 4]
def baseStart_459737 : Nat := 118140960795 + 459737 * 2 ^ 59
def prefixEnd_459737 : Nat := 4983230072969 + 3 ^ 40 * 459737 * 2
def baseEnd_459737 : Nat := 139890995944398821080423

theorem tailTrace_459737 : CollatzResearch.WordTrace tailWord_459737 prefixEnd_459737 139890995944398821080423 := by
  unfold tailWord_459737
  simp only [CollatzResearch.WordTrace]
  refine ⟨16767985935458840673665465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11178657290305893782443643 16767985935458840673665465)
  ·
    refine ⟨12575989451594130505249099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16767985935458840673665465 12575989451594130505249099)
    ·
      refine ⟨18863984177391195757873649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12575989451594130505249099 18863984177391195757873649)
      ·
        refine ⟨14147988133043396818405237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18863984177391195757873649 14147988133043396818405237)
        ·
          refine ⟨1326373887472818451725491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14147988133043396818405237 1326373887472818451725491)
          ·
            refine ⟨1989560831209227677588237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1326373887472818451725491 1989560831209227677588237)
            ·
              refine ⟨746085311703460379095589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1989560831209227677588237 746085311703460379095589)
              ·
                refine ⟨139890995944398821080423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 746085311703460379095589 139890995944398821080423)
                ·
                  rfl

theorem cell19_459737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 4].length) (baseStart_459737 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_459737 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_459737 prefixEnd_459737 := by exact prefixLift 459737
  have htrace : WordTrace (prefixWord ++ tailWord_459737) baseStart_459737 baseEnd_459737 := by
    simpa [prefixWord, tailWord_459737, baseEnd_459737] using wordTrace_append hprefix tailTrace_459737
  have hstable : (prefixWord ++ tailWord_459737).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459737).length < 2 ^ (prefixWord ++ tailWord_459737).sum := by decide
  have hdescent : baseEnd_459737 < baseStart_459737 := by decide
  rcases family_descends (prefixWord ++ tailWord_459737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459754 : List Nat := [3, 1, 3, 1, 2, 3, 3, 3]
def baseStart_459754 : Nat := 118140960795 + 459754 * 2 ^ 59
def prefixEnd_459754 : Nat := 4983230072969 + 3 ^ 40 * 459754 * 2
def baseEnd_459754 : Nat := 139896168786547818702599

theorem tailTrace_459754 : CollatzResearch.WordTrace tailWord_459754 prefixEnd_459754 139896168786547818702599 := by
  unfold tailWord_459754
  simp only [CollatzResearch.WordTrace]
  refine ⟨4192151494099313144258579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11179070650931501718022877 4192151494099313144258579)
  ·
    refine ⟨6288227241148969716387869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4192151494099313144258579 6288227241148969716387869)
    ·
      refine ⟨2358085215430863643645451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6288227241148969716387869 2358085215430863643645451)
      ·
        refine ⟨3537127823146295465468177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2358085215430863643645451 3537127823146295465468177)
        ·
          refine ⟨2652845867359721599101133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3537127823146295465468177 2652845867359721599101133)
          ·
            refine ⟨994817200259895599662925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2652845867359721599101133 994817200259895599662925)
            ·
              refine ⟨373056450097460849873597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 994817200259895599662925 373056450097460849873597)
              ·
                refine ⟨139896168786547818702599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 373056450097460849873597 139896168786547818702599)
                ·
                  rfl

theorem cell19_459754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 3, 3].length) (baseStart_459754 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_459754 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_459754 prefixEnd_459754 := by exact prefixLift 459754
  have htrace : WordTrace (prefixWord ++ tailWord_459754) baseStart_459754 baseEnd_459754 := by
    simpa [prefixWord, tailWord_459754, baseEnd_459754] using wordTrace_append hprefix tailTrace_459754
  have hstable : (prefixWord ++ tailWord_459754).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459754).length < 2 ^ (prefixWord ++ tailWord_459754).sum := by decide
  have hdescent : baseEnd_459754 < baseStart_459754 := by decide
  rcases family_descends (prefixWord ++ tailWord_459754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459811 : List Nat := [1, 1, 1, 4, 3, 4, 2, 3]
def baseStart_459811 : Nat := 118140960795 + 459811 * 2 ^ 59
def prefixEnd_459811 : Nat := 4983230072969 + 3 ^ 40 * 459811 * 2
def baseEnd_459811 : Nat := 139913513021988575435777

theorem tailTrace_459811 : CollatzResearch.WordTrace tailWord_459811 prefixEnd_459811 139913513021988575435777 := by
  unfold tailWord_459811
  simp only [CollatzResearch.WordTrace]
  refine ⟨16770684937190751311859287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11180456624793834207906191 16770684937190751311859287)
  ·
    refine ⟨25156027405786126967788931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16770684937190751311859287 25156027405786126967788931)
    ·
      refine ⟨37734041108679190451683397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25156027405786126967788931 37734041108679190451683397)
      ·
        refine ⟨7075132707877348209690637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37734041108679190451683397 7075132707877348209690637)
        ·
          refine ⟨2653174765454005578633989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7075132707877348209690637 2653174765454005578633989)
          ·
            refine ⟨497470268522626045993873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2653174765454005578633989 497470268522626045993873)
            ·
              refine ⟨373102701391969534495405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 497470268522626045993873 373102701391969534495405)
              ·
                refine ⟨139913513021988575435777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 373102701391969534495405 139913513021988575435777)
                ·
                  rfl

theorem cell19_459811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 2, 3].length) (baseStart_459811 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_459811 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_459811 prefixEnd_459811 := by exact prefixLift 459811
  have htrace : WordTrace (prefixWord ++ tailWord_459811) baseStart_459811 baseEnd_459811 := by
    simpa [prefixWord, tailWord_459811, baseEnd_459811] using wordTrace_append hprefix tailTrace_459811
  have hstable : (prefixWord ++ tailWord_459811).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459811).length < 2 ^ (prefixWord ++ tailWord_459811).sum := by decide
  have hdescent : baseEnd_459811 < baseStart_459811 := by decide
  rcases family_descends (prefixWord ++ tailWord_459811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459830 : List Nat := [5, 1, 2, 1, 1, 4, 5]
def baseStart_459830 : Nat := 118140960795 + 459830 * 2 ^ 59
def prefixEnd_459830 : Nat := 4983230072969 + 3 ^ 40 * 459830 * 2
def baseEnd_459830 : Nat := 46639764811267387004501

theorem tailTrace_459830 : CollatzResearch.WordTrace tailWord_459830 prefixEnd_459830 46639764811267387004501 := by
  unfold tailWord_459830
  simp only [CollatzResearch.WordTrace]
  refine ⟨1048211120257619847300059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11180918616081278371200629 1048211120257619847300059)
  ·
    refine ⟨1572316680386429770950089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1048211120257619847300059 1572316680386429770950089)
    ·
      refine ⟨1179237510289822328212567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1572316680386429770950089 1179237510289822328212567)
      ·
        refine ⟨1768856265434733492318851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1179237510289822328212567 1768856265434733492318851)
        ·
          refine ⟨2653284398152100238478277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1768856265434733492318851 2653284398152100238478277)
          ·
            refine ⟨497490824653518794714677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2653284398152100238478277 497490824653518794714677)
            ·
              refine ⟨46639764811267387004501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 497490824653518794714677 46639764811267387004501)
              ·
                rfl

theorem cell19_459830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 5].length) (baseStart_459830 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_459830 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_459830 prefixEnd_459830 := by exact prefixLift 459830
  have htrace : WordTrace (prefixWord ++ tailWord_459830) baseStart_459830 baseEnd_459830 := by
    simpa [prefixWord, tailWord_459830, baseEnd_459830] using wordTrace_append hprefix tailTrace_459830
  have hstable : (prefixWord ++ tailWord_459830).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459830).length < 2 ^ (prefixWord ++ tailWord_459830).sum := by decide
  have hdescent : baseEnd_459830 < baseStart_459830 := by decide
  rcases family_descends (prefixWord ++ tailWord_459830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459832 : List Nat := [2, 1, 2, 1, 5, 3, 5]
def baseStart_459832 : Nat := 118140960795 + 459832 * 2 ^ 59
def prefixEnd_459832 : Nat := 4983230072969 + 3 ^ 40 * 459832 * 2
def baseEnd_459832 : Nat := 46639967667822249656351

theorem tailTrace_459832 : CollatzResearch.WordTrace tailWord_459832 prefixEnd_459832 46639967667822249656351 := by
  unfold tailWord_459832
  simp only [CollatzResearch.WordTrace]
  refine ⟨8385725435057335949186875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11180967246743114598915833 8385725435057335949186875)
  ·
    refine ⟨12578588152586003923780313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8385725435057335949186875 12578588152586003923780313)
    ·
      refine ⟨9433941114439502942835235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12578588152586003923780313 9433941114439502942835235)
      ·
        refine ⟨14150911671659254414252853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9433941114439502942835235 14150911671659254414252853)
        ·
          refine ⟨1326647969218055101336205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14150911671659254414252853 1326647969218055101336205)
          ·
            refine ⟨497492988456770663001077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1326647969218055101336205 497492988456770663001077)
            ·
              refine ⟨46639967667822249656351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 497492988456770663001077 46639967667822249656351)
              ·
                rfl

theorem cell19_459832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 5].length) (baseStart_459832 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_459832 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_459832 prefixEnd_459832 := by exact prefixLift 459832
  have htrace : WordTrace (prefixWord ++ tailWord_459832) baseStart_459832 baseEnd_459832 := by
    simpa [prefixWord, tailWord_459832, baseEnd_459832] using wordTrace_append hprefix tailTrace_459832
  have hstable : (prefixWord ++ tailWord_459832).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459832).length < 2 ^ (prefixWord ++ tailWord_459832).sum := by decide
  have hdescent : baseEnd_459832 < baseStart_459832 := by decide
  rcases family_descends (prefixWord ++ tailWord_459832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459834 : List Nat := [3, 1, 1, 1, 3, 1, 9]
def baseStart_459834 : Nat := 118140960795 + 459834 * 2 ^ 59
def prefixEnd_459834 : Nat := 4983230072969 + 3 ^ 40 * 459834 * 2
def baseEnd_459834 : Nat := 46640170524377112308201

theorem tailTrace_459834 : CollatzResearch.WordTrace tailWord_459834 prefixEnd_459834 46640170524377112308201 := by
  unfold tailWord_459834
  simp only [CollatzResearch.WordTrace]
  refine ⟨4192880954026856559986639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11181015877404950826631037 4192880954026856559986639)
  ·
    refine ⟨6289321431040284839979959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4192880954026856559986639 6289321431040284839979959)
    ·
      refine ⟨9433982146560427259969939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6289321431040284839979959 9433982146560427259969939)
      ·
        refine ⟨14150973219840640889954909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9433982146560427259969939 14150973219840640889954909)
        ·
          refine ⟨5306614957440240333733091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14150973219840640889954909 5306614957440240333733091)
          ·
            refine ⟨7959922436160360500599637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5306614957440240333733091 7959922436160360500599637)
            ·
              refine ⟨46640170524377112308201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7959922436160360500599637 46640170524377112308201)
              ·
                rfl

theorem cell19_459834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 9].length) (baseStart_459834 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_459834 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_459834 prefixEnd_459834 := by exact prefixLift 459834
  have htrace : WordTrace (prefixWord ++ tailWord_459834) baseStart_459834 baseEnd_459834 := by
    simpa [prefixWord, tailWord_459834, baseEnd_459834] using wordTrace_append hprefix tailTrace_459834
  have hstable : (prefixWord ++ tailWord_459834).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459834).length < 2 ^ (prefixWord ++ tailWord_459834).sum := by decide
  have hdescent : baseEnd_459834 < baseStart_459834 := by decide
  rcases family_descends (prefixWord ++ tailWord_459834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459872 : List Nat := [2, 1, 1, 3, 2, 2, 1, 7]
def baseStart_459872 : Nat := 118140960795 + 459872 * 2 ^ 59
def prefixEnd_459872 : Nat := 4983230072969 + 3 ^ 40 * 459872 * 2
def baseEnd_459872 : Nat := 139932074396758508080055

theorem tailTrace_459872 : CollatzResearch.WordTrace tailWord_459872 prefixEnd_459872 139932074396758508080055 := by
  unfold tailWord_459872
  simp only [CollatzResearch.WordTrace]
  refine ⟨8386454894984879364914935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11181939859979839153219913 8386454894984879364914935)
  ·
    refine ⟨12579682342477319047372403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8386454894984879364914935 12579682342477319047372403)
    ·
      refine ⟨18869523513715978571058605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12579682342477319047372403 18869523513715978571058605)
      ·
        refine ⟨7076071317643491964146977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18869523513715978571058605 7076071317643491964146977)
        ·
          refine ⟨5307053488232618973110233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7076071317643491964146977 5307053488232618973110233)
          ·
            refine ⟨3980290116174464229832675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5307053488232618973110233 3980290116174464229832675)
            ·
              refine ⟨5970435174261696344749013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3980290116174464229832675 5970435174261696344749013)
              ·
                refine ⟨139932074396758508080055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5970435174261696344749013 139932074396758508080055)
                ·
                  rfl

theorem cell19_459872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 7].length) (baseStart_459872 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_459872 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_459872 prefixEnd_459872 := by exact prefixLift 459872
  have htrace : WordTrace (prefixWord ++ tailWord_459872) baseStart_459872 baseEnd_459872 := by
    simpa [prefixWord, tailWord_459872, baseEnd_459872] using wordTrace_append hprefix tailTrace_459872
  have hstable : (prefixWord ++ tailWord_459872).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459872).length < 2 ^ (prefixWord ++ tailWord_459872).sum := by decide
  have hdescent : baseEnd_459872 < baseStart_459872 := by decide
  rcases family_descends (prefixWord ++ tailWord_459872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459908 : List Nat := [2, 3, 2, 1, 2, 2, 3, 4]
def baseStart_459908 : Nat := 118140960795 + 459908 * 2 ^ 59
def prefixEnd_459908 : Nat := 4983230072969 + 3 ^ 40 * 459908 * 2
def baseEnd_459908 : Nat := 139943028650721091279957

theorem tailTrace_459908 : CollatzResearch.WordTrace tailWord_459908 prefixEnd_459908 139943028650721091279957 := by
  unfold tailWord_459908
  simp only [CollatzResearch.WordTrace]
  refine ⟨8387111408919668439070189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11182815211892891252093585 8387111408919668439070189)
  ·
    refine ⟨3145166778344875664651321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8387111408919668439070189 3145166778344875664651321)
    ·
      refine ⟨2358875083758656748488491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3145166778344875664651321 2358875083758656748488491)
      ·
        refine ⟨3538312625637985122732737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2358875083758656748488491 3538312625637985122732737)
        ·
          refine ⟨2653734469228488842049553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3538312625637985122732737 2653734469228488842049553)
          ·
            refine ⟨1990300851921366631537165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2653734469228488842049553 1990300851921366631537165)
            ·
              refine ⟨746362819470512486826437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1990300851921366631537165 746362819470512486826437)
              ·
                refine ⟨139943028650721091279957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 746362819470512486826437 139943028650721091279957)
                ·
                  rfl

theorem cell19_459908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 4].length) (baseStart_459908 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_459908 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_459908 prefixEnd_459908 := by exact prefixLift 459908
  have htrace : WordTrace (prefixWord ++ tailWord_459908) baseStart_459908 baseEnd_459908 := by
    simpa [prefixWord, tailWord_459908, baseEnd_459908] using wordTrace_append hprefix tailTrace_459908
  have hstable : (prefixWord ++ tailWord_459908).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459908).length < 2 ^ (prefixWord ++ tailWord_459908).sum := by decide
  have hdescent : baseEnd_459908 < baseStart_459908 := by decide
  rcases family_descends (prefixWord ++ tailWord_459908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_459974 : List Nat := [6, 1, 2, 2, 2, 1, 2, 3]
def baseStart_459974 : Nat := 118140960795 + 459974 * 2 ^ 59
def prefixEnd_459974 : Nat := 4983230072969 + 3 ^ 40 * 459974 * 2
def baseEnd_459974 : Nat := 139963111449652493813111

theorem tailTrace_459974 : CollatzResearch.WordTrace tailWord_459974 prefixEnd_459974 139963111449652493813111 := by
  unfold tailWord_459974
  simp only [CollatzResearch.WordTrace]
  refine ⟨524269688612507192188843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 11184420023733486766695317 524269688612507192188843)
  ·
    refine ⟨786404532918760788283265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 524269688612507192188843 786404532918760788283265)
    ·
      refine ⟨589803399689070591212449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 786404532918760788283265 589803399689070591212449)
      ·
        refine ⟨442352549766802943409337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 589803399689070591212449 442352549766802943409337)
        ·
          refine ⟨331764412325102207557003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 442352549766802943409337 331764412325102207557003)
          ·
            refine ⟨497646618487653311335505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 331764412325102207557003 497646618487653311335505)
            ·
              refine ⟨373234963865739983501629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 497646618487653311335505 373234963865739983501629)
              ·
                refine ⟨139963111449652493813111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 373234963865739983501629 139963111449652493813111)
                ·
                  rfl

theorem cell19_459974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_459974 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_459974 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_459974 prefixEnd_459974 := by exact prefixLift 459974
  have htrace : WordTrace (prefixWord ++ tailWord_459974) baseStart_459974 baseEnd_459974 := by
    simpa [prefixWord, tailWord_459974, baseEnd_459974] using wordTrace_append hprefix tailTrace_459974
  have hstable : (prefixWord ++ tailWord_459974).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_459974).length < 2 ^ (prefixWord ++ tailWord_459974).sum := by decide
  have hdescent : baseEnd_459974 < baseStart_459974 := by decide
  rcases family_descends (prefixWord ++ tailWord_459974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460043 : List Nat := [1, 1, 1, 1, 5, 3, 2, 5]
def baseStart_460043 : Nat := 118140960795 + 460043 * 2 ^ 59
def prefixEnd_460043 : Nat := 4983230072969 + 3 ^ 40 * 460043 * 2
def baseEnd_460043 : Nat := 139984107103080778279589

theorem tailTrace_460043 : CollatzResearch.WordTrace tailWord_460043 prefixEnd_460043 139984107103080778279589 := by
  unfold tailWord_460043
  simp only [CollatzResearch.WordTrace]
  refine ⟨16779146672350254934304783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11186097781566836622869855 16779146672350254934304783)
  ·
    refine ⟨25168720008525382401457175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16779146672350254934304783 25168720008525382401457175)
    ·
      refine ⟨37753080012788073602185763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25168720008525382401457175 37753080012788073602185763)
      ·
        refine ⟨56629620019182110403278645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37753080012788073602185763 56629620019182110403278645)
        ·
          refine ⟨5309026876798322850307373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56629620019182110403278645 5309026876798322850307373)
          ·
            refine ⟨1990885078799371068865265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5309026876798322850307373 1990885078799371068865265)
            ·
              refine ⟨1493163809099528301648949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1990885078799371068865265 1493163809099528301648949)
              ·
                refine ⟨139984107103080778279589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1493163809099528301648949 139984107103080778279589)
                ·
                  rfl

theorem cell19_460043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 5].length) (baseStart_460043 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_460043 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_460043 prefixEnd_460043 := by exact prefixLift 460043
  have htrace : WordTrace (prefixWord ++ tailWord_460043) baseStart_460043 baseEnd_460043 := by
    simpa [prefixWord, tailWord_460043, baseEnd_460043] using wordTrace_append hprefix tailTrace_460043
  have hstable : (prefixWord ++ tailWord_460043).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460043).length < 2 ^ (prefixWord ++ tailWord_460043).sum := by decide
  have hdescent : baseEnd_460043 < baseStart_460043 := by decide
  rcases family_descends (prefixWord ++ tailWord_460043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460077 : List Nat := [1, 5, 3, 1, 1, 1, 3, 4]
def baseStart_460077 : Nat := 118140960795 + 460077 * 2 ^ 59
def prefixEnd_460077 : Nat := 4983230072969 + 3 ^ 40 * 460077 * 2
def baseEnd_460077 : Nat := 139994452787378773523941

theorem tailTrace_460077 : CollatzResearch.WordTrace tailWord_460077 prefixEnd_460077 139994452787378773523941 := by
  unfold tailWord_460077
  simp only [CollatzResearch.WordTrace]
  refine ⟨16780386754227078741042485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11186924502818052494028323 16780386754227078741042485)
  ·
    refine ⟨1573161258208788631972733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16780386754227078741042485 1573161258208788631972733)
    ·
      refine ⟨589935471828295736989775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1573161258208788631972733 589935471828295736989775)
      ·
        refine ⟨884903207742443605484663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 589935471828295736989775 884903207742443605484663)
        ·
          refine ⟨1327354811613665408226995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 884903207742443605484663 1327354811613665408226995)
          ·
            refine ⟨1991032217420498112340493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1327354811613665408226995 1991032217420498112340493)
            ·
              refine ⟨746637081532686792127685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1991032217420498112340493 746637081532686792127685)
              ·
                refine ⟨139994452787378773523941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 746637081532686792127685 139994452787378773523941)
                ·
                  rfl

theorem cell19_460077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 4].length) (baseStart_460077 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_460077 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_460077 prefixEnd_460077 := by exact prefixLift 460077
  have htrace : WordTrace (prefixWord ++ tailWord_460077) baseStart_460077 baseEnd_460077 := by
    simpa [prefixWord, tailWord_460077, baseEnd_460077] using wordTrace_append hprefix tailTrace_460077
  have hstable : (prefixWord ++ tailWord_460077).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460077).length < 2 ^ (prefixWord ++ tailWord_460077).sum := by decide
  have hdescent : baseEnd_460077 < baseStart_460077 := by decide
  rcases family_descends (prefixWord ++ tailWord_460077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460119 : List Nat := [1, 1, 3, 2, 3, 3, 6]
def baseStart_460119 : Nat := 118140960795 + 460119 * 2 ^ 59
def prefixEnd_460119 : Nat := 4983230072969 + 3 ^ 40 * 460119 * 2
def baseEnd_460119 : Nat := 46669077583445040196831

theorem tailTrace_460119 : CollatzResearch.WordTrace tailWord_460119 prefixEnd_460119 46669077583445040196831 := by
  unfold tailWord_460119
  simp only [CollatzResearch.WordTrace]
  refine ⟨16781918620074919914071411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11187945746716613276047607 16781918620074919914071411)
  ·
    refine ⟨25172877930112379871107117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16781918620074919914071411 25172877930112379871107117)
    ·
      refine ⟨9439829223792142451665169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25172877930112379871107117 9439829223792142451665169)
      ·
        refine ⟨7079871917844106838748877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9439829223792142451665169 7079871917844106838748877)
        ·
          refine ⟨2654951969191540064530829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7079871917844106838748877 2654951969191540064530829)
          ·
            refine ⟨995606988446827524199061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2654951969191540064530829 995606988446827524199061)
            ·
              refine ⟨46669077583445040196831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 995606988446827524199061 46669077583445040196831)
              ·
                rfl

theorem cell19_460119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 6].length) (baseStart_460119 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_460119 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_460119 prefixEnd_460119 := by exact prefixLift 460119
  have htrace : WordTrace (prefixWord ++ tailWord_460119) baseStart_460119 baseEnd_460119 := by
    simpa [prefixWord, tailWord_460119, baseEnd_460119] using wordTrace_append hprefix tailTrace_460119
  have hstable : (prefixWord ++ tailWord_460119).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460119).length < 2 ^ (prefixWord ++ tailWord_460119).sum := by decide
  have hdescent : baseEnd_460119 < baseStart_460119 := by decide
  rcases family_descends (prefixWord ++ tailWord_460119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460157 : List Nat := [1, 4, 1, 1, 2, 2, 3, 5]
def baseStart_460157 : Nat := 118140960795 + 460157 * 2 ^ 59
def prefixEnd_460157 : Nat := 4983230072969 + 3 ^ 40 * 460157 * 2
def baseEnd_460157 : Nat := 140018795573962291745945

theorem tailTrace_460157 : CollatzResearch.WordTrace tailWord_460157 prefixEnd_460157 140018795573962291745945 := by
  unfold tailWord_460157
  simp only [CollatzResearch.WordTrace]
  refine ⟨16783304593937252403954725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11188869729291501602636483 16783304593937252403954725)
  ·
    refine ⟨3146869611363234825741511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16783304593937252403954725 3146869611363234825741511)
    ·
      refine ⟨4720304417044852238612267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3146869611363234825741511 4720304417044852238612267)
      ·
        refine ⟨7080456625567278357918401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4720304417044852238612267 7080456625567278357918401)
        ·
          refine ⟨5310342469175458768438801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7080456625567278357918401 5310342469175458768438801)
          ·
            refine ⟨3982756851881594076329101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5310342469175458768438801 3982756851881594076329101)
            ·
              refine ⟨1493533819455597778623413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3982756851881594076329101 1493533819455597778623413)
              ·
                refine ⟨140018795573962291745945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1493533819455597778623413 140018795573962291745945)
                ·
                  rfl

theorem cell19_460157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 5].length) (baseStart_460157 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_460157 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_460157 prefixEnd_460157 := by exact prefixLift 460157
  have htrace : WordTrace (prefixWord ++ tailWord_460157) baseStart_460157 baseEnd_460157 := by
    simpa [prefixWord, tailWord_460157, baseEnd_460157] using wordTrace_append hprefix tailTrace_460157
  have hstable : (prefixWord ++ tailWord_460157).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460157).length < 2 ^ (prefixWord ++ tailWord_460157).sum := by decide
  have hdescent : baseEnd_460157 < baseStart_460157 := by decide
  rcases family_descends (prefixWord ++ tailWord_460157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460195 : List Nat := [1, 1, 1, 4, 1, 3, 4, 4]
def baseStart_460195 : Nat := 118140960795 + 460195 * 2 ^ 59
def prefixEnd_460195 : Nat := 4983230072969 + 3 ^ 40 * 460195 * 2
def baseEnd_460195 : Nat := 140030358397589462901397

theorem tailTrace_460195 : CollatzResearch.WordTrace tailWord_460195 prefixEnd_460195 140030358397589462901397 := by
  unfold tailWord_460195
  simp only [CollatzResearch.WordTrace]
  refine ⟨16784690567799584893838039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11189793711866389929225359 16784690567799584893838039)
  ·
    refine ⟨25177035851699377340757059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16784690567799584893838039 25177035851699377340757059)
    ·
      refine ⟨37765553777549066011135589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25177035851699377340757059 37765553777549066011135589)
      ·
        refine ⟨7081041333290449877087923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37765553777549066011135589 7081041333290449877087923)
        ·
          refine ⟨10621561999935674815631885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7081041333290449877087923 10621561999935674815631885)
          ·
            refine ⟨3983085749975878055861957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10621561999935674815631885 3983085749975878055861957)
            ·
              refine ⟨746828578120477135474117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3983085749975878055861957 746828578120477135474117)
              ·
                refine ⟨140030358397589462901397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 746828578120477135474117 140030358397589462901397)
                ·
                  rfl

theorem cell19_460195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 4].length) (baseStart_460195 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_460195 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_460195 prefixEnd_460195 := by exact prefixLift 460195
  have htrace : WordTrace (prefixWord ++ tailWord_460195) baseStart_460195 baseEnd_460195 := by
    simpa [prefixWord, tailWord_460195, baseEnd_460195] using wordTrace_append hprefix tailTrace_460195
  have hstable : (prefixWord ++ tailWord_460195).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460195).length < 2 ^ (prefixWord ++ tailWord_460195).sum := by decide
  have hdescent : baseEnd_460195 < baseStart_460195 := by decide
  rcases family_descends (prefixWord ++ tailWord_460195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460250 : List Nat := [3, 1, 1, 2, 3, 4, 1, 4]
def baseStart_460250 : Nat := 118140960795 + 460250 * 2 ^ 59
def prefixEnd_460250 : Nat := 4983230072969 + 3 ^ 40 * 460250 * 2
def baseEnd_460250 : Nat := 140047094063365631679025

theorem tailTrace_460250 : CollatzResearch.WordTrace tailWord_460250 prefixEnd_460250 140047094063365631679025 := by
  unfold tailWord_460250
  simp only [CollatzResearch.WordTrace]
  refine ⟨4196674145650082321772551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11191131055066886191393469 4196674145650082321772551)
  ·
    refine ⟨6295011218475123482658827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4196674145650082321772551 6295011218475123482658827)
    ·
      refine ⟨9442516827712685223988241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6295011218475123482658827 9442516827712685223988241)
      ·
        refine ⟨7081887620784513917991181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9442516827712685223988241 7081887620784513917991181)
        ·
          refine ⟨2655707857794192719246693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7081887620784513917991181 2655707857794192719246693)
          ·
            refine ⟨497945223336411134858755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2655707857794192719246693 497945223336411134858755)
            ·
              refine ⟨746917835004616702288133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 497945223336411134858755 746917835004616702288133)
              ·
                refine ⟨140047094063365631679025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 746917835004616702288133 140047094063365631679025)
                ·
                  rfl

theorem cell19_460250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 4].length) (baseStart_460250 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_460250 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_460250 prefixEnd_460250 := by exact prefixLift 460250
  have htrace : WordTrace (prefixWord ++ tailWord_460250) baseStart_460250 baseEnd_460250 := by
    simpa [prefixWord, tailWord_460250, baseEnd_460250] using wordTrace_append hprefix tailTrace_460250
  have hstable : (prefixWord ++ tailWord_460250).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460250).length < 2 ^ (prefixWord ++ tailWord_460250).sum := by decide
  have hdescent : baseEnd_460250 < baseStart_460250 := by decide
  rcases family_descends (prefixWord ++ tailWord_460250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460286 : List Nat := [4, 2, 2, 3, 1, 1, 6]
def baseStart_460286 : Nat := 118140960795 + 460286 * 2 ^ 59
def prefixEnd_460286 : Nat := 4983230072969 + 3 ^ 40 * 460286 * 2
def baseEnd_460286 : Nat := 46686016105776071626309

theorem tailTrace_460286 : CollatzResearch.WordTrace tailWord_460286 prefixEnd_460286 46686016105776071626309 := by
  unfold tailWord_460286
  simp only [CollatzResearch.WordTrace]
  refine ⟨2098501201308738429425089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11192006406979938290267141 2098501201308738429425089)
  ·
    refine ⟨1573875900981553822068817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2098501201308738429425089 1573875900981553822068817)
    ·
      refine ⟨1180406925736165366551613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1573875900981553822068817 1180406925736165366551613)
      ·
        refine ⟨442652597151062012456855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1180406925736165366551613 442652597151062012456855)
        ·
          refine ⟨663978895726593018685283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 442652597151062012456855 663978895726593018685283)
          ·
            refine ⟨995968343589889528027925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 663978895726593018685283 995968343589889528027925)
            ·
              refine ⟨46686016105776071626309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 995968343589889528027925 46686016105776071626309)
              ·
                rfl

theorem cell19_460286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 6].length) (baseStart_460286 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_460286 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_460286 prefixEnd_460286 := by exact prefixLift 460286
  have htrace : WordTrace (prefixWord ++ tailWord_460286) baseStart_460286 baseEnd_460286 := by
    simpa [prefixWord, tailWord_460286, baseEnd_460286] using wordTrace_append hprefix tailTrace_460286
  have hstable : (prefixWord ++ tailWord_460286).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460286).length < 2 ^ (prefixWord ++ tailWord_460286).sum := by decide
  have hdescent : baseEnd_460286 < baseStart_460286 := by decide
  rcases family_descends (prefixWord ++ tailWord_460286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460318 : List Nat := [4, 3, 3, 1, 1, 2, 2, 3]
def baseStart_460318 : Nat := 118140960795 + 460318 * 2 ^ 59
def prefixEnd_460318 : Nat := 4983230072969 + 3 ^ 40 * 460318 * 2
def baseEnd_460318 : Nat := 140067785431961622167729

theorem tailTrace_460318 : CollatzResearch.WordTrace tailWord_460318 prefixEnd_460318 140067785431961622167729 := by
  unfold tailWord_460318
  simp only [CollatzResearch.WordTrace]
  refine ⟨2098647093294247112570701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11192784497569317933710405 2098647093294247112570701)
  ·
    refine ⟨786992659985342667214013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2098647093294247112570701 786992659985342667214013)
    ·
      refine ⟨295122247494503500205255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 786992659985342667214013 295122247494503500205255)
      ·
        refine ⟨442683371241755250307883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295122247494503500205255 442683371241755250307883)
        ·
          refine ⟨664025056862632875461825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 442683371241755250307883 664025056862632875461825)
          ·
            refine ⟨498018792646974656596369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 664025056862632875461825 498018792646974656596369)
            ·
              refine ⟨373514094485230992447277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 498018792646974656596369 373514094485230992447277)
              ·
                refine ⟨140067785431961622167729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 373514094485230992447277 140067785431961622167729)
                ·
                  rfl

theorem cell19_460318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 2, 3].length) (baseStart_460318 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_460318 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_460318 prefixEnd_460318 := by exact prefixLift 460318
  have htrace : WordTrace (prefixWord ++ tailWord_460318) baseStart_460318 baseEnd_460318 := by
    simpa [prefixWord, tailWord_460318, baseEnd_460318] using wordTrace_append hprefix tailTrace_460318
  have hstable : (prefixWord ++ tailWord_460318).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460318).length < 2 ^ (prefixWord ++ tailWord_460318).sum := by decide
  have hdescent : baseEnd_460318 < baseStart_460318 := by decide
  rcases family_descends (prefixWord ++ tailWord_460318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460423 : List Nat := [1, 1, 4, 2, 1, 3, 3, 4]
def baseStart_460423 : Nat := 118140960795 + 460423 * 2 ^ 59
def prefixEnd_460423 : Nat := 4983230072969 + 3 ^ 40 * 460423 * 2
def baseEnd_460423 : Nat := 140099735339352489834109

theorem tailTrace_460423 : CollatzResearch.WordTrace tailWord_460423 prefixEnd_460423 140099735339352489834109 := by
  unfold tailWord_460423
  simp only [CollatzResearch.WordTrace]
  refine ⟨16793006410973579833137923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11195337607315719888758615 16793006410973579833137923)
  ·
    refine ⟨25189509616460369749706885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16793006410973579833137923 25189509616460369749706885)
    ·
      refine ⟨4723033053086319328070041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25189509616460369749706885 4723033053086319328070041)
      ·
        refine ⟨3542274789814739496052531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4723033053086319328070041 3542274789814739496052531)
        ·
          refine ⟨5313412184722109244078797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3542274789814739496052531 5313412184722109244078797)
          ·
            refine ⟨1992529569270790966529549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5313412184722109244078797 1992529569270790966529549)
            ·
              refine ⟨747198588476546612448581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1992529569270790966529549 747198588476546612448581)
              ·
                refine ⟨140099735339352489834109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 747198588476546612448581 140099735339352489834109)
                ·
                  rfl

theorem cell19_460423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 4].length) (baseStart_460423 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_460423 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_460423 prefixEnd_460423 := by exact prefixLift 460423
  have htrace : WordTrace (prefixWord ++ tailWord_460423) baseStart_460423 baseEnd_460423 := by
    simpa [prefixWord, tailWord_460423, baseEnd_460423] using wordTrace_append hprefix tailTrace_460423
  have hstable : (prefixWord ++ tailWord_460423).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460423).length < 2 ^ (prefixWord ++ tailWord_460423).sum := by decide
  have hdescent : baseEnd_460423 < baseStart_460423 := by decide
  rcases family_descends (prefixWord ++ tailWord_460423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460440 : List Nat := [2, 1, 2, 4, 1, 3, 3, 3]
def baseStart_460440 : Nat := 118140960795 + 460440 * 2 ^ 59
def prefixEnd_460440 : Nat := 4983230072969 + 3 ^ 40 * 460440 * 2
def baseEnd_460440 : Nat := 140104908181501487456285

theorem tailTrace_460440 : CollatzResearch.WordTrace tailWord_460440 prefixEnd_460440 140104908181501487456285 := by
  unfold tailWord_460440
  simp only [CollatzResearch.WordTrace]
  refine ⟨8396813225955995868253387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11195750967941327824337849 8396813225955995868253387)
  ·
    refine ⟨12595219838933993802380081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8396813225955995868253387 12595219838933993802380081)
    ·
      refine ⟨9446414879200495351785061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12595219838933993802380081 9446414879200495351785061)
      ·
        refine ⟨1771202789850092878459699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9446414879200495351785061 1771202789850092878459699)
        ·
          refine ⟨2656804184775139317689549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1771202789850092878459699 2656804184775139317689549)
          ·
            refine ⟨996301569290677244133581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2656804184775139317689549 996301569290677244133581)
            ·
              refine ⟨373613088484003966550093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 996301569290677244133581 373613088484003966550093)
              ·
                refine ⟨140104908181501487456285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 373613088484003966550093 140104908181501487456285)
                ·
                  rfl

theorem cell19_460440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 3, 3].length) (baseStart_460440 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_460440 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_460440 prefixEnd_460440 := by exact prefixLift 460440
  have htrace : WordTrace (prefixWord ++ tailWord_460440) baseStart_460440 baseEnd_460440 := by
    simpa [prefixWord, tailWord_460440, baseEnd_460440] using wordTrace_append hprefix tailTrace_460440
  have hstable : (prefixWord ++ tailWord_460440).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460440).length < 2 ^ (prefixWord ++ tailWord_460440).sum := by decide
  have hdescent : baseEnd_460440 < baseStart_460440 := by decide
  rcases family_descends (prefixWord ++ tailWord_460440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460461 : List Nat := [1, 5, 2, 1, 1, 1, 8]
def baseStart_460461 : Nat := 118140960795 + 460461 * 2 ^ 59
def prefixEnd_460461 : Nat := 4983230072969 + 3 ^ 40 * 460461 * 2
def baseEnd_460461 : Nat := 46703766054326553663187

theorem tailTrace_460461 : CollatzResearch.WordTrace tailWord_460461 prefixEnd_460461 46703766054326553663187 := by
  unfold tailWord_460461
  simp only [CollatzResearch.WordTrace]
  refine ⟨16794392384835912323021237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11196261589890608215347491 16794392384835912323021237)
  ·
    refine ⟨1574474286078366780283241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16794392384835912323021237 1574474286078366780283241)
    ·
      refine ⟨1180855714558775085212431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1574474286078366780283241 1180855714558775085212431)
      ·
        refine ⟨1771283571838162627818647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1180855714558775085212431 1771283571838162627818647)
        ·
          refine ⟨2656925357757243941727971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1771283571838162627818647 2656925357757243941727971)
          ·
            refine ⟨3985388036635865912591957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2656925357757243941727971 3985388036635865912591957)
            ·
              refine ⟨46703766054326553663187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3985388036635865912591957 46703766054326553663187)
              ·
                rfl

theorem cell19_460461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 8].length) (baseStart_460461 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_460461 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_460461 prefixEnd_460461 := by exact prefixLift 460461
  have htrace : WordTrace (prefixWord ++ tailWord_460461) baseStart_460461 baseEnd_460461 := by
    simpa [prefixWord, tailWord_460461, baseEnd_460461] using wordTrace_append hprefix tailTrace_460461
  have hstable : (prefixWord ++ tailWord_460461).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460461).length < 2 ^ (prefixWord ++ tailWord_460461).sum := by decide
  have hdescent : baseEnd_460461 < baseStart_460461 := by decide
  rcases family_descends (prefixWord ++ tailWord_460461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460463 : List Nat := [1, 1, 2, 1, 2, 4, 8]
def baseStart_460463 : Nat := 118140960795 + 460463 * 2 ^ 59
def prefixEnd_460463 : Nat := 4983230072969 + 3 ^ 40 * 460463 * 2
def baseEnd_460463 : Nat := 46703968910881416315037

theorem tailTrace_460463 : CollatzResearch.WordTrace tailWord_460463 prefixEnd_460463 46703968910881416315037 := by
  unfold tailWord_460463
  simp only [CollatzResearch.WordTrace]
  refine ⟨16794465330828666664594043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11196310220552444443062695 16794465330828666664594043)
  ·
    refine ⟨25191697996242999996891065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16794465330828666664594043 25191697996242999996891065)
    ·
      refine ⟨18893773497182249997668299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25191697996242999996891065 18893773497182249997668299)
      ·
        refine ⟨28340660245773374996502449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18893773497182249997668299 28340660245773374996502449)
        ·
          refine ⟨21255495184330031247376837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28340660245773374996502449 21255495184330031247376837)
          ·
            refine ⟨3985405347061880858883157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21255495184330031247376837 3985405347061880858883157)
            ·
              refine ⟨46703968910881416315037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3985405347061880858883157 46703968910881416315037)
              ·
                rfl

theorem cell19_460463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 8].length) (baseStart_460463 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_460463 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_460463 prefixEnd_460463 := by exact prefixLift 460463
  have htrace : WordTrace (prefixWord ++ tailWord_460463) baseStart_460463 baseEnd_460463 := by
    simpa [prefixWord, tailWord_460463, baseEnd_460463] using wordTrace_append hprefix tailTrace_460463
  have hstable : (prefixWord ++ tailWord_460463).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460463).length < 2 ^ (prefixWord ++ tailWord_460463).sum := by decide
  have hdescent : baseEnd_460463 < baseStart_460463 := by decide
  rcases family_descends (prefixWord ++ tailWord_460463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460493 : List Nat := [1, 6, 2, 1, 1, 3, 2, 3]
def baseStart_460493 : Nat := 118140960795 + 460493 * 2 ^ 59
def prefixEnd_460493 : Nat := 4983230072969 + 3 ^ 40 * 460493 * 2
def baseEnd_460493 : Nat := 140121035277613068278363

theorem tailTrace_460493 : CollatzResearch.WordTrace tailWord_460493 prefixEnd_460493 140121035277613068278363 := by
  unfold tailWord_460493
  simp only [CollatzResearch.WordTrace]
  refine ⟨16795559520719981788186133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11197039680479987858790755 16795559520719981788186133)
  ·
    refine ⟨787291852533749146321225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 16795559520719981788186133 787291852533749146321225)
    ·
      refine ⟨590468889400311859740919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 787291852533749146321225 590468889400311859740919)
      ·
        refine ⟨885703334100467789611379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 590468889400311859740919 885703334100467789611379)
        ·
          refine ⟨1328555001150701684417069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 885703334100467789611379 1328555001150701684417069)
          ·
            refine ⟨498208125431513131656401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1328555001150701684417069 498208125431513131656401)
            ·
              refine ⟨373656094073634848742301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 498208125431513131656401 373656094073634848742301)
              ·
                refine ⟨140121035277613068278363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 373656094073634848742301 140121035277613068278363)
                ·
                  rfl

theorem cell19_460493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 2, 3].length) (baseStart_460493 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_460493 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_460493 prefixEnd_460493 := by exact prefixLift 460493
  have htrace : WordTrace (prefixWord ++ tailWord_460493) baseStart_460493 baseEnd_460493 := by
    simpa [prefixWord, tailWord_460493, baseEnd_460493] using wordTrace_append hprefix tailTrace_460493
  have hstable : (prefixWord ++ tailWord_460493).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460493).length < 2 ^ (prefixWord ++ tailWord_460493).sum := by decide
  have hdescent : baseEnd_460493 < baseStart_460493 := by decide
  rcases family_descends (prefixWord ++ tailWord_460493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460497 : List Nat := [1, 2, 2, 1, 2, 6, 2, 3]
def baseStart_460497 : Nat := 118140960795 + 460497 * 2 ^ 59
def prefixEnd_460497 : Nat := 4983230072969 + 3 ^ 40 * 460497 * 2
def baseEnd_460497 : Nat := 140122252416942244189463

theorem tailTrace_460497 : CollatzResearch.WordTrace tailWord_460497 prefixEnd_460497 140122252416942244189463 := by
  unfold tailWord_460497
  simp only [CollatzResearch.WordTrace]
  refine ⟨16795705412705490471331745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11197136941803660314221163 16795705412705490471331745)
  ·
    refine ⟨12596779059529117853498809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16795705412705490471331745 12596779059529117853498809)
    ·
      refine ⟨9447584294646838390124107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12596779059529117853498809 9447584294646838390124107)
      ·
        refine ⟨14171376441970257585186161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9447584294646838390124107 14171376441970257585186161)
        ·
          refine ⟨10628532331477693188889621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14171376441970257585186161 10628532331477693188889621)
          ·
            refine ⟨498212453038016868229201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 10628532331477693188889621 498212453038016868229201)
            ·
              refine ⟨373659339778512651171901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 498212453038016868229201 373659339778512651171901)
              ·
                refine ⟨140122252416942244189463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 373659339778512651171901 140122252416942244189463)
                ·
                  rfl

theorem cell19_460497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 2, 3].length) (baseStart_460497 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_460497 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_460497 prefixEnd_460497 := by exact prefixLift 460497
  have htrace : WordTrace (prefixWord ++ tailWord_460497) baseStart_460497 baseEnd_460497 := by
    simpa [prefixWord, tailWord_460497, baseEnd_460497] using wordTrace_append hprefix tailTrace_460497
  have hstable : (prefixWord ++ tailWord_460497).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460497).length < 2 ^ (prefixWord ++ tailWord_460497).sum := by decide
  have hdescent : baseEnd_460497 < baseStart_460497 := by decide
  rcases family_descends (prefixWord ++ tailWord_460497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460577 : List Nat := [1, 2, 3, 2, 1, 10]
def baseStart_460577 : Nat := 118140960795 + 460577 * 2 ^ 59
def prefixEnd_460577 : Nat := 4983230072969 + 3 ^ 40 * 460577 * 2
def baseEnd_460577 : Nat := 15571843911502862490163

theorem tailTrace_460577 : CollatzResearch.WordTrace tailWord_460577 prefixEnd_460577 15571843911502862490163 := by
  unfold tailWord_460577
  simp only [CollatzResearch.WordTrace]
  refine ⟨16798623252415664134243985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11199082168277109422829323 16798623252415664134243985)
  ·
    refine ⟨12598967439311748100682989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16798623252415664134243985 12598967439311748100682989)
    ·
      refine ⟨4724612789741905537756121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12598967439311748100682989 4724612789741905537756121)
      ·
        refine ⟨3543459592306429153317091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4724612789741905537756121 3543459592306429153317091)
        ·
          refine ⟨5315189388459643729975637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3543459592306429153317091 5315189388459643729975637)
          ·
            refine ⟨15571843911502862490163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5315189388459643729975637 15571843911502862490163)
            ·
              rfl

theorem cell19_460577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 10].length) (baseStart_460577 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_460577 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_460577 prefixEnd_460577 := by exact prefixLift 460577
  have htrace : WordTrace (prefixWord ++ tailWord_460577) baseStart_460577 baseEnd_460577 := by
    simpa [prefixWord, tailWord_460577, baseEnd_460577] using wordTrace_append hprefix tailTrace_460577
  have hstable : (prefixWord ++ tailWord_460577).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460577).length < 2 ^ (prefixWord ++ tailWord_460577).sum := by decide
  have hdescent : baseEnd_460577 < baseStart_460577 := by decide
  rcases family_descends (prefixWord ++ tailWord_460577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460590 : List Nat := [4, 1, 3, 2, 2, 2, 1, 4]
def baseStart_460590 : Nat := 118140960795 + 460590 * 2 ^ 59
def prefixEnd_460590 : Nat := 4983230072969 + 3 ^ 40 * 460590 * 2
def baseEnd_460590 : Nat := 140150550906345584122543

theorem tailTrace_460590 : CollatzResearch.WordTrace tailWord_460590 prefixEnd_460590 140150550906345584122543 := by
  unfold tailWord_460590
  simp only [CollatzResearch.WordTrace]
  refine ⟨2099887175171070919308403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11199398267579044902978149 2099887175171070919308403)
  ·
    refine ⟨3149830762756606378962605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2099887175171070919308403 3149830762756606378962605)
    ·
      refine ⟨1181186536033727392110977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3149830762756606378962605 1181186536033727392110977)
      ·
        refine ⟨885889902025295544083233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1181186536033727392110977 885889902025295544083233)
        ·
          refine ⟨664417426518971658062425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 885889902025295544083233 664417426518971658062425)
          ·
            refine ⟨498313069889228743546819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 664417426518971658062425 498313069889228743546819)
            ·
              refine ⟨747469604833843115320229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 498313069889228743546819 747469604833843115320229)
              ·
                refine ⟨140150550906345584122543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 747469604833843115320229 140150550906345584122543)
                ·
                  rfl

theorem cell19_460590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_460590 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_460590 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_460590 prefixEnd_460590 := by exact prefixLift 460590
  have htrace : WordTrace (prefixWord ++ tailWord_460590) baseStart_460590 baseEnd_460590 := by
    simpa [prefixWord, tailWord_460590, baseEnd_460590] using wordTrace_append hprefix tailTrace_460590
  have hstable : (prefixWord ++ tailWord_460590).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460590).length < 2 ^ (prefixWord ++ tailWord_460590).sum := by decide
  have hdescent : baseEnd_460590 < baseStart_460590 := by decide
  rcases family_descends (prefixWord ++ tailWord_460590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460594 : List Nat := [3, 2, 1, 1, 3, 2, 3, 4]
def baseStart_460594 : Nat := 118140960795 + 460594 * 2 ^ 59
def prefixEnd_460594 : Nat := 4983230072969 + 3 ^ 40 * 460594 * 2
def baseEnd_460594 : Nat := 140151768045674760033643

theorem tailTrace_460594 : CollatzResearch.WordTrace tailWord_460594 prefixEnd_460594 140151768045674760033643 := by
  unfold tailWord_460594
  simp only [CollatzResearch.WordTrace]
  refine ⟨4199810823338519009403209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11199495528902717358408557 4199810823338519009403209)
  ·
    refine ⟨3149858117503889257052407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4199810823338519009403209 3149858117503889257052407)
    ·
      refine ⟨4724787176255833885578611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3149858117503889257052407 4724787176255833885578611)
      ·
        refine ⟨7087180764383750828367917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4724787176255833885578611 7087180764383750828367917)
        ·
          refine ⟨2657692786643906560637969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7087180764383750828367917 2657692786643906560637969)
          ·
            refine ⟨1993269589982929920478477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2657692786643906560637969 1993269589982929920478477)
            ·
              refine ⟨747476096243598720179429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1993269589982929920478477 747476096243598720179429)
              ·
                refine ⟨140151768045674760033643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 747476096243598720179429 140151768045674760033643)
                ·
                  rfl

theorem cell19_460594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 4].length) (baseStart_460594 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_460594 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_460594 prefixEnd_460594 := by exact prefixLift 460594
  have htrace : WordTrace (prefixWord ++ tailWord_460594) baseStart_460594 baseEnd_460594 := by
    simpa [prefixWord, tailWord_460594, baseEnd_460594] using wordTrace_append hprefix tailTrace_460594
  have hstable : (prefixWord ++ tailWord_460594).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460594).length < 2 ^ (prefixWord ++ tailWord_460594).sum := by decide
  have hdescent : baseEnd_460594 < baseStart_460594 := by decide
  rcases family_descends (prefixWord ++ tailWord_460594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460613 : List Nat := [1, 3, 1, 1, 1, 2, 7, 3]
def baseStart_460613 : Nat := 118140960795 + 460613 * 2 ^ 59
def prefixEnd_460613 : Nat := 4983230072969 + 3 ^ 40 * 460613 * 2
def baseEnd_460613 : Nat := 140157549457488345611369

theorem tailTrace_460613 : CollatzResearch.WordTrace tailWord_460613 prefixEnd_460613 140157549457488345611369 := by
  unfold tailWord_460613
  simp only [CollatzResearch.WordTrace]
  refine ⟨16799936280285242282554493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11199957520190161521702995 16799936280285242282554493)
  ·
    refine ⟨6299976105106965855957935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16799936280285242282554493 6299976105106965855957935)
    ·
      refine ⟨9449964157660448783936903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6299976105106965855957935 9449964157660448783936903)
      ·
        refine ⟨14174946236490673175905355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9449964157660448783936903 14174946236490673175905355)
        ·
          refine ⟨21262419354736009763858033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14174946236490673175905355 21262419354736009763858033)
          ·
            refine ⟨15946814516052007322893525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21262419354736009763858033 15946814516052007322893525)
            ·
              refine ⟨373753465219968921630317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 15946814516052007322893525 373753465219968921630317)
              ·
                refine ⟨140157549457488345611369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 373753465219968921630317 140157549457488345611369)
                ·
                  rfl

theorem cell19_460613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 7, 3].length) (baseStart_460613 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_460613 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_460613 prefixEnd_460613 := by exact prefixLift 460613
  have htrace : WordTrace (prefixWord ++ tailWord_460613) baseStart_460613 baseEnd_460613 := by
    simpa [prefixWord, tailWord_460613, baseEnd_460613] using wordTrace_append hprefix tailTrace_460613
  have hstable : (prefixWord ++ tailWord_460613).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460613).length < 2 ^ (prefixWord ++ tailWord_460613).sum := by decide
  have hdescent : baseEnd_460613 < baseStart_460613 := by decide
  rcases family_descends (prefixWord ++ tailWord_460613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460615 : List Nat := [1, 1, 4, 1, 2, 1, 2, 7]
def baseStart_460615 : Nat := 118140960795 + 460615 * 2 ^ 59
def prefixEnd_460615 : Nat := 4983230072969 + 3 ^ 40 * 460615 * 2
def baseEnd_460615 : Nat := 140158158027152933566919

theorem tailTrace_460615 : CollatzResearch.WordTrace tailWord_460615 prefixEnd_460615 140158158027152933566919 := by
  unfold tailWord_460615
  simp only [CollatzResearch.WordTrace]
  refine ⟨16800009226277996624127299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11200006150851997749418199 16800009226277996624127299)
  ·
    refine ⟨25200013839416994936190949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16800009226277996624127299 25200013839416994936190949)
    ·
      refine ⟨4725002594890686550535803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25200013839416994936190949 4725002594890686550535803)
      ·
        refine ⟨7087503892336029825803705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4725002594890686550535803 7087503892336029825803705)
        ·
          refine ⟨5315627919252022369352779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7087503892336029825803705 5315627919252022369352779)
          ·
            refine ⟨7973441878878033554029169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5315627919252022369352779 7973441878878033554029169)
            ·
              refine ⟨5980081409158525165521877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7973441878878033554029169 5980081409158525165521877)
              ·
                refine ⟨140158158027152933566919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5980081409158525165521877 140158158027152933566919)
                ·
                  rfl

theorem cell19_460615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 7].length) (baseStart_460615 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_460615 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_460615 prefixEnd_460615 := by exact prefixLift 460615
  have htrace : WordTrace (prefixWord ++ tailWord_460615) baseStart_460615 baseEnd_460615 := by
    simpa [prefixWord, tailWord_460615, baseEnd_460615] using wordTrace_append hprefix tailTrace_460615
  have hstable : (prefixWord ++ tailWord_460615).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460615).length < 2 ^ (prefixWord ++ tailWord_460615).sum := by decide
  have hdescent : baseEnd_460615 < baseStart_460615 := by decide
  rcases family_descends (prefixWord ++ tailWord_460615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460634 : List Nat := [3, 1, 1, 2, 1, 3, 8]
def baseStart_460634 : Nat := 118140960795 + 460634 * 2 ^ 59
def prefixEnd_460634 : Nat := 4983230072969 + 3 ^ 40 * 460634 * 2
def baseEnd_460634 : Nat := 46721313146322173048215

theorem tailTrace_460634 : CollatzResearch.WordTrace tailWord_460634 prefixEnd_460634 46721313146322173048215 := by
  unfold tailWord_460634
  simp only [CollatzResearch.WordTrace]
  refine ⟨4200175553302290717267239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11200468142139441912712637 4200175553302290717267239)
  ·
    refine ⟨6300263329953436075900859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4200175553302290717267239 6300263329953436075900859)
    ·
      refine ⟨9450394994930154113851289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6300263329953436075900859 9450394994930154113851289)
      ·
        refine ⟨7087796246197615585388467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9450394994930154113851289 7087796246197615585388467)
        ·
          refine ⟨10631694369296423378082701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7087796246197615585388467 10631694369296423378082701)
          ·
            refine ⟨3986885388486158766781013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10631694369296423378082701 3986885388486158766781013)
            ·
              refine ⟨46721313146322173048215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3986885388486158766781013 46721313146322173048215)
              ·
                rfl

theorem cell19_460634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 8].length) (baseStart_460634 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_460634 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_460634 prefixEnd_460634 := by exact prefixLift 460634
  have htrace : WordTrace (prefixWord ++ tailWord_460634) baseStart_460634 baseEnd_460634 := by
    simpa [prefixWord, tailWord_460634, baseEnd_460634] using wordTrace_append hprefix tailTrace_460634
  have hstable : (prefixWord ++ tailWord_460634).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460634).length < 2 ^ (prefixWord ++ tailWord_460634).sum := by decide
  have hdescent : baseEnd_460634 < baseStart_460634 := by decide
  rcases family_descends (prefixWord ++ tailWord_460634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460672 : List Nat := [2, 1, 1, 2, 1, 2, 5, 5]
def baseStart_460672 : Nat := 118140960795 + 460672 * 2 ^ 59
def prefixEnd_460672 : Nat := 4983230072969 + 3 ^ 40 * 460672 * 2
def baseEnd_460672 : Nat := 140175502262593690300097

theorem tailTrace_460672 : CollatzResearch.WordTrace tailWord_460672 prefixEnd_460672 140175502262593690300097 := by
  unfold tailWord_460672
  simp only [CollatzResearch.WordTrace]
  refine ⟨8401044093535747679476135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11201392124714330239301513 8401044093535747679476135)
  ·
    refine ⟨12601566140303621519214203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8401044093535747679476135 12601566140303621519214203)
    ·
      refine ⟨18902349210455432278821305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12601566140303621519214203 18902349210455432278821305)
      ·
        refine ⟨14176761907841574209115979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18902349210455432278821305 14176761907841574209115979)
        ·
          refine ⟨21265142861762361313673969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14176761907841574209115979 21265142861762361313673969)
          ·
            refine ⟨15948857146321770985255477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21265142861762361313673969 15948857146321770985255477)
            ·
              refine ⟨1495205357467666029867701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15948857146321770985255477 1495205357467666029867701)
              ·
                refine ⟨140175502262593690300097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1495205357467666029867701 140175502262593690300097)
                ·
                  rfl

theorem cell19_460672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 5].length) (baseStart_460672 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_460672 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_460672 prefixEnd_460672 := by exact prefixLift 460672
  have htrace : WordTrace (prefixWord ++ tailWord_460672) baseStart_460672 baseEnd_460672 := by
    simpa [prefixWord, tailWord_460672, baseEnd_460672] using wordTrace_append hprefix tailTrace_460672
  have hstable : (prefixWord ++ tailWord_460672).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460672).length < 2 ^ (prefixWord ++ tailWord_460672).sum := by decide
  have hdescent : baseEnd_460672 < baseStart_460672 := by decide
  rcases family_descends (prefixWord ++ tailWord_460672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460706 : List Nat := [3, 3, 1, 2, 3, 1, 2, 4]
def baseStart_460706 : Nat := 118140960795 + 460706 * 2 ^ 59
def prefixEnd_460706 : Nat := 4983230072969 + 3 ^ 40 * 460706 * 2
def baseEnd_460706 : Nat := 140185847946891685544449

theorem tailTrace_460706 : CollatzResearch.WordTrace tailWord_460706 prefixEnd_460706 140185847946891685544449 := by
  unfold tailWord_460706
  simp only [CollatzResearch.WordTrace]
  refine ⟨4200832067237079791422493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11202218845965546110459981 4200832067237079791422493)
  ·
    refine ⟨1575312025213904921783435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4200832067237079791422493 1575312025213904921783435)
    ·
      refine ⟨2362968037820857382675153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1575312025213904921783435 2362968037820857382675153)
      ·
        refine ⟨1772226028365643037006365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2362968037820857382675153 1772226028365643037006365)
        ·
          refine ⟨664584760637116138877387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1772226028365643037006365 664584760637116138877387)
          ·
            refine ⟨996877140955674208316081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 664584760637116138877387 996877140955674208316081)
            ·
              refine ⟨747657855716755656237061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 996877140955674208316081 747657855716755656237061)
              ·
                refine ⟨140185847946891685544449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 747657855716755656237061 140185847946891685544449)
                ·
                  rfl

theorem cell19_460706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 4].length) (baseStart_460706 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_460706 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_460706 prefixEnd_460706 := by exact prefixLift 460706
  have htrace : WordTrace (prefixWord ++ tailWord_460706) baseStart_460706 baseEnd_460706 := by
    simpa [prefixWord, tailWord_460706, baseEnd_460706] using wordTrace_append hprefix tailTrace_460706
  have hstable : (prefixWord ++ tailWord_460706).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460706).length < 2 ^ (prefixWord ++ tailWord_460706).sum := by decide
  have hdescent : baseEnd_460706 < baseStart_460706 := by decide
  rcases family_descends (prefixWord ++ tailWord_460706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460708 : List Nat := [2, 3, 1, 2, 1, 4, 2, 4]
def baseStart_460708 : Nat := 118140960795 + 460708 * 2 ^ 59
def prefixEnd_460708 : Nat := 4983230072969 + 3 ^ 40 * 460708 * 2
def baseEnd_460708 : Nat := 140186456516556273499999

theorem tailTrace_460708 : CollatzResearch.WordTrace tailWord_460708 prefixEnd_460708 140186456516556273499999 := by
  unfold tailWord_460708
  simp only [CollatzResearch.WordTrace]
  refine ⟨8401700607470536753631389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11202267476627382338175185 8401700607470536753631389)
  ·
    refine ⟨3150637727801451282611771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8401700607470536753631389 3150637727801451282611771)
    ·
      refine ⟨4725956591702176923917657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3150637727801451282611771 4725956591702176923917657)
      ·
        refine ⟨3544467443776632692938243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4725956591702176923917657 3544467443776632692938243)
        ·
          refine ⟨5316701165664949039407365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3544467443776632692938243 5316701165664949039407365)
          ·
            refine ⟨996881468562177944888881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5316701165664949039407365 996881468562177944888881)
            ·
              refine ⟨747661101421633458666661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 996881468562177944888881 747661101421633458666661)
              ·
                refine ⟨140186456516556273499999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 747661101421633458666661 140186456516556273499999)
                ·
                  rfl

theorem cell19_460708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 4].length) (baseStart_460708 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_460708 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_460708 prefixEnd_460708 := by exact prefixLift 460708
  have htrace : WordTrace (prefixWord ++ tailWord_460708) baseStart_460708 baseEnd_460708 := by
    simpa [prefixWord, tailWord_460708, baseEnd_460708] using wordTrace_append hprefix tailTrace_460708
  have hstable : (prefixWord ++ tailWord_460708).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460708).length < 2 ^ (prefixWord ++ tailWord_460708).sum := by decide
  have hdescent : baseEnd_460708 < baseStart_460708 := by decide
  rcases family_descends (prefixWord ++ tailWord_460708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460729 : List Nat := [1, 2, 1, 4, 2, 1, 1, 7]
def baseStart_460729 : Nat := 118140960795 + 460729 * 2 ^ 59
def prefixEnd_460729 : Nat := 4983230072969 + 3 ^ 40 * 460729 * 2
def baseEnd_460729 : Nat := 140192846498034447033275

theorem tailTrace_460729 : CollatzResearch.WordTrace tailWord_460729 prefixEnd_460729 140192846498034447033275 := by
  unfold tailWord_460729
  simp only [CollatzResearch.WordTrace]
  refine ⟨16804167147864994093777241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11202778098576662729184827 16804167147864994093777241)
  ·
    refine ⟨12603125360898745570332931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16804167147864994093777241 12603125360898745570332931)
    ·
      refine ⟨18904688041348118355499397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12603125360898745570332931 18904688041348118355499397)
      ·
        refine ⟨3544629007752772191656137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18904688041348118355499397 3544629007752772191656137)
        ·
          refine ⟨2658471755814579143742103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3544629007752772191656137 2658471755814579143742103)
          ·
            refine ⟨3987707633721868715613155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2658471755814579143742103 3987707633721868715613155)
            ·
              refine ⟨5981561450582803073419733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3987707633721868715613155 5981561450582803073419733)
              ·
                refine ⟨140192846498034447033275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5981561450582803073419733 140192846498034447033275)
                ·
                  rfl

theorem cell19_460729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 7].length) (baseStart_460729 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_460729 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_460729 prefixEnd_460729 := by exact prefixLift 460729
  have htrace : WordTrace (prefixWord ++ tailWord_460729) baseStart_460729 baseEnd_460729 := by
    simpa [prefixWord, tailWord_460729, baseEnd_460729] using wordTrace_append hprefix tailTrace_460729
  have hstable : (prefixWord ++ tailWord_460729).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460729).length < 2 ^ (prefixWord ++ tailWord_460729).sum := by decide
  have hdescent : baseEnd_460729 < baseStart_460729 := by decide
  rcases family_descends (prefixWord ++ tailWord_460729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460748 : List Nat := [2, 2, 1, 4, 1, 9]
def baseStart_460748 : Nat := 118140960795 + 460748 * 2 ^ 59
def prefixEnd_460748 : Nat := 4983230072969 + 3 ^ 40 * 460748 * 2
def baseEnd_460748 : Nat := 15577625323316448067889

theorem tailTrace_460748 : CollatzResearch.WordTrace tailWord_460748 prefixEnd_460748 15577625323316448067889 := by
  unfold tailWord_460748
  simp only [CollatzResearch.WordTrace]
  refine ⟨8402430067398080169359449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11203240089864106892479265 8402430067398080169359449)
  ·
    refine ⟨6301822550548560127019587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8402430067398080169359449 6301822550548560127019587)
    ·
      refine ⟨9452733825822840190529381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6301822550548560127019587 9452733825822840190529381)
      ·
        refine ⟨1772387592341782535724259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9452733825822840190529381 1772387592341782535724259)
        ·
          refine ⟨2658581388512673803586389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1772387592341782535724259 2658581388512673803586389)
          ·
            refine ⟨15577625323316448067889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2658581388512673803586389 15577625323316448067889)
            ·
              rfl

theorem cell19_460748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 9].length) (baseStart_460748 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_460748 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_460748 prefixEnd_460748 := by exact prefixLift 460748
  have htrace : WordTrace (prefixWord ++ tailWord_460748) baseStart_460748 baseEnd_460748 := by
    simpa [prefixWord, tailWord_460748, baseEnd_460748] using wordTrace_append hprefix tailTrace_460748
  have hstable : (prefixWord ++ tailWord_460748).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460748).length < 2 ^ (prefixWord ++ tailWord_460748).sum := by decide
  have hdescent : baseEnd_460748 < baseStart_460748 := by decide
  rcases family_descends (prefixWord ++ tailWord_460748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460782 : List Nat := [4, 1, 2, 1, 3, 2, 3, 3]
def baseStart_460782 : Nat := 118140960795 + 460782 * 2 ^ 59
def prefixEnd_460782 : Nat := 4983230072969 + 3 ^ 40 * 460782 * 2
def baseEnd_460782 : Nat := 140208973594146027855353

theorem tailTrace_460782 : CollatzResearch.WordTrace tailWord_460782 prefixEnd_460782 140208973594146027855353 := by
  unfold tailWord_460782
  simp only [CollatzResearch.WordTrace]
  refine ⟨2100762527084123018182075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11204066811115322763637733 2100762527084123018182075)
  ·
    refine ⟨3151143790626184527273113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2100762527084123018182075 3151143790626184527273113)
    ·
      refine ⟨2363357842969638395454835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3151143790626184527273113 2363357842969638395454835)
      ·
        refine ⟨3545036764454457593182253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2363357842969638395454835 3545036764454457593182253)
        ·
          refine ⟨1329388786670421597443345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3545036764454457593182253 1329388786670421597443345)
          ·
            refine ⟨997041590002816198082509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1329388786670421597443345 997041590002816198082509)
            ·
              refine ⟨373890596251056074280941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 997041590002816198082509 373890596251056074280941)
              ·
                refine ⟨140208973594146027855353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 373890596251056074280941 140208973594146027855353)
                ·
                  rfl

theorem cell19_460782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 3, 3].length) (baseStart_460782 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_460782 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_460782 prefixEnd_460782 := by exact prefixLift 460782
  have htrace : WordTrace (prefixWord ++ tailWord_460782) baseStart_460782 baseEnd_460782 := by
    simpa [prefixWord, tailWord_460782, baseEnd_460782] using wordTrace_append hprefix tailTrace_460782
  have hstable : (prefixWord ++ tailWord_460782).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460782).length < 2 ^ (prefixWord ++ tailWord_460782).sum := by decide
  have hdescent : baseEnd_460782 < baseStart_460782 := by decide
  rcases family_descends (prefixWord ++ tailWord_460782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460805 : List Nat := [1, 3, 1, 1, 2, 5, 6]
def baseStart_460805 : Nat := 118140960795 + 460805 * 2 ^ 59
def prefixEnd_460805 : Nat := 4983230072969 + 3 ^ 40 * 460805 * 2
def baseEnd_460805 : Nat := 46738657381762929781393

theorem tailTrace_460805 : CollatzResearch.WordTrace tailWord_460805 prefixEnd_460805 46738657381762929781393 := by
  unfold tailWord_460805
  simp only [CollatzResearch.WordTrace]
  refine ⟨16806939095589659073543869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11204626063726439382362579 16806939095589659073543869)
  ·
    refine ⟨6302602160846122152578951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16806939095589659073543869 6302602160846122152578951)
    ·
      refine ⟨9453903241269183228868427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6302602160846122152578951 9453903241269183228868427)
      ·
        refine ⟨14180854861903774843302641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9453903241269183228868427 14180854861903774843302641)
        ·
          refine ⟨10635641146427831132476981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14180854861903774843302641 10635641146427831132476981)
          ·
            refine ⟨997091357477609168669717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10635641146427831132476981 997091357477609168669717)
            ·
              refine ⟨46738657381762929781393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 997091357477609168669717 46738657381762929781393)
              ·
                rfl

theorem cell19_460805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 6].length) (baseStart_460805 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_460805 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_460805 prefixEnd_460805 := by exact prefixLift 460805
  have htrace : WordTrace (prefixWord ++ tailWord_460805) baseStart_460805 baseEnd_460805 := by
    simpa [prefixWord, tailWord_460805, baseEnd_460805] using wordTrace_append hprefix tailTrace_460805
  have hstable : (prefixWord ++ tailWord_460805).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460805).length < 2 ^ (prefixWord ++ tailWord_460805).sum := by decide
  have hdescent : baseEnd_460805 < baseStart_460805 := by decide
  rcases family_descends (prefixWord ++ tailWord_460805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460824 : List Nat := [2, 1, 2, 3, 2, 1, 2, 6]
def baseStart_460824 : Nat := 118140960795 + 460824 * 2 ^ 59
def prefixEnd_460824 : Nat := 4983230072969 + 3 ^ 40 * 460824 * 2
def baseEnd_460824 : Nat := 140221753557102374921905

theorem tailTrace_460824 : CollatzResearch.WordTrace tailWord_460824 prefixEnd_460824 140221753557102374921905 := by
  unfold tailWord_460824
  simp only [CollatzResearch.WordTrace]
  refine ⟨8403816041260412659242763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11205088055013883545657017 8403816041260412659242763)
  ·
    refine ⟨12605724061890618988864145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8403816041260412659242763 12605724061890618988864145)
    ·
      refine ⟨9454293046417964241648109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12605724061890618988864145 9454293046417964241648109)
      ·
        refine ⟨3545359892406736590618041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9454293046417964241648109 3545359892406736590618041)
        ·
          refine ⟨2659019919305052442963531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3545359892406736590618041 2659019919305052442963531)
          ·
            refine ⟨3988529878957578664445297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2659019919305052442963531 3988529878957578664445297)
            ·
              refine ⟨2991397409218183998333973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3988529878957578664445297 2991397409218183998333973)
              ·
                refine ⟨140221753557102374921905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2991397409218183998333973 140221753557102374921905)
                ·
                  rfl

theorem cell19_460824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 6].length) (baseStart_460824 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_460824 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_460824 prefixEnd_460824 := by exact prefixLift 460824
  have htrace : WordTrace (prefixWord ++ tailWord_460824) baseStart_460824 baseEnd_460824 := by
    simpa [prefixWord, tailWord_460824, baseEnd_460824] using wordTrace_append hprefix tailTrace_460824
  have hstable : (prefixWord ++ tailWord_460824).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460824).length < 2 ^ (prefixWord ++ tailWord_460824).sum := by decide
  have hdescent : baseEnd_460824 < baseStart_460824 := by decide
  rcases family_descends (prefixWord ++ tailWord_460824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460839 : List Nat := [1, 1, 7, 1, 2, 1, 1, 5]
def baseStart_460839 : Nat := 118140960795 + 460839 * 2 ^ 59
def prefixEnd_460839 : Nat := 4983230072969 + 3 ^ 40 * 460839 * 2
def baseEnd_460839 : Nat := 140226317829586784588531

theorem tailTrace_460839 : CollatzResearch.WordTrace tailWord_460839 prefixEnd_460839 140226317829586784588531 := by
  unfold tailWord_460839
  simp only [CollatzResearch.WordTrace]
  refine ⟨16808179177466482880281571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11205452784977655253521047 16808179177466482880281571)
  ·
    refine ⟨25212268766199724320422357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16808179177466482880281571 25212268766199724320422357)
    ·
      refine ⟨590912549207806038759899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 25212268766199724320422357 590912549207806038759899)
      ·
        refine ⟨886368823811709058139849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 590912549207806038759899 886368823811709058139849)
        ·
          refine ⟨664776617858781793604887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 886368823811709058139849 664776617858781793604887)
          ·
            refine ⟨997164926788172690407331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 664776617858781793604887 997164926788172690407331)
            ·
              refine ⟨1495747390182259035610997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 997164926788172690407331 1495747390182259035610997)
              ·
                refine ⟨140226317829586784588531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1495747390182259035610997 140226317829586784588531)
                ·
                  rfl

theorem cell19_460839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 5].length) (baseStart_460839 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_460839 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_460839 prefixEnd_460839 := by exact prefixLift 460839
  have htrace : WordTrace (prefixWord ++ tailWord_460839) baseStart_460839 baseEnd_460839 := by
    simpa [prefixWord, tailWord_460839, baseEnd_460839] using wordTrace_append hprefix tailTrace_460839
  have hstable : (prefixWord ++ tailWord_460839).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460839).length < 2 ^ (prefixWord ++ tailWord_460839).sum := by decide
  have hdescent : baseEnd_460839 < baseStart_460839 := by decide
  rcases family_descends (prefixWord ++ tailWord_460839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460900 : List Nat := [2, 3, 1, 1, 2, 1, 4, 5]
def baseStart_460900 : Nat := 118140960795 + 460900 * 2 ^ 59
def prefixEnd_460900 : Nat := 4983230072969 + 3 ^ 40 * 460900 * 2
def baseEnd_460900 : Nat := 140244879204356717232809

theorem tailTrace_460900 : CollatzResearch.WordTrace tailWord_460900 prefixEnd_460900 140244879204356717232809 := by
  unfold tailWord_460900
  simp only [CollatzResearch.WordTrace]
  refine ⟨8405202015122745149126077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11206936020163660198834769 8405202015122745149126077)
  ·
    refine ⟨3151950755671029430922279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8405202015122745149126077 3151950755671029430922279)
    ·
      refine ⟨4727926133506544146383419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3151950755671029430922279 4727926133506544146383419)
      ·
        refine ⟨7091889200259816219575129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4727926133506544146383419 7091889200259816219575129)
        ·
          refine ⟨5318916900194862164681347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7091889200259816219575129 5318916900194862164681347)
          ·
            refine ⟨7978375350292293247022021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5318916900194862164681347 7978375350292293247022021)
            ·
              refine ⟨1495945378179804983816629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7978375350292293247022021 1495945378179804983816629)
              ·
                refine ⟨140244879204356717232809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1495945378179804983816629 140244879204356717232809)
                ·
                  rfl

theorem cell19_460900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 5].length) (baseStart_460900 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_460900 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_460900 prefixEnd_460900 := by exact prefixLift 460900
  have htrace : WordTrace (prefixWord ++ tailWord_460900) baseStart_460900 baseEnd_460900 := by
    simpa [prefixWord, tailWord_460900, baseEnd_460900] using wordTrace_append hprefix tailTrace_460900
  have hstable : (prefixWord ++ tailWord_460900).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460900).length < 2 ^ (prefixWord ++ tailWord_460900).sum := by decide
  have hdescent : baseEnd_460900 < baseStart_460900 := by decide
  rcases family_descends (prefixWord ++ tailWord_460900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_460936 : List Nat := [2, 1, 3, 4, 1, 1, 3, 4]
def baseStart_460936 : Nat := 118140960795 + 460936 * 2 ^ 59
def prefixEnd_460936 : Nat := 4983230072969 + 3 ^ 40 * 460936 * 2
def baseEnd_460936 : Nat := 140255833458319300432711

theorem tailTrace_460936 : CollatzResearch.WordTrace tailWord_460936 prefixEnd_460936 140255833458319300432711 := by
  unfold tailWord_460936
  simp only [CollatzResearch.WordTrace]
  refine ⟨8405858529057534223281331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11207811372076712297708441 8405858529057534223281331)
  ·
    refine ⟨12608787793586301334921997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8405858529057534223281331 12608787793586301334921997)
    ·
      refine ⟨4728295422594863000595749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12608787793586301334921997 4728295422594863000595749)
      ·
        refine ⟨886555391736536812611703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4728295422594863000595749 886555391736536812611703)
        ·
          refine ⟨1329833087604805218917555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 886555391736536812611703 1329833087604805218917555)
          ·
            refine ⟨1994749631407207828376333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1329833087604805218917555 1994749631407207828376333)
            ·
              refine ⟨748031111777702935641125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1994749631407207828376333 748031111777702935641125)
              ·
                refine ⟨140255833458319300432711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 748031111777702935641125 140255833458319300432711)
                ·
                  rfl

theorem cell19_460936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 4].length) (baseStart_460936 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_460936 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_460936 prefixEnd_460936 := by exact prefixLift 460936
  have htrace : WordTrace (prefixWord ++ tailWord_460936) baseStart_460936 baseEnd_460936 := by
    simpa [prefixWord, tailWord_460936, baseEnd_460936] using wordTrace_append hprefix tailTrace_460936
  have hstable : (prefixWord ++ tailWord_460936).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_460936).length < 2 ^ (prefixWord ++ tailWord_460936).sum := by decide
  have hdescent : baseEnd_460936 < baseStart_460936 := by decide
  rcases family_descends (prefixWord ++ tailWord_460936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461010 : List Nat := [3, 2, 2, 2, 1, 4, 2, 3]
def baseStart_461010 : Nat := 118140960795 + 461010 * 2 ^ 59
def prefixEnd_461010 : Nat := 4983230072969 + 3 ^ 40 * 461010 * 2
def baseEnd_461010 : Nat := 140278350535909054788065

theorem tailTrace_461010 : CollatzResearch.WordTrace tailWord_461010 prefixEnd_461010 140278350535909054788065 := by
  unfold tailWord_461010
  simp only [CollatzResearch.WordTrace]
  refine ⟨4203604014961744771189121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11209610706564652723170989 4203604014961744771189121)
  ·
    refine ⟨3152703011221308578391841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4203604014961744771189121 3152703011221308578391841)
    ·
      refine ⟨2364527258415981433793881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3152703011221308578391841 2364527258415981433793881)
      ·
        refine ⟨1773395443811986075345411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2364527258415981433793881 1773395443811986075345411)
        ·
          refine ⟨2660093165717979113018117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1773395443811986075345411 2660093165717979113018117)
          ·
            refine ⟨498767468572121083690897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2660093165717979113018117 498767468572121083690897)
            ·
              refine ⟨374075601429090812768173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 498767468572121083690897 374075601429090812768173)
              ·
                refine ⟨140278350535909054788065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 374075601429090812768173 140278350535909054788065)
                ·
                  rfl

theorem cell19_461010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 2, 3].length) (baseStart_461010 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_461010 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_461010 prefixEnd_461010 := by exact prefixLift 461010
  have htrace : WordTrace (prefixWord ++ tailWord_461010) baseStart_461010 baseEnd_461010 := by
    simpa [prefixWord, tailWord_461010, baseEnd_461010] using wordTrace_append hprefix tailTrace_461010
  have hstable : (prefixWord ++ tailWord_461010).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461010).length < 2 ^ (prefixWord ++ tailWord_461010).sum := by decide
  have hdescent : baseEnd_461010 < baseStart_461010 := by decide
  rcases family_descends (prefixWord ++ tailWord_461010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461031 : List Nat := [1, 1, 5, 3, 1, 3, 5]
def baseStart_461031 : Nat := 118140960795 + 461031 * 2 ^ 59
def prefixEnd_461031 : Nat := 4983230072969 + 3 ^ 40 * 461031 * 2
def baseEnd_461031 : Nat := 46761580172462409440447

theorem tailTrace_461031 : CollatzResearch.WordTrace tailWord_461031 prefixEnd_461031 46761580172462409440447 := by
  unfold tailWord_461031
  simp only [CollatzResearch.WordTrace]
  refine ⟨16815181992770899671270947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11210121328513933114180631 16815181992770899671270947)
  ·
    refine ⟨25222772989156349506906421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16815181992770899671270947 25222772989156349506906421)
    ·
      refine ⟨2364634967733407766272477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25222772989156349506906421 2364634967733407766272477)
      ·
        refine ⟨886738112900027912352179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2364634967733407766272477 886738112900027912352179)
        ·
          refine ⟨1330107169350041868528269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 886738112900027912352179 1330107169350041868528269)
          ·
            refine ⟨498790188506265700698101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1330107169350041868528269 498790188506265700698101)
            ·
              refine ⟨46761580172462409440447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 498790188506265700698101 46761580172462409440447)
              ·
                rfl

theorem cell19_461031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 5].length) (baseStart_461031 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_461031 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_461031 prefixEnd_461031 := by exact prefixLift 461031
  have htrace : WordTrace (prefixWord ++ tailWord_461031) baseStart_461031 baseEnd_461031 := by
    simpa [prefixWord, tailWord_461031, baseEnd_461031] using wordTrace_append hprefix tailTrace_461031
  have hstable : (prefixWord ++ tailWord_461031).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461031).length < 2 ^ (prefixWord ++ tailWord_461031).sum := by decide
  have hdescent : baseEnd_461031 < baseStart_461031 := by decide
  rcases family_descends (prefixWord ++ tailWord_461031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461052 : List Nat := [2, 2, 2, 1, 4, 1, 1, 6]
def baseStart_461052 : Nat := 118140960795 + 461052 * 2 ^ 59
def prefixEnd_461052 : Nat := 4983230072969 + 3 ^ 40 * 461052 * 2
def baseEnd_461052 : Nat := 140291130498865401854617

theorem tailTrace_461052 : CollatzResearch.WordTrace tailWord_461052 prefixEnd_461052 140291130498865401854617 := by
  unfold tailWord_461052
  simp only [CollatzResearch.WordTrace]
  refine ⟨8407973962847410128892705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11210631950463213505190273 8407973962847410128892705)
  ·
    refine ⟨6305980472135557596669529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8407973962847410128892705 6305980472135557596669529)
    ·
      refine ⟨4729485354101668197502147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6305980472135557596669529 4729485354101668197502147)
      ·
        refine ⟨7094228031152502296253221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4729485354101668197502147 7094228031152502296253221)
        ·
          refine ⟨1330167755841094180547479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7094228031152502296253221 1330167755841094180547479)
          ·
            refine ⟨1995251633761641270821219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1330167755841094180547479 1995251633761641270821219)
            ·
              refine ⟨2992877450642461906231829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1995251633761641270821219 2992877450642461906231829)
              ·
                refine ⟨140291130498865401854617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2992877450642461906231829 140291130498865401854617)
                ·
                  rfl

theorem cell19_461052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 6].length) (baseStart_461052 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_461052 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_461052 prefixEnd_461052 := by exact prefixLift 461052
  have htrace : WordTrace (prefixWord ++ tailWord_461052) baseStart_461052 baseEnd_461052 := by
    simpa [prefixWord, tailWord_461052, baseEnd_461052] using wordTrace_append hprefix tailTrace_461052
  have hstable : (prefixWord ++ tailWord_461052).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461052).length < 2 ^ (prefixWord ++ tailWord_461052).sum := by decide
  have hdescent : baseEnd_461052 < baseStart_461052 := by decide
  rcases family_descends (prefixWord ++ tailWord_461052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461090 : List Nat := [3, 3, 1, 1, 3, 8]
def baseStart_461090 : Nat := 118140960795 + 461090 * 2 ^ 59
def prefixEnd_461090 : Nat := 4983230072969 + 3 ^ 40 * 461090 * 2
def baseEnd_461090 : Nat := 15589188146943619223341

theorem tailTrace_461090 : CollatzResearch.WordTrace tailWord_461090 prefixEnd_461090 15589188146943619223341 := by
  unfold tailWord_461090
  simp only [CollatzResearch.WordTrace]
  refine ⟨4204333474889288186917181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11211555933038101831779149 4204333474889288186917181)
  ·
    refine ⟨1576625053083483070093943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4204333474889288186917181 1576625053083483070093943)
    ·
      refine ⟨2364937579625224605140915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1576625053083483070093943 2364937579625224605140915)
      ·
        refine ⟨3547406369437836907711373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2364937579625224605140915 3547406369437836907711373)
        ·
          refine ⟨1330277388539188840391765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3547406369437836907711373 1330277388539188840391765)
          ·
            refine ⟨15589188146943619223341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1330277388539188840391765 15589188146943619223341)
            ·
              rfl

theorem cell19_461090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 8].length) (baseStart_461090 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_461090 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_461090 prefixEnd_461090 := by exact prefixLift 461090
  have htrace : WordTrace (prefixWord ++ tailWord_461090) baseStart_461090 baseEnd_461090 := by
    simpa [prefixWord, tailWord_461090, baseEnd_461090] using wordTrace_append hprefix tailTrace_461090
  have hstable : (prefixWord ++ tailWord_461090).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461090).length < 2 ^ (prefixWord ++ tailWord_461090).sum := by decide
  have hdescent : baseEnd_461090 < baseStart_461090 := by decide
  rcases family_descends (prefixWord ++ tailWord_461090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461105 : List Nat := [1, 2, 2, 3, 5, 1, 1, 4]
def baseStart_461105 : Nat := 118140960795 + 461105 * 2 ^ 59
def prefixEnd_461105 : Nat := 4983230072969 + 3 ^ 40 * 461105 * 2
def baseEnd_461105 : Nat := 140307257594976982676695

theorem tailTrace_461105 : CollatzResearch.WordTrace tailWord_461105 prefixEnd_461105 140307257594976982676695 := by
  unfold tailWord_461105
  simp only [CollatzResearch.WordTrace]
  refine ⟨16817880994502810309464769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11211920663001873539643179 16817880994502810309464769)
  ·
    refine ⟨12613410745877107732098577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16817880994502810309464769 12613410745877107732098577)
    ·
      refine ⟨9460058059407830799073933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12613410745877107732098577 9460058059407830799073933)
      ·
        refine ⟨3547521772277936549652725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9460058059407830799073933 3547521772277936549652725)
        ·
          refine ⟨332580166151056551529943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3547521772277936549652725 332580166151056551529943)
          ·
            refine ⟨498870249226584827294915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332580166151056551529943 498870249226584827294915)
            ·
              refine ⟨748305373839877240942373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 498870249226584827294915 748305373839877240942373)
              ·
                refine ⟨140307257594976982676695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 748305373839877240942373 140307257594976982676695)
                ·
                  rfl

theorem cell19_461105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 4].length) (baseStart_461105 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_461105 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_461105 prefixEnd_461105 := by exact prefixLift 461105
  have htrace : WordTrace (prefixWord ++ tailWord_461105) baseStart_461105 baseEnd_461105 := by
    simpa [prefixWord, tailWord_461105, baseEnd_461105] using wordTrace_append hprefix tailTrace_461105
  have hstable : (prefixWord ++ tailWord_461105).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461105).length < 2 ^ (prefixWord ++ tailWord_461105).sum := by decide
  have hdescent : baseEnd_461105 < baseStart_461105 := by decide
  rcases family_descends (prefixWord ++ tailWord_461105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461223 : List Nat := [1, 1, 6, 1, 1, 2, 1, 6]
def baseStart_461223 : Nat := 118140960795 + 461223 * 2 ^ 59
def prefixEnd_461223 : Nat := 4983230072969 + 3 ^ 40 * 461223 * 2
def baseEnd_461223 : Nat := 140343163205187672054151

theorem tailTrace_461223 : CollatzResearch.WordTrace tailWord_461223 prefixEnd_461223 140343163205187672054151 := by
  unfold tailWord_461223
  simp only [CollatzResearch.WordTrace]
  refine ⟨16822184808075316462260323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11214789872050210974840215 16822184808075316462260323)
  ·
    refine ⟨25233277212112974693390485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16822184808075316462260323 25233277212112974693390485)
    ·
      refine ⟨1182809869317795688752679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 25233277212112974693390485 1182809869317795688752679)
      ·
        refine ⟨1774214803976693533129019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1182809869317795688752679 1774214803976693533129019)
        ·
          refine ⟨2661322205965040299693529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1774214803976693533129019 2661322205965040299693529)
          ·
            refine ⟨1995991654473780224770147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2661322205965040299693529 1995991654473780224770147)
            ·
              refine ⟨2993987481710670337155221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1995991654473780224770147 2993987481710670337155221)
              ·
                refine ⟨140343163205187672054151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2993987481710670337155221 140343163205187672054151)
                ·
                  rfl

theorem cell19_461223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 6].length) (baseStart_461223 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_461223 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_461223 prefixEnd_461223 := by exact prefixLift 461223
  have htrace : WordTrace (prefixWord ++ tailWord_461223) baseStart_461223 baseEnd_461223 := by
    simpa [prefixWord, tailWord_461223, baseEnd_461223] using wordTrace_append hprefix tailTrace_461223
  have hstable : (prefixWord ++ tailWord_461223).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461223).length < 2 ^ (prefixWord ++ tailWord_461223).sum := by decide
  have hdescent : baseEnd_461223 < baseStart_461223 := by decide
  rcases family_descends (prefixWord ++ tailWord_461223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461299 : List Nat := [1, 1, 1, 2, 2, 2, 7, 3]
def baseStart_461299 : Nat := 118140960795 + 461299 * 2 ^ 59
def prefixEnd_461299 : Nat := 4983230072969 + 3 ^ 40 * 461299 * 2
def baseEnd_461299 : Nat := 140366288852442014365055

theorem tailTrace_461299 : CollatzResearch.WordTrace tailWord_461299 prefixEnd_461299 140366288852442014365055 := by
  unfold tailWord_461299
  simp only [CollatzResearch.WordTrace]
  refine ⟨16824956755799981442026951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11216637837199987628017967 16824956755799981442026951)
  ·
    refine ⟨25237435133699972163040427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16824956755799981442026951 25237435133699972163040427)
    ·
      refine ⟨37856152700549958244560641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25237435133699972163040427 37856152700549958244560641)
      ·
        refine ⟨28392114525412468683420481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37856152700549958244560641 28392114525412468683420481)
        ·
          refine ⟨21294085894059351512565361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28392114525412468683420481 21294085894059351512565361)
          ·
            refine ⟨15970564420544513634424021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21294085894059351512565361 15970564420544513634424021)
            ·
              refine ⟨374310103606512038306813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 15970564420544513634424021 374310103606512038306813)
              ·
                refine ⟨140366288852442014365055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 374310103606512038306813 140366288852442014365055)
                ·
                  rfl

theorem cell19_461299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 7, 3].length) (baseStart_461299 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_461299 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_461299 prefixEnd_461299 := by exact prefixLift 461299
  have htrace : WordTrace (prefixWord ++ tailWord_461299) baseStart_461299 baseEnd_461299 := by
    simpa [prefixWord, tailWord_461299, baseEnd_461299] using wordTrace_append hprefix tailTrace_461299
  have hstable : (prefixWord ++ tailWord_461299).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461299).length < 2 ^ (prefixWord ++ tailWord_461299).sum := by decide
  have hdescent : baseEnd_461299 < baseStart_461299 := by decide
  rcases family_descends (prefixWord ++ tailWord_461299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461352 : List Nat := [2, 1, 5, 2, 1, 3, 2, 3]
def baseStart_461352 : Nat := 118140960795 + 461352 * 2 ^ 59
def prefixEnd_461352 : Nat := 4983230072969 + 3 ^ 40 * 461352 * 2
def baseEnd_461352 : Nat := 140382415948553595187133

theorem tailTrace_461352 : CollatzResearch.WordTrace tailWord_461352 prefixEnd_461352 140382415948553595187133 := by
  unfold tailWord_461352
  simp only [CollatzResearch.WordTrace]
  refine ⟨8413444912303985746853155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11217926549738647662470873 8413444912303985746853155)
  ·
    refine ⟨12620167368455978620279733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8413444912303985746853155 12620167368455978620279733)
    ·
      refine ⟨1183140690792747995651225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12620167368455978620279733 1183140690792747995651225)
      ·
        refine ⟨887355518094560996738419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1183140690792747995651225 887355518094560996738419)
        ·
          refine ⟨1331033277141841495107629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 887355518094560996738419 1331033277141841495107629)
          ·
            refine ⟨499137478928190560665361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1331033277141841495107629 499137478928190560665361)
            ·
              refine ⟨374353109196142920499021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 499137478928190560665361 374353109196142920499021)
              ·
                refine ⟨140382415948553595187133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 374353109196142920499021 140382415948553595187133)
                ·
                  rfl

theorem cell19_461352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 2, 3].length) (baseStart_461352 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_461352 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_461352 prefixEnd_461352 := by exact prefixLift 461352
  have htrace : WordTrace (prefixWord ++ tailWord_461352) baseStart_461352 baseEnd_461352 := by
    simpa [prefixWord, tailWord_461352, baseEnd_461352] using wordTrace_append hprefix tailTrace_461352
  have hstable : (prefixWord ++ tailWord_461352).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461352).length < 2 ^ (prefixWord ++ tailWord_461352).sum := by decide
  have hdescent : baseEnd_461352 < baseStart_461352 := by decide
  rcases family_descends (prefixWord ++ tailWord_461352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461354 : List Nat := [3, 1, 4, 1, 1, 2, 4, 3]
def baseStart_461354 : Nat := 118140960795 + 461354 * 2 ^ 59
def prefixEnd_461354 : Nat := 4983230072969 + 3 ^ 40 * 461354 * 2
def baseEnd_461354 : Nat := 140383024518218183142683

theorem tailTrace_461354 : CollatzResearch.WordTrace tailWord_461354 prefixEnd_461354 140383024518218183142683 := by
  unfold tailWord_461354
  simp only [CollatzResearch.WordTrace]
  refine ⟨4206740692650181458819779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11217975180400483890186077 4206740692650181458819779)
  ·
    refine ⟨6310111038975272188229669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4206740692650181458819779 6310111038975272188229669)
    ·
      refine ⟨1183145819807863535293063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6310111038975272188229669 1183145819807863535293063)
      ·
        refine ⟨1774718729711795302939595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1183145819807863535293063 1774718729711795302939595)
        ·
          refine ⟨2662078094567692954409393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1774718729711795302939595 2662078094567692954409393)
          ·
            refine ⟨1996558570925769715807045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2662078094567692954409393 1996558570925769715807045)
            ·
              refine ⟨374354732048581821713821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1996558570925769715807045 374354732048581821713821)
              ·
                refine ⟨140383024518218183142683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 374354732048581821713821 140383024518218183142683)
                ·
                  rfl

theorem cell19_461354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 4, 3].length) (baseStart_461354 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_461354 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_461354 prefixEnd_461354 := by exact prefixLift 461354
  have htrace : WordTrace (prefixWord ++ tailWord_461354) baseStart_461354 baseEnd_461354 := by
    simpa [prefixWord, tailWord_461354, baseEnd_461354] using wordTrace_append hprefix tailTrace_461354
  have hstable : (prefixWord ++ tailWord_461354).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461354).length < 2 ^ (prefixWord ++ tailWord_461354).sum := by decide
  have hdescent : baseEnd_461354 < baseStart_461354 := by decide
  rcases family_descends (prefixWord ++ tailWord_461354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461394 : List Nat := [3, 2, 2, 1, 2, 1, 4, 4]
def baseStart_461394 : Nat := 118140960795 + 461394 * 2 ^ 59
def prefixEnd_461394 : Nat := 4983230072969 + 3 ^ 40 * 461394 * 2
def baseEnd_461394 : Nat := 140395195911509942253685

theorem tailTrace_461394 : CollatzResearch.WordTrace tailWord_461394 prefixEnd_461394 140395195911509942253685 := by
  unfold tailWord_461394
  simp only [CollatzResearch.WordTrace]
  refine ⟨4207105422613953166683809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11218947793637208444490157 4207105422613953166683809)
  ·
    refine ⟨3155329066960464875012857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4207105422613953166683809 3155329066960464875012857)
    ·
      refine ⟨2366496800220348656259643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3155329066960464875012857 2366496800220348656259643)
      ·
        refine ⟨3549745200330522984389465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2366496800220348656259643 3549745200330522984389465)
        ·
          refine ⟨2662308900247892238292099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3549745200330522984389465 2662308900247892238292099)
          ·
            refine ⟨3993463350371838357438149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2662308900247892238292099 3993463350371838357438149)
            ·
              refine ⟨748774378194719692019653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3993463350371838357438149 748774378194719692019653)
              ·
                refine ⟨140395195911509942253685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 748774378194719692019653 140395195911509942253685)
                ·
                  rfl

theorem cell19_461394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 4].length) (baseStart_461394 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_461394 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_461394 prefixEnd_461394 := by exact prefixLift 461394
  have htrace : WordTrace (prefixWord ++ tailWord_461394) baseStart_461394 baseEnd_461394 := by
    simpa [prefixWord, tailWord_461394, baseEnd_461394] using wordTrace_append hprefix tailTrace_461394
  have hstable : (prefixWord ++ tailWord_461394).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461394).length < 2 ^ (prefixWord ++ tailWord_461394).sum := by decide
  have hdescent : baseEnd_461394 < baseStart_461394 := by decide
  rcases family_descends (prefixWord ++ tailWord_461394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461430 : List Nat := [5, 1, 1, 2, 4, 6]
def baseStart_461430 : Nat := 118140960795 + 461430 * 2 ^ 59
def prefixEnd_461430 : Nat := 4983230072969 + 3 ^ 40 * 461430 * 2
def baseEnd_461430 : Nat := 15600683351719169494843

theorem tailTrace_461430 : CollatzResearch.WordTrace tailWord_461430 prefixEnd_461430 15600683351719169494843 := by
  unfold tailWord_461430
  simp only [CollatzResearch.WordTrace]
  refine ⟨1051858419895336925940359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 11219823145550260543363829 1051858419895336925940359)
  ·
    refine ⟨1577787629843005388910539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1051858419895336925940359 1577787629843005388910539)
    ·
      refine ⟨2366681444764508083365809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1577787629843005388910539 2366681444764508083365809)
      ·
        refine ⟨1775011083573381062524357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2366681444764508083365809 1775011083573381062524357)
        ·
          refine ⟨332814578170008949223317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1775011083573381062524357 332814578170008949223317)
          ·
            refine ⟨15600683351719169494843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 332814578170008949223317 15600683351719169494843)
            ·
              rfl

theorem cell19_461430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 6].length) (baseStart_461430 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_461430 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_461430 prefixEnd_461430 := by exact prefixLift 461430
  have htrace : WordTrace (prefixWord ++ tailWord_461430) baseStart_461430 baseEnd_461430 := by
    simpa [prefixWord, tailWord_461430, baseEnd_461430] using wordTrace_append hprefix tailTrace_461430
  have hstable : (prefixWord ++ tailWord_461430).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461430).length < 2 ^ (prefixWord ++ tailWord_461430).sum := by decide
  have hdescent : baseEnd_461430 < baseStart_461430 := by decide
  rcases family_descends (prefixWord ++ tailWord_461430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_461466 : List Nat := [3, 1, 1, 6, 1, 1, 3, 3]
def baseStart_461466 : Nat := 118140960795 + 461466 * 2 ^ 59
def prefixEnd_461466 : Nat := 4983230072969 + 3 ^ 40 * 461466 * 2
def baseEnd_461466 : Nat := 140417104419435108653489

theorem tailTrace_461466 : CollatzResearch.WordTrace tailWord_461466 prefixEnd_461466 140417104419435108653489 := by
  unfold tailWord_461466
  simp only [CollatzResearch.WordTrace]
  refine ⟨4207761936548742240839063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 11220698497463312642237501 4207761936548742240839063)
  ·
    refine ⟨6311642904823113361258595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4207761936548742240839063 6311642904823113361258595)
    ·
      refine ⟨9467464357234670041887893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6311642904823113361258595 9467464357234670041887893)
      ·
        refine ⟨443787391745375158213495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 9467464357234670041887893 443787391745375158213495)
        ·
          refine ⟨665681087618062737320243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 443787391745375158213495 665681087618062737320243)
          ·
            refine ⟨998521631427094105980365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 665681087618062737320243 998521631427094105980365)
            ·
              refine ⟨374445611785160289742637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 998521631427094105980365 374445611785160289742637)
              ·
                refine ⟨140417104419435108653489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 374445611785160289742637 140417104419435108653489)
                ·
                  rfl

theorem cell19_461466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 3, 3].length) (baseStart_461466 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_461466 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_461466 prefixEnd_461466 := by exact prefixLift 461466
  have htrace : WordTrace (prefixWord ++ tailWord_461466) baseStart_461466 baseEnd_461466 := by
    simpa [prefixWord, tailWord_461466, baseEnd_461466] using wordTrace_append hprefix tailTrace_461466
  have hstable : (prefixWord ++ tailWord_461466).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_461466).length < 2 ^ (prefixWord ++ tailWord_461466).sum := by decide
  have hdescent : baseEnd_461466 < baseStart_461466 := by decide
  rcases family_descends (prefixWord ++ tailWord_461466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan19Incremental
