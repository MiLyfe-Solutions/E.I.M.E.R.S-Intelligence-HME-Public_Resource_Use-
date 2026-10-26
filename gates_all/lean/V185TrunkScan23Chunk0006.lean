import V185TrunkScan23Chunk0005

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_34318 : List Nat := [4, 1, 1, 2, 4, 2, 2, 1, 2, 1, 3]
def baseStart_34318 : Nat := 118140960795 + 34318 * 2 ^ 59
def prefixEnd_34318 : Nat := 4983230072969 + 3 ^ 40 * 34318 * 2
def baseEnd_34318 : Nat := 17621629101101964367181

theorem tailTrace_34318 : CollatzResearch.WordTrace tailWord_34318 prefixEnd_34318 17621629101101964367181 := by
  unfold tailWord_34318
  simp only [CollatzResearch.WordTrace]
  refine ⟨156460036209902736610951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 834453526452814595258405 156460036209902736610951)
  ·
    refine ⟨234690054314854104916427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156460036209902736610951 234690054314854104916427)
    ·
      refine ⟨352035081472281157374641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234690054314854104916427 352035081472281157374641)
      ·
        refine ⟨264026311104210868030981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 352035081472281157374641 264026311104210868030981)
        ·
          refine ⟨49504933332039537755809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 264026311104210868030981 49504933332039537755809)
          ·
            refine ⟨37128699999029653316857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49504933332039537755809 37128699999029653316857)
            ·
              refine ⟨27846524999272239987643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37128699999029653316857 27846524999272239987643)
              ·
                refine ⟨41769787498908359981465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27846524999272239987643 41769787498908359981465)
                ·
                  refine ⟨31327340624181269986099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41769787498908359981465 31327340624181269986099)
                  ·
                    refine ⟨46991010936271904979149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31327340624181269986099 46991010936271904979149)
                    ·
                      refine ⟨17621629101101964367181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 46991010936271904979149 17621629101101964367181)
                      ·
                        rfl

theorem cell23_34318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 2, 1, 2, 1, 3].length) (baseStart_34318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_34318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_34318 prefixEnd_34318 := by exact prefixLift 34318
  have htrace : WordTrace (prefixWord ++ tailWord_34318) baseStart_34318 baseEnd_34318 := by
    simpa [prefixWord, tailWord_34318, baseEnd_34318] using wordTrace_append hprefix tailTrace_34318
  have hstable : (prefixWord ++ tailWord_34318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34318).length < 2 ^ (prefixWord ++ tailWord_34318).sum := by decide
  have hdescent : baseEnd_34318 < baseStart_34318 := by decide
  rcases family_descends (prefixWord ++ tailWord_34318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34328 : List Nat := [2, 1, 2, 3, 5, 1, 1, 2, 1, 3, 2]
def baseStart_34328 : Nat := 118140960795 + 34328 * 2 ^ 59
def prefixEnd_34328 : Nat := 4983230072969 + 3 ^ 40 * 34328 * 2
def baseEnd_34328 : Nat := 17626763907646925242135

theorem tailTrace_34328 : CollatzResearch.WordTrace tailWord_34328 prefixEnd_34328 17626763907646925242135 := by
  unfold tailWord_34328
  simp only [CollatzResearch.WordTrace]
  refine ⟨626022509821496800375819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 834696679761995733834425 626022509821496800375819)
  ·
    refine ⟨939033764732245200563729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 626022509821496800375819 939033764732245200563729)
    ·
      refine ⟨704275323549183900422797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 939033764732245200563729 704275323549183900422797)
      ·
        refine ⟨264103246330943962658549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 704275323549183900422797 264103246330943962658549)
        ·
          refine ⟨24759679343525996499239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 264103246330943962658549 24759679343525996499239)
          ·
            refine ⟨37139519015288994748859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24759679343525996499239 37139519015288994748859)
            ·
              refine ⟨55709278522933492123289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37139519015288994748859 55709278522933492123289)
              ·
                refine ⟨41781958892200119092467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55709278522933492123289 41781958892200119092467)
                ·
                  refine ⟨62672938338300178638701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41781958892200119092467 62672938338300178638701)
                  ·
                    refine ⟨23502351876862566989513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 62672938338300178638701 23502351876862566989513)
                    ·
                      refine ⟨17626763907646925242135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 23502351876862566989513 17626763907646925242135)
                      ·
                        rfl

theorem cell23_34328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 2, 1, 3, 2].length) (baseStart_34328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_34328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_34328 prefixEnd_34328 := by exact prefixLift 34328
  have htrace : WordTrace (prefixWord ++ tailWord_34328) baseStart_34328 baseEnd_34328 := by
    simpa [prefixWord, tailWord_34328, baseEnd_34328] using wordTrace_append hprefix tailTrace_34328
  have hstable : (prefixWord ++ tailWord_34328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34328).length < 2 ^ (prefixWord ++ tailWord_34328).sum := by decide
  have hdescent : baseEnd_34328 < baseStart_34328 := by decide
  rcases family_descends (prefixWord ++ tailWord_34328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34364 : List Nat := [2, 2, 2, 2, 4, 1, 1, 4, 5]
def baseStart_34364 : Nat := 118140960795 + 34364 * 2 ^ 59
def prefixEnd_34364 : Nat := 4983230072969 + 3 ^ 40 * 34364 * 2
def baseEnd_34364 : Nat := 1960583245689864932441

theorem tailTrace_34364 : CollatzResearch.WordTrace tailWord_34364 prefixEnd_34364 1960583245689864932441 := by
  unfold tailWord_34364
  simp only [CollatzResearch.WordTrace]
  refine ⟨626679023756285874531073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 835572031675047832708097 626679023756285874531073)
  ·
    refine ⟨470009267817214405898305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 626679023756285874531073 470009267817214405898305)
    ·
      refine ⟨352506950862910804423729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 470009267817214405898305 352506950862910804423729)
      ·
        refine ⟨264380213147183103317797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 352506950862910804423729 264380213147183103317797)
        ·
          refine ⟨49571289965096831872087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 264380213147183103317797 49571289965096831872087)
          ·
            refine ⟨74356934947645247808131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49571289965096831872087 74356934947645247808131)
            ·
              refine ⟨111535402421467871712197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74356934947645247808131 111535402421467871712197)
              ·
                refine ⟨20912887954025225946037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 111535402421467871712197 20912887954025225946037)
                ·
                  refine ⟨1960583245689864932441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20912887954025225946037 1960583245689864932441)
                  ·
                    rfl

theorem cell23_34364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 4, 5].length) (baseStart_34364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_34364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_34364 prefixEnd_34364 := by exact prefixLift 34364
  have htrace : WordTrace (prefixWord ++ tailWord_34364) baseStart_34364 baseEnd_34364 := by
    simpa [prefixWord, tailWord_34364, baseEnd_34364] using wordTrace_append hprefix tailTrace_34364
  have hstable : (prefixWord ++ tailWord_34364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34364).length < 2 ^ (prefixWord ++ tailWord_34364).sum := by decide
  have hdescent : baseEnd_34364 < baseStart_34364 := by decide
  rcases family_descends (prefixWord ++ tailWord_34364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34367 : List Nat := [1, 1, 2, 2, 3, 3, 1, 1, 2, 5, 2]
def baseStart_34367 : Nat := 118140960795 + 34367 * 2 ^ 59
def prefixEnd_34367 : Nat := 4983230072969 + 3 ^ 40 * 34367 * 2
def baseEnd_34367 : Nat := 17646789653172272654455

theorem tailTrace_34367 : CollatzResearch.WordTrace tailWord_34367 prefixEnd_34367 17646789653172272654455 := by
  unfold tailWord_34367
  simp only [CollatzResearch.WordTrace]
  refine ⟨1253467466501703261421355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 835644977667802174280903 1253467466501703261421355)
  ·
    refine ⟨1880201199752554892132033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1253467466501703261421355 1880201199752554892132033)
    ·
      refine ⟨1410150899814416169099025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1880201199752554892132033 1410150899814416169099025)
      ·
        refine ⟨1057613174860812126824269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1410150899814416169099025 1057613174860812126824269)
        ·
          refine ⟨396604940572804547559101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1057613174860812126824269 396604940572804547559101)
          ·
            refine ⟨148726852714801705334663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 396604940572804547559101 148726852714801705334663)
            ·
              refine ⟨223090279072202558001995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148726852714801705334663 223090279072202558001995)
              ·
                refine ⟨334635418608303837002993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 223090279072202558001995 334635418608303837002993)
                ·
                  refine ⟨250976563956227877752245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 334635418608303837002993 250976563956227877752245)
                  ·
                    refine ⟨23529052870896363539273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 250976563956227877752245 23529052870896363539273)
                    ·
                      refine ⟨17646789653172272654455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 23529052870896363539273 17646789653172272654455)
                      ·
                        rfl

theorem cell23_34367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 2, 5, 2].length) (baseStart_34367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_34367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_34367 prefixEnd_34367 := by exact prefixLift 34367
  have htrace : WordTrace (prefixWord ++ tailWord_34367) baseStart_34367 baseEnd_34367 := by
    simpa [prefixWord, tailWord_34367, baseEnd_34367] using wordTrace_append hprefix tailTrace_34367
  have hstable : (prefixWord ++ tailWord_34367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34367).length < 2 ^ (prefixWord ++ tailWord_34367).sum := by decide
  have hdescent : baseEnd_34367 < baseStart_34367 := by decide
  rcases family_descends (prefixWord ++ tailWord_34367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34417 : List Nat := [1, 2, 2, 2, 1, 1, 1, 6, 2, 2, 3]
def baseStart_34417 : Nat := 118140960795 + 34417 * 2 ^ 59
def prefixEnd_34417 : Nat := 4983230072969 + 3 ^ 40 * 34417 * 2
def baseEnd_34417 : Nat := 17672463685897077029225

theorem tailTrace_34417 : CollatzResearch.WordTrace tailWord_34417 prefixEnd_34417 17672463685897077029225 := by
  unfold tailWord_34417
  simp only [CollatzResearch.WordTrace]
  refine ⟨1255291116320561800741505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 836860744213707867161003 1255291116320561800741505)
  ·
    refine ⟨941468337240421350556129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1255291116320561800741505 941468337240421350556129)
    ·
      refine ⟨706101252930316012917097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 941468337240421350556129 706101252930316012917097)
      ·
        refine ⟨529575939697737009687823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 706101252930316012917097 529575939697737009687823)
        ·
          refine ⟨794363909546605514531735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 529575939697737009687823 794363909546605514531735)
          ·
            refine ⟨1191545864319908271797603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 794363909546605514531735 1191545864319908271797603)
            ·
              refine ⟨1787318796479862407696405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1191545864319908271797603 1787318796479862407696405)
              ·
                refine ⟨83780568584993550360769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1787318796479862407696405 83780568584993550360769)
                ·
                  refine ⟨62835426438745162770577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83780568584993550360769 62835426438745162770577)
                  ·
                    refine ⟨47126569829058872077933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 62835426438745162770577 47126569829058872077933)
                    ·
                      refine ⟨17672463685897077029225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 47126569829058872077933 17672463685897077029225)
                      ·
                        rfl

theorem cell23_34417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 6, 2, 2, 3].length) (baseStart_34417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_34417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_34417 prefixEnd_34417 := by exact prefixLift 34417
  have htrace : WordTrace (prefixWord ++ tailWord_34417) baseStart_34417 baseEnd_34417 := by
    simpa [prefixWord, tailWord_34417, baseEnd_34417] using wordTrace_append hprefix tailTrace_34417
  have hstable : (prefixWord ++ tailWord_34417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34417).length < 2 ^ (prefixWord ++ tailWord_34417).sum := by decide
  have hdescent : baseEnd_34417 < baseStart_34417 := by decide
  rcases family_descends (prefixWord ++ tailWord_34417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34467 : List Nat := [1, 1, 1, 4, 1, 1, 3, 5, 1, 5]
def baseStart_34467 : Nat := 118140960795 + 34467 * 2 ^ 59
def prefixEnd_34467 : Nat := 4983230072969 + 3 ^ 40 * 34467 * 2
def baseEnd_34467 : Nat := 5899379239540627134665

theorem tailTrace_34467 : CollatzResearch.WordTrace tailWord_34467 prefixEnd_34467 5899379239540627134665 := by
  unfold tailWord_34467
  simp only [CollatzResearch.WordTrace]
  refine ⟨1257114766139420340061655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 838076510759613560041103 1257114766139420340061655)
  ·
    refine ⟨1885672149209130510092483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1257114766139420340061655 1885672149209130510092483)
    ·
      refine ⟨2828508223813695765138725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1885672149209130510092483 2828508223813695765138725)
      ·
        refine ⟨530345291965067955963511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2828508223813695765138725 530345291965067955963511)
        ·
          refine ⟨795517937947601933945267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 530345291965067955963511 795517937947601933945267)
          ·
            refine ⟨1193276906921402900917901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 795517937947601933945267 1193276906921402900917901)
            ·
              refine ⟨447478840095526087844213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1193276906921402900917901 447478840095526087844213)
              ·
                refine ⟨41951141258955570735395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 447478840095526087844213 41951141258955570735395)
                ·
                  refine ⟨62926711888433356103093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41951141258955570735395 62926711888433356103093)
                  ·
                    refine ⟨5899379239540627134665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 62926711888433356103093 5899379239540627134665)
                    ·
                      rfl

theorem cell23_34467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 5, 1, 5].length) (baseStart_34467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_34467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_34467 prefixEnd_34467 := by exact prefixLift 34467
  have htrace : WordTrace (prefixWord ++ tailWord_34467) baseStart_34467 baseEnd_34467 := by
    simpa [prefixWord, tailWord_34467, baseEnd_34467] using wordTrace_append hprefix tailTrace_34467
  have hstable : (prefixWord ++ tailWord_34467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34467).length < 2 ^ (prefixWord ++ tailWord_34467).sum := by decide
  have hdescent : baseEnd_34467 < baseStart_34467 := by decide
  rcases family_descends (prefixWord ++ tailWord_34467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34508 : List Nat := [2, 2, 1, 5, 2, 1, 2, 1, 2, 3, 2]
def baseStart_34508 : Nat := 118140960795 + 34508 * 2 ^ 59
def prefixEnd_34508 : Nat := 4983230072969 + 3 ^ 40 * 34508 * 2
def baseEnd_34508 : Nat := 17719190425456220991307

theorem tailTrace_34508 : CollatzResearch.WordTrace tailWord_34508 prefixEnd_34508 17719190425456220991307 := by
  unfold tailWord_34508
  simp only [CollatzResearch.WordTrace]
  refine ⟨629305079495442171152089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 839073439327256228202785 629305079495442171152089)
  ·
    refine ⟨471978809621581628364067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 629305079495442171152089 471978809621581628364067)
    ·
      refine ⟨707968214432372442546101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 471978809621581628364067 707968214432372442546101)
      ·
        refine ⟨66372020103034916488697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 707968214432372442546101 66372020103034916488697)
        ·
          refine ⟨49779015077276187366523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66372020103034916488697 49779015077276187366523)
          ·
            refine ⟨74668522615914281049785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49779015077276187366523 74668522615914281049785)
            ·
              refine ⟨56001391961935710787339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74668522615914281049785 56001391961935710787339)
              ·
                refine ⟨84002087942903566181009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56001391961935710787339 84002087942903566181009)
                ·
                  refine ⟨63001565957177674635757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 84002087942903566181009 63001565957177674635757)
                  ·
                    refine ⟨23625587233941627988409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 63001565957177674635757 23625587233941627988409)
                    ·
                      refine ⟨17719190425456220991307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 23625587233941627988409 17719190425456220991307)
                      ·
                        rfl

theorem cell23_34508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_34508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_34508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_34508 prefixEnd_34508 := by exact prefixLift 34508
  have htrace : WordTrace (prefixWord ++ tailWord_34508) baseStart_34508 baseEnd_34508 := by
    simpa [prefixWord, tailWord_34508, baseEnd_34508] using wordTrace_append hprefix tailTrace_34508
  have hstable : (prefixWord ++ tailWord_34508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34508).length < 2 ^ (prefixWord ++ tailWord_34508).sum := by decide
  have hdescent : baseEnd_34508 < baseStart_34508 := by decide
  rcases family_descends (prefixWord ++ tailWord_34508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34514 : List Nat := [3, 2, 2, 2, 2, 2, 1, 2, 1, 6]
def baseStart_34514 : Nat := 118140960795 + 34514 * 2 ^ 59
def prefixEnd_34514 : Nat := 4983230072969 + 3 ^ 40 * 34514 * 2
def baseEnd_34514 : Nat := 5907423769794399172093

theorem tailTrace_34514 : CollatzResearch.WordTrace tailWord_34514 prefixEnd_34514 5907423769794399172093 := by
  unfold tailWord_34514
  simp only [CollatzResearch.WordTrace]
  refine ⟨314707249242286841755649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 839219331312764911348397 314707249242286841755649)
  ·
    refine ⟨236030436931715131316737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 314707249242286841755649 236030436931715131316737)
    ·
      refine ⟨177022827698786348487553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 236030436931715131316737 177022827698786348487553)
      ·
        refine ⟨132767120774089761365665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 177022827698786348487553 132767120774089761365665)
        ·
          refine ⟨99575340580567321024249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132767120774089761365665 99575340580567321024249)
          ·
            refine ⟨74681505435425490768187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99575340580567321024249 74681505435425490768187)
            ·
              refine ⟨112022258153138236152281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74681505435425490768187 112022258153138236152281)
              ·
                refine ⟨84016693614853677114211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 112022258153138236152281 84016693614853677114211)
                ·
                  refine ⟨126025040422280515671317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 84016693614853677114211 126025040422280515671317)
                  ·
                    refine ⟨5907423769794399172093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 126025040422280515671317 5907423769794399172093)
                    ·
                      rfl

theorem cell23_34514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 2, 1, 6].length) (baseStart_34514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_34514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_34514 prefixEnd_34514 := by exact prefixLift 34514
  have htrace : WordTrace (prefixWord ++ tailWord_34514) baseStart_34514 baseEnd_34514 := by
    simpa [prefixWord, tailWord_34514, baseEnd_34514] using wordTrace_append hprefix tailTrace_34514
  have hstable : (prefixWord ++ tailWord_34514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34514).length < 2 ^ (prefixWord ++ tailWord_34514).sum := by decide
  have hdescent : baseEnd_34514 < baseStart_34514 := by decide
  rcases family_descends (prefixWord ++ tailWord_34514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34521 : List Nat := [1, 2, 1, 2, 3, 4, 3, 1, 1, 1, 4]
def baseStart_34521 : Nat := 118140960795 + 34521 * 2 ^ 59
def prefixEnd_34521 : Nat := 4983230072969 + 3 ^ 40 * 34521 * 2
def baseEnd_34521 : Nat := 17725865673964670128747

theorem tailTrace_34521 : CollatzResearch.WordTrace tailWord_34521 prefixEnd_34521 17725865673964670128747 := by
  unfold tailWord_34521
  simp only [CollatzResearch.WordTrace]
  refine ⟨1259084307943787562527417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 839389538629191708351611 1259084307943787562527417)
  ·
    refine ⟨944313230957840671895563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1259084307943787562527417 944313230957840671895563)
    ·
      refine ⟨1416469846436761007843345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 944313230957840671895563 1416469846436761007843345)
      ·
        refine ⟨1062352384827570755882509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1416469846436761007843345 1062352384827570755882509)
        ·
          refine ⟨398382144310339033455941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1062352384827570755882509 398382144310339033455941)
          ·
            refine ⟨74696652058188568772989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 398382144310339033455941 74696652058188568772989)
            ·
              refine ⟨28011244521820713289871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74696652058188568772989 28011244521820713289871)
              ·
                refine ⟨42016866782731069934807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28011244521820713289871 42016866782731069934807)
                ·
                  refine ⟨63025300174096604902211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42016866782731069934807 63025300174096604902211)
                  ·
                    refine ⟨94537950261144907353317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 63025300174096604902211 94537950261144907353317)
                    ·
                      refine ⟨17725865673964670128747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 94537950261144907353317 17725865673964670128747)
                      ·
                        rfl

theorem cell23_34521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 3, 1, 1, 1, 4].length) (baseStart_34521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_34521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_34521 prefixEnd_34521 := by exact prefixLift 34521
  have htrace : WordTrace (prefixWord ++ tailWord_34521) baseStart_34521 baseEnd_34521 := by
    simpa [prefixWord, tailWord_34521, baseEnd_34521] using wordTrace_append hprefix tailTrace_34521
  have hstable : (prefixWord ++ tailWord_34521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34521).length < 2 ^ (prefixWord ++ tailWord_34521).sum := by decide
  have hdescent : baseEnd_34521 < baseStart_34521 := by decide
  rcases family_descends (prefixWord ++ tailWord_34521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34537 : List Nat := [1, 2, 1, 1, 1, 2, 3, 1, 5, 3, 3]
def baseStart_34537 : Nat := 118140960795 + 34537 * 2 ^ 59
def prefixEnd_34537 : Nat := 4983230072969 + 3 ^ 40 * 34537 * 2
def baseEnd_34537 : Nat := 17734081364436607528673

theorem tailTrace_34537 : CollatzResearch.WordTrace tailWord_34537 prefixEnd_34537 17734081364436607528673 := by
  unfold tailWord_34537
  simp only [CollatzResearch.WordTrace]
  refine ⟨1259667875885822295109865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 839778583923881530073243 1259667875885822295109865)
  ·
    refine ⟨944750906914366721332399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1259667875885822295109865 944750906914366721332399)
    ·
      refine ⟨1417126360371550081998599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 944750906914366721332399 1417126360371550081998599)
      ·
        refine ⟨2125689540557325122997899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1417126360371550081998599 2125689540557325122997899)
        ·
          refine ⟨3188534310835987684496849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2125689540557325122997899 3188534310835987684496849)
          ·
            refine ⟨2391400733126990763372637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3188534310835987684496849 2391400733126990763372637)
            ·
              refine ⟨896775274922621536264739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2391400733126990763372637 896775274922621536264739)
              ·
                refine ⟨1345162912383932304397109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 896775274922621536264739 1345162912383932304397109)
                ·
                  refine ⟨126109023035993653537229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1345162912383932304397109 126109023035993653537229)
                  ·
                    refine ⟨47290883638497620076461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 126109023035993653537229 47290883638497620076461)
                    ·
                      refine ⟨17734081364436607528673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 47290883638497620076461 17734081364436607528673)
                      ·
                        rfl

theorem cell23_34537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 5, 3, 3].length) (baseStart_34537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_34537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_34537 prefixEnd_34537 := by exact prefixLift 34537
  have htrace : WordTrace (prefixWord ++ tailWord_34537) baseStart_34537 baseEnd_34537 := by
    simpa [prefixWord, tailWord_34537, baseEnd_34537] using wordTrace_append hprefix tailTrace_34537
  have hstable : (prefixWord ++ tailWord_34537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34537).length < 2 ^ (prefixWord ++ tailWord_34537).sum := by decide
  have hdescent : baseEnd_34537 < baseStart_34537 := by decide
  rcases family_descends (prefixWord ++ tailWord_34537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34548 : List Nat := [2, 6, 1, 1, 1, 2, 2, 1, 1, 6]
def baseStart_34548 : Nat := 118140960795 + 34548 * 2 ^ 59
def prefixEnd_34548 : Nat := 4983230072969 + 3 ^ 40 * 34548 * 2
def baseEnd_34548 : Nat := 5913243217212021497041

theorem tailTrace_34548 : CollatzResearch.WordTrace tailWord_34548 prefixEnd_34548 5913243217212021497041 := by
  unfold tailWord_34548
  simp only [CollatzResearch.WordTrace]
  refine ⟨630034539422985586880149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 840046052563980782506865 630034539422985586880149)
  ·
    refine ⟨29532869035452449385007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 630034539422985586880149 29532869035452449385007)
    ·
      refine ⟨44299303553178674077511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29532869035452449385007 44299303553178674077511)
      ·
        refine ⟨66448955329768011116267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44299303553178674077511 66448955329768011116267)
        ·
          refine ⟨99673432994652016674401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66448955329768011116267 99673432994652016674401)
          ·
            refine ⟨74755074745989012505801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99673432994652016674401 74755074745989012505801)
            ·
              refine ⟨56066306059491759379351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74755074745989012505801 56066306059491759379351)
              ·
                refine ⟨84099459089237639069027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56066306059491759379351 84099459089237639069027)
                ·
                  refine ⟨126149188633856458603541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 84099459089237639069027 126149188633856458603541)
                  ·
                    refine ⟨5913243217212021497041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 126149188633856458603541 5913243217212021497041)
                    ·
                      rfl

theorem cell23_34548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_34548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_34548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_34548 prefixEnd_34548 := by exact prefixLift 34548
  have htrace : WordTrace (prefixWord ++ tailWord_34548) baseStart_34548 baseEnd_34548 := by
    simpa [prefixWord, tailWord_34548, baseEnd_34548] using wordTrace_append hprefix tailTrace_34548
  have hstable : (prefixWord ++ tailWord_34548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34548).length < 2 ^ (prefixWord ++ tailWord_34548).sum := by decide
  have hdescent : baseEnd_34548 < baseStart_34548 := by decide
  rcases family_descends (prefixWord ++ tailWord_34548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34554 : List Nat := [3, 1, 1, 1, 1, 3, 1, 2, 6, 1, 3]
def baseStart_34554 : Nat := 118140960795 + 34554 * 2 ^ 59
def prefixEnd_34554 : Nat := 4983230072969 + 3 ^ 40 * 34554 * 2
def baseEnd_34554 : Nat := 17742810535563041016095

theorem tailTrace_34554 : CollatzResearch.WordTrace tailWord_34554 prefixEnd_34554 17742810535563041016095 := by
  unfold tailWord_34554
  simp only [CollatzResearch.WordTrace]
  refine ⟨315071979206058549619679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 840191944549489465652477 315071979206058549619679)
  ·
    refine ⟨472607968809087824429519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 315071979206058549619679 472607968809087824429519)
    ·
      refine ⟨708911953213631736644279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 472607968809087824429519 708911953213631736644279)
      ·
        refine ⟨1063367929820447604966419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 708911953213631736644279 1063367929820447604966419)
        ·
          refine ⟨1595051894730671407449629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1063367929820447604966419 1595051894730671407449629)
          ·
            refine ⟨598144460524001777793611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1595051894730671407449629 598144460524001777793611)
            ·
              refine ⟨897216690786002666690417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 598144460524001777793611 897216690786002666690417)
              ·
                refine ⟨672912518089502000017813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 897216690786002666690417 672912518089502000017813)
                ·
                  refine ⟨31542774285445406250835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 672912518089502000017813 31542774285445406250835)
                  ·
                    refine ⟨47314161428168109376253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31542774285445406250835 47314161428168109376253)
                    ·
                      refine ⟨17742810535563041016095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 47314161428168109376253 17742810535563041016095)
                      ·
                        rfl

theorem cell23_34554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 6, 1, 3].length) (baseStart_34554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_34554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_34554 prefixEnd_34554 := by exact prefixLift 34554
  have htrace : WordTrace (prefixWord ++ tailWord_34554) baseStart_34554 baseEnd_34554 := by
    simpa [prefixWord, tailWord_34554, baseEnd_34554] using wordTrace_append hprefix tailTrace_34554
  have hstable : (prefixWord ++ tailWord_34554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34554).length < 2 ^ (prefixWord ++ tailWord_34554).sum := by decide
  have hdescent : baseEnd_34554 < baseStart_34554 := by decide
  rcases family_descends (prefixWord ++ tailWord_34554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34664 : List Nat := [2, 1, 4, 2, 1, 1, 1, 2, 4, 5]
def baseStart_34664 : Nat := 118140960795 + 34664 * 2 ^ 59
def prefixEnd_34664 : Nat := 4983230072969 + 3 ^ 40 * 34664 * 2
def baseEnd_34664 : Nat := 5933097802519203546863

theorem tailTrace_34664 : CollatzResearch.WordTrace tailWord_34664 prefixEnd_34664 5933097802519203546863 := by
  unfold tailWord_34664
  simp only [CollatzResearch.WordTrace]
  refine ⟨632149973212861492491523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 842866630950481989988697 632149973212861492491523)
  ·
    refine ⟨948224959819292238737285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 632149973212861492491523 948224959819292238737285)
    ·
      refine ⟨177792179966117294763241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 948224959819292238737285 177792179966117294763241)
      ·
        refine ⟨133344134974587971072431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 177792179966117294763241 133344134974587971072431)
        ·
          refine ⟨200016202461881956608647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133344134974587971072431 200016202461881956608647)
          ·
            refine ⟨300024303692822934912971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 200016202461881956608647 300024303692822934912971)
            ·
              refine ⟨450036455539234402369457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 300024303692822934912971 450036455539234402369457)
              ·
                refine ⟨337527341654425801777093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 450036455539234402369457 337527341654425801777093)
                ·
                  refine ⟨63286376560204837833205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 337527341654425801777093 63286376560204837833205)
                  ·
                    refine ⟨5933097802519203546863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 63286376560204837833205 5933097802519203546863)
                    ·
                      rfl

theorem cell23_34664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 4, 5].length) (baseStart_34664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_34664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_34664 prefixEnd_34664 := by exact prefixLift 34664
  have htrace : WordTrace (prefixWord ++ tailWord_34664) baseStart_34664 baseEnd_34664 := by
    simpa [prefixWord, tailWord_34664, baseEnd_34664] using wordTrace_append hprefix tailTrace_34664
  have hstable : (prefixWord ++ tailWord_34664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34664).length < 2 ^ (prefixWord ++ tailWord_34664).sum := by decide
  have hdescent : baseEnd_34664 < baseStart_34664 := by decide
  rcases family_descends (prefixWord ++ tailWord_34664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34702 : List Nat := [4, 1, 1, 5, 1, 2, 2, 2, 5]
def baseStart_34702 : Nat := 118140960795 + 34702 * 2 ^ 59
def prefixEnd_34702 : Nat := 4983230072969 + 3 ^ 40 * 34702 * 2
def baseEnd_34702 : Nat := 1979867296936495773935

theorem tailTrace_34702 : CollatzResearch.WordTrace tailWord_34702 prefixEnd_34702 1979867296936495773935 := by
  unfold tailWord_34702
  simp only [CollatzResearch.WordTrace]
  refine ⟨158210740036006934358295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 843790613525370316577573 158210740036006934358295)
  ·
    refine ⟨237316110054010401537443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158210740036006934358295 237316110054010401537443)
    ·
      refine ⟨355974165081015602306165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 237316110054010401537443 355974165081015602306165)
      ·
        refine ⟨33372577976345212716203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 355974165081015602306165 33372577976345212716203)
        ·
          refine ⟨50058866964517819074305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33372577976345212716203 50058866964517819074305)
          ·
            refine ⟨37544150223388364305729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50058866964517819074305 37544150223388364305729)
            ·
              refine ⟨28158112667541273229297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37544150223388364305729 28158112667541273229297)
              ·
                refine ⟨21118584500655954921973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28158112667541273229297 21118584500655954921973)
                ·
                  refine ⟨1979867296936495773935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21118584500655954921973 1979867296936495773935)
                  ·
                    rfl

theorem cell23_34702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 2, 2, 5].length) (baseStart_34702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_34702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_34702 prefixEnd_34702 := by exact prefixLift 34702
  have htrace : WordTrace (prefixWord ++ tailWord_34702) baseStart_34702 baseEnd_34702 := by
    simpa [prefixWord, tailWord_34702, baseEnd_34702] using wordTrace_append hprefix tailTrace_34702
  have hstable : (prefixWord ++ tailWord_34702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34702).length < 2 ^ (prefixWord ++ tailWord_34702).sum := by decide
  have hdescent : baseEnd_34702 < baseStart_34702 := by decide
  rcases family_descends (prefixWord ++ tailWord_34702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34707 : List Nat := [1, 1, 1, 2, 1, 2, 1, 2, 12]
def baseStart_34707 : Nat := 118140960795 + 34707 * 2 ^ 59
def prefixEnd_34707 : Nat := 4983230072969 + 3 ^ 40 * 34707 * 2
def baseEnd_34707 : Nat := 1980152563966771378099

theorem tailTrace_34707 : CollatzResearch.WordTrace tailWord_34707 prefixEnd_34707 1980152563966771378099 := by
  unfold tailWord_34707
  simp only [CollatzResearch.WordTrace]
  refine ⟨1265868285269941328798375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 843912190179960885865583 1265868285269941328798375)
  ·
    refine ⟨1898802427904911993197563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1265868285269941328798375 1898802427904911993197563)
    ·
      refine ⟨2848203641857367989796345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1898802427904911993197563 2848203641857367989796345)
      ·
        refine ⟨2136152731393025992347259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2848203641857367989796345 2136152731393025992347259)
        ·
          refine ⟨3204229097089538988520889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2136152731393025992347259 3204229097089538988520889)
          ·
            refine ⟨2403171822817154241390667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3204229097089538988520889 2403171822817154241390667)
            ·
              refine ⟨3604757734225731362086001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2403171822817154241390667 3604757734225731362086001)
              ·
                refine ⟨2703568300669298521564501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3604757734225731362086001 2703568300669298521564501)
                ·
                  refine ⟨1980152563966771378099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 2703568300669298521564501 1980152563966771378099)
                  ·
                    rfl

theorem cell23_34707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 12].length) (baseStart_34707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_34707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_34707 prefixEnd_34707 := by exact prefixLift 34707
  have htrace : WordTrace (prefixWord ++ tailWord_34707) baseStart_34707 baseEnd_34707 := by
    simpa [prefixWord, tailWord_34707, baseEnd_34707] using wordTrace_append hprefix tailTrace_34707
  have hstable : (prefixWord ++ tailWord_34707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34707).length < 2 ^ (prefixWord ++ tailWord_34707).sum := by decide
  have hdescent : baseEnd_34707 < baseStart_34707 := by decide
  rcases family_descends (prefixWord ++ tailWord_34707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34751 : List Nat := [1, 1, 2, 2, 2, 1, 3, 2, 5, 1, 3]
def baseStart_34751 : Nat := 118140960795 + 34751 * 2 ^ 59
def prefixEnd_34751 : Nat := 4983230072969 + 3 ^ 40 * 34751 * 2
def baseEnd_34751 : Nat := 17843966224498770252689

theorem tailTrace_34751 : CollatzResearch.WordTrace tailWord_34751 prefixEnd_34751 17843966224498770252689 := by
  unfold tailWord_34751
  simp only [CollatzResearch.WordTrace]
  refine ⟨1267473097110536843400107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 844982064740357895600071 1267473097110536843400107)
  ·
    refine ⟨1901209645665805265100161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1267473097110536843400107 1901209645665805265100161)
    ·
      refine ⟨1425907234249353948825121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1901209645665805265100161 1425907234249353948825121)
      ·
        refine ⟨1069430425687015461618841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1425907234249353948825121 1069430425687015461618841)
        ·
          refine ⟨802072819265261596214131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1069430425687015461618841 802072819265261596214131)
          ·
            refine ⟨1203109228897892394321197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 802072819265261596214131 1203109228897892394321197)
            ·
              refine ⟨451165960836709647870449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1203109228897892394321197 451165960836709647870449)
              ·
                refine ⟨338374470627532235902837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 451165960836709647870449 338374470627532235902837)
                ·
                  refine ⟨31722606621331147115891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 338374470627532235902837 31722606621331147115891)
                  ·
                    refine ⟨47583909931996720673837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31722606621331147115891 47583909931996720673837)
                    ·
                      refine ⟨17843966224498770252689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 47583909931996720673837 17843966224498770252689)
                      ·
                        rfl

theorem cell23_34751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 5, 1, 3].length) (baseStart_34751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_34751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_34751 prefixEnd_34751 := by exact prefixLift 34751
  have htrace : WordTrace (prefixWord ++ tailWord_34751) baseStart_34751 baseEnd_34751 := by
    simpa [prefixWord, tailWord_34751, baseEnd_34751] using wordTrace_append hprefix tailTrace_34751
  have hstable : (prefixWord ++ tailWord_34751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34751).length < 2 ^ (prefixWord ++ tailWord_34751).sum := by decide
  have hdescent : baseEnd_34751 < baseStart_34751 := by decide
  rcases family_descends (prefixWord ++ tailWord_34751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34808 : List Nat := [2, 1, 2, 1, 1, 3, 2, 2, 5, 2, 2]
def baseStart_34808 : Nat := 118140960795 + 34808 * 2 ^ 59
def prefixEnd_34808 : Nat := 4983230072969 + 3 ^ 40 * 34808 * 2
def baseEnd_34808 : Nat := 17873234621805047239927

theorem tailTrace_34808 : CollatzResearch.WordTrace tailWord_34808 prefixEnd_34808 17873234621805047239927 := by
  unfold tailWord_34808
  simp only [CollatzResearch.WordTrace]
  refine ⟨634776028952017789112539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 846368038602690385483385 634776028952017789112539)
  ·
    refine ⟨952164043428026683668809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 634776028952017789112539 952164043428026683668809)
    ·
      refine ⟨714123032571020012751607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 952164043428026683668809 714123032571020012751607)
      ·
        refine ⟨1071184548856530019127411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 714123032571020012751607 1071184548856530019127411)
        ·
          refine ⟨1606776823284795028691117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1071184548856530019127411 1606776823284795028691117)
          ·
            refine ⟨602541308731798135759169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1606776823284795028691117 602541308731798135759169)
            ·
              refine ⟨451905981548848601819377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 602541308731798135759169 451905981548848601819377)
              ·
                refine ⟨338929486161636451364533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 451905981548848601819377 338929486161636451364533)
                ·
                  refine ⟨31774639327653417315425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 338929486161636451364533 31774639327653417315425)
                  ·
                    refine ⟨23830979495740062986569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31774639327653417315425 23830979495740062986569)
                    ·
                      refine ⟨17873234621805047239927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 23830979495740062986569 17873234621805047239927)
                      ·
                        rfl

theorem cell23_34808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 5, 2, 2].length) (baseStart_34808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_34808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_34808 prefixEnd_34808 := by exact prefixLift 34808
  have htrace : WordTrace (prefixWord ++ tailWord_34808) baseStart_34808 baseEnd_34808 := by
    simpa [prefixWord, tailWord_34808, baseEnd_34808] using wordTrace_append hprefix tailTrace_34808
  have hstable : (prefixWord ++ tailWord_34808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34808).length < 2 ^ (prefixWord ++ tailWord_34808).sum := by decide
  have hdescent : baseEnd_34808 < baseStart_34808 := by decide
  rcases family_descends (prefixWord ++ tailWord_34808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34841 : List Nat := [1, 2, 1, 2, 1, 1, 3, 5, 1, 3, 3]
def baseStart_34841 : Nat := 118140960795 + 34841 * 2 ^ 59
def prefixEnd_34841 : Nat := 4983230072969 + 3 ^ 40 * 34841 * 2
def baseEnd_34841 : Nat := 17890179483403418127275

theorem tailTrace_34841 : CollatzResearch.WordTrace tailWord_34841 prefixEnd_34841 17890179483403418127275 := by
  unfold tailWord_34841
  simp only [CollatzResearch.WordTrace]
  refine ⟨1270755666784482214176377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 847170444522988142784251 1270755666784482214176377)
  ·
    refine ⟨953066750088361660632283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1270755666784482214176377 953066750088361660632283)
    ·
      refine ⟨1429600125132542490948425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 953066750088361660632283 1429600125132542490948425)
      ·
        refine ⟨1072200093849406868211319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1429600125132542490948425 1072200093849406868211319)
        ·
          refine ⟨1608300140774110302316979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1072200093849406868211319 1608300140774110302316979)
          ·
            refine ⟨2412450211161165453475469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1608300140774110302316979 2412450211161165453475469)
            ·
              refine ⟨904668829185437045053301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2412450211161165453475469 904668829185437045053301)
              ·
                refine ⟨84812702736134722973747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 904668829185437045053301 84812702736134722973747)
                ·
                  refine ⟨127219054104202084460621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 84812702736134722973747 127219054104202084460621)
                  ·
                    refine ⟨47707145289075781672733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 127219054104202084460621 47707145289075781672733)
                    ·
                      refine ⟨17890179483403418127275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 47707145289075781672733 17890179483403418127275)
                      ·
                        rfl

theorem cell23_34841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 5, 1, 3, 3].length) (baseStart_34841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_34841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_34841 prefixEnd_34841 := by exact prefixLift 34841
  have htrace : WordTrace (prefixWord ++ tailWord_34841) baseStart_34841 baseEnd_34841 := by
    simpa [prefixWord, tailWord_34841, baseEnd_34841] using wordTrace_append hprefix tailTrace_34841
  have hstable : (prefixWord ++ tailWord_34841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34841).length < 2 ^ (prefixWord ++ tailWord_34841).sum := by decide
  have hdescent : baseEnd_34841 < baseStart_34841 := by decide
  rcases family_descends (prefixWord ++ tailWord_34841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34845 : List Nat := [1, 4, 2, 2, 2, 1, 3, 2, 1, 2, 3]
def baseStart_34845 : Nat := 118140960795 + 34845 * 2 ^ 59
def prefixEnd_34845 : Nat := 4983230072969 + 3 ^ 40 * 34845 * 2
def baseEnd_34845 : Nat := 17892233406021402477257

theorem tailTrace_34845 : CollatzResearch.WordTrace tailWord_34845 prefixEnd_34845 17892233406021402477257 := by
  unfold tailWord_34845
  simp only [CollatzResearch.WordTrace]
  refine ⟨1270901558769990897321989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 847267705846660598214659 1270901558769990897321989)
  ·
    refine ⟨238294042269373293247873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1270901558769990897321989 238294042269373293247873)
    ·
      refine ⟨178720531702029969935905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 238294042269373293247873 178720531702029969935905)
      ·
        refine ⟨134040398776522477451929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 178720531702029969935905 134040398776522477451929)
        ·
          refine ⟨100530299082391858088947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134040398776522477451929 100530299082391858088947)
          ·
            refine ⟨150795448623587787133421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100530299082391858088947 150795448623587787133421)
            ·
              refine ⟨56548293233845420175033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 150795448623587787133421 56548293233845420175033)
              ·
                refine ⟨42411219925384065131275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56548293233845420175033 42411219925384065131275)
                ·
                  refine ⟨63616829888076097696913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42411219925384065131275 63616829888076097696913)
                  ·
                    refine ⟨47712622416057073272685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 63616829888076097696913 47712622416057073272685)
                    ·
                      refine ⟨17892233406021402477257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 47712622416057073272685 17892233406021402477257)
                      ·
                        rfl

theorem cell23_34845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_34845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_34845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_34845 prefixEnd_34845 := by exact prefixLift 34845
  have htrace : WordTrace (prefixWord ++ tailWord_34845) baseStart_34845 baseEnd_34845 := by
    simpa [prefixWord, tailWord_34845, baseEnd_34845] using wordTrace_append hprefix tailTrace_34845
  have hstable : (prefixWord ++ tailWord_34845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34845).length < 2 ^ (prefixWord ++ tailWord_34845).sum := by decide
  have hdescent : baseEnd_34845 < baseStart_34845 := by decide
  rcases family_descends (prefixWord ++ tailWord_34845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34855 : List Nat := [1, 1, 7, 1, 2, 1, 1, 2, 1, 2, 4]
def baseStart_34855 : Nat := 118140960795 + 34855 * 2 ^ 59
def prefixEnd_34855 : Nat := 4983230072969 + 3 ^ 40 * 34855 * 2
def baseEnd_34855 : Nat := 17897368212566363352211

theorem tailTrace_34855 : CollatzResearch.WordTrace tailWord_34855 prefixEnd_34855 17897368212566363352211 := by
  unfold tailWord_34855
  simp only [CollatzResearch.WordTrace]
  refine ⟨1271266288733762605186019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 847510859155841736790679 1271266288733762605186019)
  ·
    refine ⟨1906899433100643907779029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1271266288733762605186019 1906899433100643907779029)
    ·
      refine ⟨44692955463296341588571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 1906899433100643907779029 44692955463296341588571)
      ·
        refine ⟨67039433194944512382857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44692955463296341588571 67039433194944512382857)
        ·
          refine ⟨50279574896208384287143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67039433194944512382857 50279574896208384287143)
          ·
            refine ⟨75419362344312576430715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50279574896208384287143 75419362344312576430715)
            ·
              refine ⟨113129043516468864646073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75419362344312576430715 113129043516468864646073)
              ·
                refine ⟨84846782637351648484555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113129043516468864646073 84846782637351648484555)
                ·
                  refine ⟨127270173956027472726833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 84846782637351648484555 127270173956027472726833)
                  ·
                    refine ⟨95452630467020604545125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 127270173956027472726833 95452630467020604545125)
                    ·
                      refine ⟨17897368212566363352211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 95452630467020604545125 17897368212566363352211)
                      ·
                        rfl

theorem cell23_34855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_34855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_34855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_34855 prefixEnd_34855 := by exact prefixLift 34855
  have htrace : WordTrace (prefixWord ++ tailWord_34855) baseStart_34855 baseEnd_34855 := by
    simpa [prefixWord, tailWord_34855, baseEnd_34855] using wordTrace_append hprefix tailTrace_34855
  have hstable : (prefixWord ++ tailWord_34855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34855).length < 2 ^ (prefixWord ++ tailWord_34855).sum := by decide
  have hdescent : baseEnd_34855 < baseStart_34855 := by decide
  rcases family_descends (prefixWord ++ tailWord_34855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34858 : List Nat := [3, 1, 4, 1, 2, 1, 1, 1, 3, 3, 3]
def baseStart_34858 : Nat := 118140960795 + 34858 * 2 ^ 59
def prefixEnd_34858 : Nat := 4983230072969 + 3 ^ 40 * 34858 * 2
def baseEnd_34858 : Nat := 17898908654529851614697

theorem tailTrace_34858 : CollatzResearch.WordTrace tailWord_34858 prefixEnd_34858 17898908654529851614697 := by
  unfold tailWord_34858
  simp only [CollatzResearch.WordTrace]
  refine ⟨317843926930723529386307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 847583805148596078363485 317843926930723529386307)
  ·
    refine ⟨476765890396085294079461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 317843926930723529386307 476765890396085294079461)
    ·
      refine ⟨89393604449265992639899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 476765890396085294079461 89393604449265992639899)
      ·
        refine ⟨134090406673898988959849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89393604449265992639899 134090406673898988959849)
        ·
          refine ⟨100567805005424241719887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134090406673898988959849 100567805005424241719887)
          ·
            refine ⟨150851707508136362579831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100567805005424241719887 150851707508136362579831)
            ·
              refine ⟨226277561262204543869747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150851707508136362579831 226277561262204543869747)
              ·
                refine ⟨339416341893306815804621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 226277561262204543869747 339416341893306815804621)
                ·
                  refine ⟨127281128209990055926733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 339416341893306815804621 127281128209990055926733)
                  ·
                    refine ⟨47730423078746270972525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 127281128209990055926733 47730423078746270972525)
                    ·
                      refine ⟨17898908654529851614697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 47730423078746270972525 17898908654529851614697)
                      ·
                        rfl

theorem cell23_34858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_34858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_34858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_34858 prefixEnd_34858 := by exact prefixLift 34858
  have htrace : WordTrace (prefixWord ++ tailWord_34858) baseStart_34858 baseEnd_34858 := by
    simpa [prefixWord, tailWord_34858, baseEnd_34858] using wordTrace_append hprefix tailTrace_34858
  have hstable : (prefixWord ++ tailWord_34858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34858).length < 2 ^ (prefixWord ++ tailWord_34858).sum := by decide
  have hdescent : baseEnd_34858 < baseStart_34858 := by decide
  rcases family_descends (prefixWord ++ tailWord_34858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34862 : List Nat := [4, 1, 3, 1, 1, 3, 3, 1, 1, 2, 3]
def baseStart_34862 : Nat := 118140960795 + 34862 * 2 ^ 59
def prefixEnd_34862 : Nat := 4983230072969 + 3 ^ 40 * 34862 * 2
def baseEnd_34862 : Nat := 17900962577147835964679

theorem tailTrace_34862 : CollatzResearch.WordTrace tailWord_34862 prefixEnd_34862 17900962577147835964679 := by
  unfold tailWord_34862
  simp only [CollatzResearch.WordTrace]
  refine ⟨158940199963550350086355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 847681066472268533793893 158940199963550350086355)
  ·
    refine ⟨238410299945325525129533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158940199963550350086355 238410299945325525129533)
    ·
      refine ⟨89403862479497071923575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 238410299945325525129533 89403862479497071923575)
      ·
        refine ⟨134105793719245607885363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89403862479497071923575 134105793719245607885363)
        ·
          refine ⟨201158690578868411828045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134105793719245607885363 201158690578868411828045)
          ·
            refine ⟨75434508967075654435517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 201158690578868411828045 75434508967075654435517)
            ·
              refine ⟨28287940862653370413319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75434508967075654435517 28287940862653370413319)
              ·
                refine ⟨42431911293980055619979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28287940862653370413319 42431911293980055619979)
                ·
                  refine ⟨63647866940970083429969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42431911293980055619979 63647866940970083429969)
                  ·
                    refine ⟨47735900205727562572477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 63647866940970083429969 47735900205727562572477)
                    ·
                      refine ⟨17900962577147835964679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 47735900205727562572477 17900962577147835964679)
                      ·
                        rfl

theorem cell23_34862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 3, 1, 1, 2, 3].length) (baseStart_34862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_34862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_34862 prefixEnd_34862 := by exact prefixLift 34862
  have htrace : WordTrace (prefixWord ++ tailWord_34862) baseStart_34862 baseEnd_34862 := by
    simpa [prefixWord, tailWord_34862, baseEnd_34862] using wordTrace_append hprefix tailTrace_34862
  have hstable : (prefixWord ++ tailWord_34862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34862).length < 2 ^ (prefixWord ++ tailWord_34862).sum := by decide
  have hdescent : baseEnd_34862 < baseStart_34862 := by decide
  rcases family_descends (prefixWord ++ tailWord_34862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34948 : List Nat := [2, 3, 2, 1, 2, 1, 1, 3, 2, 3, 3]
def baseStart_34948 : Nat := 118140960795 + 34948 * 2 ^ 59
def prefixEnd_34948 : Nat := 4983230072969 + 3 ^ 40 * 34948 * 2
def baseEnd_34948 : Nat := 17945121913434499489283

theorem tailTrace_34948 : CollatzResearch.WordTrace tailWord_34948 prefixEnd_34948 17945121913434499489283 := by
  unfold tailWord_34948
  simp only [CollatzResearch.WordTrace]
  refine ⟨637329138698419744160749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 849772184931226325547665 637329138698419744160749)
  ·
    refine ⟨238998427011907404060281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 637329138698419744160749 238998427011907404060281)
    ·
      refine ⟨179248820258930553045211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 238998427011907404060281 179248820258930553045211)
      ·
        refine ⟨268873230388395829567817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179248820258930553045211 268873230388395829567817)
        ·
          refine ⟨201654922791296872175863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 268873230388395829567817 201654922791296872175863)
          ·
            refine ⟨302482384186945308263795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201654922791296872175863 302482384186945308263795)
            ·
              refine ⟨453723576280417962395693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 302482384186945308263795 453723576280417962395693)
              ·
                refine ⟨170146341105156735898385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 453723576280417962395693 170146341105156735898385)
                ·
                  refine ⟨127609755828867551923789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 170146341105156735898385 127609755828867551923789)
                  ·
                    refine ⟨47853658435825331971421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 127609755828867551923789 47853658435825331971421)
                    ·
                      refine ⟨17945121913434499489283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 47853658435825331971421 17945121913434499489283)
                      ·
                        rfl

theorem cell23_34948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 3, 2, 3, 3].length) (baseStart_34948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_34948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_34948 prefixEnd_34948 := by exact prefixLift 34948
  have htrace : WordTrace (prefixWord ++ tailWord_34948) baseStart_34948 baseEnd_34948 := by
    simpa [prefixWord, tailWord_34948, baseEnd_34948] using wordTrace_append hprefix tailTrace_34948
  have hstable : (prefixWord ++ tailWord_34948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34948).length < 2 ^ (prefixWord ++ tailWord_34948).sum := by decide
  have hdescent : baseEnd_34948 < baseStart_34948 := by decide
  rcases family_descends (prefixWord ++ tailWord_34948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34949 : List Nat := [1, 3, 1, 1, 5, 2, 3, 1, 2, 2, 2]
def baseStart_34949 : Nat := 118140960795 + 34949 * 2 ^ 59
def prefixEnd_34949 : Nat := 4983230072969 + 3 ^ 40 * 34949 * 2
def baseEnd_34949 : Nat := 17945635394088995576779

theorem tailTrace_34949 : CollatzResearch.WordTrace tailWord_34949 prefixEnd_34949 17945635394088995576779 := by
  unfold tailWord_34949
  simp only [CollatzResearch.WordTrace]
  refine ⟨1274694750393216659107901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 849796500262144439405267 1274694750393216659107901)
  ·
    refine ⟨478010531397456247165463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1274694750393216659107901 478010531397456247165463)
    ·
      refine ⟨717015797096184370748195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 478010531397456247165463 717015797096184370748195)
      ·
        refine ⟨1075523695644276556122293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 717015797096184370748195 1075523695644276556122293)
        ·
          refine ⟨100830346466650927136465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1075523695644276556122293 100830346466650927136465)
          ·
            refine ⟨75622759849988195352349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100830346466650927136465 75622759849988195352349)
            ·
              refine ⟨28358534943745573257131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75622759849988195352349 28358534943745573257131)
              ·
                refine ⟨42537802415618359885697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28358534943745573257131 42537802415618359885697)
                ·
                  refine ⟨31903351811713769914273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42537802415618359885697 31903351811713769914273)
                  ·
                    refine ⟨23927513858785327435705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31903351811713769914273 23927513858785327435705)
                    ·
                      refine ⟨17945635394088995576779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 23927513858785327435705 17945635394088995576779)
                      ·
                        rfl

theorem cell23_34949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 3, 1, 2, 2, 2].length) (baseStart_34949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_34949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_34949 prefixEnd_34949 := by exact prefixLift 34949
  have htrace : WordTrace (prefixWord ++ tailWord_34949) baseStart_34949 baseEnd_34949 := by
    simpa [prefixWord, tailWord_34949, baseEnd_34949] using wordTrace_append hprefix tailTrace_34949
  have hstable : (prefixWord ++ tailWord_34949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34949).length < 2 ^ (prefixWord ++ tailWord_34949).sum := by decide
  have hdescent : baseEnd_34949 < baseStart_34949 := by decide
  rcases family_descends (prefixWord ++ tailWord_34949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34951 : List Nat := [1, 1, 4, 2, 1, 1, 3, 2, 1, 7]
def baseStart_34951 : Nat := 118140960795 + 34951 * 2 ^ 59
def prefixEnd_34951 : Nat := 4983230072969 + 3 ^ 40 * 34951 * 2
def baseEnd_34951 : Nat := 5982220785132662583923

theorem tailTrace_34951 : CollatzResearch.WordTrace tailWord_34951 prefixEnd_34951 5982220785132662583923 := by
  unfold tailWord_34951
  simp only [CollatzResearch.WordTrace]
  refine ⟨1274767696385971000680707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 849845130923980667120471 1274767696385971000680707)
  ·
    refine ⟨1912151544578956501021061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1274767696385971000680707 1912151544578956501021061)
    ·
      refine ⟨358528414608554343941449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1912151544578956501021061 358528414608554343941449)
      ·
        refine ⟨268896310956415757956087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 358528414608554343941449 268896310956415757956087)
        ·
          refine ⟨403344466434623636934131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 268896310956415757956087 403344466434623636934131)
          ·
            refine ⟨605016699651935455401197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 403344466434623636934131 605016699651935455401197)
            ·
              refine ⟨226881262369475795775449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 605016699651935455401197 226881262369475795775449)
              ·
                refine ⟨170160946777106846831587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 226881262369475795775449 170160946777106846831587)
                ·
                  refine ⟨255241420165660270247381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 170160946777106846831587 255241420165660270247381)
                  ·
                    refine ⟨5982220785132662583923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 255241420165660270247381 5982220785132662583923)
                    ·
                      rfl

theorem cell23_34951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 2, 1, 7].length) (baseStart_34951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_34951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_34951 prefixEnd_34951 := by exact prefixLift 34951
  have htrace : WordTrace (prefixWord ++ tailWord_34951) baseStart_34951 baseEnd_34951 := by
    simpa [prefixWord, tailWord_34951, baseEnd_34951] using wordTrace_append hprefix tailTrace_34951
  have hstable : (prefixWord ++ tailWord_34951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34951).length < 2 ^ (prefixWord ++ tailWord_34951).sum := by decide
  have hdescent : baseEnd_34951 < baseStart_34951 := by decide
  rcases family_descends (prefixWord ++ tailWord_34951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_34971 : List Nat := [1, 1, 1, 1, 1, 1, 2, 7, 1, 3, 4]
def baseStart_34971 : Nat := 118140960795 + 34971 * 2 ^ 59
def prefixEnd_34971 : Nat := 4983230072969 + 3 ^ 40 * 34971 * 2
def baseEnd_34971 : Nat := 17956931968487909501677

theorem tailTrace_34971 : CollatzResearch.WordTrace tailWord_34971 prefixEnd_34971 17956931968487909501677 := by
  unfold tailWord_34971
  simp only [CollatzResearch.WordTrace]
  refine ⟨1275497156313514416408767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 850331437542342944272511 1275497156313514416408767)
  ·
    refine ⟨1913245734470271624613151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1275497156313514416408767 1913245734470271624613151)
    ·
      refine ⟨2869868601705407436919727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1913245734470271624613151 2869868601705407436919727)
      ·
        refine ⟨4304802902558111155379591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2869868601705407436919727 4304802902558111155379591)
        ·
          refine ⟨6457204353837166733069387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4304802902558111155379591 6457204353837166733069387)
          ·
            refine ⟨9685806530755750099604081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6457204353837166733069387 9685806530755750099604081)
            ·
              refine ⟨7264354898066812574703061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9685806530755750099604081 7264354898066812574703061)
              ·
                refine ⟨170258317923440919719603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 7264354898066812574703061 170258317923440919719603)
                ·
                  refine ⟨255387476885161379579405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 170258317923440919719603 255387476885161379579405)
                  ·
                    refine ⟨95770303831935517342277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 255387476885161379579405 95770303831935517342277)
                    ·
                      refine ⟨17956931968487909501677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 95770303831935517342277 17956931968487909501677)
                      ·
                        rfl

theorem cell23_34971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 7, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 7, 1, 3, 4].length) (baseStart_34971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_34971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_34971 prefixEnd_34971 := by exact prefixLift 34971
  have htrace : WordTrace (prefixWord ++ tailWord_34971) baseStart_34971 baseEnd_34971 := by
    simpa [prefixWord, tailWord_34971, baseEnd_34971] using wordTrace_append hprefix tailTrace_34971
  have hstable : (prefixWord ++ tailWord_34971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_34971).length < 2 ^ (prefixWord ++ tailWord_34971).sum := by decide
  have hdescent : baseEnd_34971 < baseStart_34971 := by decide
  rcases family_descends (prefixWord ++ tailWord_34971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35031 : List Nat := [1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 8]
def baseStart_35031 : Nat := 118140960795 + 35031 * 2 ^ 59
def prefixEnd_35031 : Nat := 4983230072969 + 3 ^ 40 * 35031 * 2
def baseEnd_35031 : Nat := 17987740807757674751401

theorem tailTrace_35031 : CollatzResearch.WordTrace tailWord_35031 prefixEnd_35031 17987740807757674751401 := by
  unfold tailWord_35031
  simp only [CollatzResearch.WordTrace]
  refine ⟨1277685536096144663592947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 851790357397429775728631 1277685536096144663592947)
  ·
    refine ⟨1916528304144216995389421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1277685536096144663592947 1916528304144216995389421)
    ·
      refine ⟨718698114054081373271033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1916528304144216995389421 718698114054081373271033)
      ·
        refine ⟨539023585540561029953275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 718698114054081373271033 539023585540561029953275)
        ·
          refine ⟨808535378310841544929913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 539023585540561029953275 808535378310841544929913)
          ·
            refine ⟨606401533733131158697435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 808535378310841544929913 606401533733131158697435)
            ·
              refine ⟨909602300599696738046153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 606401533733131158697435 909602300599696738046153)
              ·
                refine ⟨682201725449772553534615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 909602300599696738046153 682201725449772553534615)
                ·
                  refine ⟨1023302588174658830301923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 682201725449772553534615 1023302588174658830301923)
                  ·
                    refine ⟨1534953882261988245452885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1023302588174658830301923 1534953882261988245452885)
                    ·
                      refine ⟨17987740807757674751401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 1534953882261988245452885 17987740807757674751401)
                      ·
                        rfl

theorem cell23_35031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 8].length) (baseStart_35031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_35031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_35031 prefixEnd_35031 := by exact prefixLift 35031
  have htrace : WordTrace (prefixWord ++ tailWord_35031) baseStart_35031 baseEnd_35031 := by
    simpa [prefixWord, tailWord_35031, baseEnd_35031] using wordTrace_append hprefix tailTrace_35031
  have hstable : (prefixWord ++ tailWord_35031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35031).length < 2 ^ (prefixWord ++ tailWord_35031).sum := by decide
  have hdescent : baseEnd_35031 < baseStart_35031 := by decide
  rcases family_descends (prefixWord ++ tailWord_35031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35045 : List Nat := [1, 3, 1, 4, 2, 2, 2, 2, 6]
def baseStart_35045 : Nat := 118140960795 + 35045 * 2 ^ 59
def prefixEnd_35045 : Nat := 4983230072969 + 3 ^ 40 * 35045 * 2
def baseEnd_35045 : Nat := 1999436615213402219593

theorem tailTrace_35045 : CollatzResearch.WordTrace tailWord_35045 prefixEnd_35045 1999436615213402219593 := by
  unfold tailWord_35045
  simp only [CollatzResearch.WordTrace]
  refine ⟨1278196158045425054602589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 852130772030283369735059 1278196158045425054602589)
  ·
    refine ⟨479323559267034395475971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1278196158045425054602589 479323559267034395475971)
    ·
      refine ⟨718985338900551593213957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 479323559267034395475971 718985338900551593213957)
      ·
        refine ⟨134809751043853423727617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 718985338900551593213957 134809751043853423727617)
        ·
          refine ⟨101107313282890067795713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134809751043853423727617 101107313282890067795713)
          ·
            refine ⟨75830484962167550846785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101107313282890067795713 75830484962167550846785)
            ·
              refine ⟨56872863721625663135089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75830484962167550846785 56872863721625663135089)
              ·
                refine ⟨42654647791219247351317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56872863721625663135089 42654647791219247351317)
                ·
                  refine ⟨1999436615213402219593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 42654647791219247351317 1999436615213402219593)
                  ·
                    rfl

theorem cell23_35045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 2, 6].length) (baseStart_35045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_35045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_35045 prefixEnd_35045 := by exact prefixLift 35045
  have htrace : WordTrace (prefixWord ++ tailWord_35045) baseStart_35045 baseEnd_35045 := by
    simpa [prefixWord, tailWord_35045, baseEnd_35045] using wordTrace_append hprefix tailTrace_35045
  have hstable : (prefixWord ++ tailWord_35045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35045).length < 2 ^ (prefixWord ++ tailWord_35045).sum := by decide
  have hdescent : baseEnd_35045 < baseStart_35045 := by decide
  rcases family_descends (prefixWord ++ tailWord_35045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35082 : List Nat := [3, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2]
def baseStart_35082 : Nat := 118140960795 + 35082 * 2 ^ 59
def prefixEnd_35082 : Nat := 4983230072969 + 3 ^ 40 * 35082 * 2
def baseEnd_35082 : Nat := 18013928321136975213667

theorem tailTrace_35082 : CollatzResearch.WordTrace tailWord_35082 prefixEnd_35082 18013928321136975213667 := by
  unfold tailWord_35082
  simp only [CollatzResearch.WordTrace]
  refine ⟨319886414727845093424875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 853030439274253582466333 319886414727845093424875)
  ·
    refine ⟨479829622091767640137313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 319886414727845093424875 479829622091767640137313)
    ·
      refine ⟨359872216568825730102985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 479829622091767640137313 359872216568825730102985)
      ·
        refine ⟨269904162426619297577239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 359872216568825730102985 269904162426619297577239)
        ·
          refine ⟨404856243639928946365859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 269904162426619297577239 404856243639928946365859)
          ·
            refine ⟨607284365459893419548789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 404856243639928946365859 607284365459893419548789)
            ·
              refine ⟨56932909261865008082699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 607284365459893419548789 56932909261865008082699)
              ·
                refine ⟨85399363892797512124049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56932909261865008082699 85399363892797512124049)
                ·
                  refine ⟨64049522919598134093037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 85399363892797512124049 64049522919598134093037)
                  ·
                    refine ⟨24018571094849300284889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 64049522919598134093037 24018571094849300284889)
                    ·
                      refine ⟨18013928321136975213667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 24018571094849300284889 18013928321136975213667)
                      ·
                        rfl

theorem cell23_35082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2].length) (baseStart_35082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_35082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_35082 prefixEnd_35082 := by exact prefixLift 35082
  have htrace : WordTrace (prefixWord ++ tailWord_35082) baseStart_35082 baseEnd_35082 := by
    simpa [prefixWord, tailWord_35082, baseEnd_35082] using wordTrace_append hprefix tailTrace_35082
  have hstable : (prefixWord ++ tailWord_35082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35082).length < 2 ^ (prefixWord ++ tailWord_35082).sum := by decide
  have hdescent : baseEnd_35082 < baseStart_35082 := by decide
  rcases family_descends (prefixWord ++ tailWord_35082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35089 : List Nat := [1, 2, 2, 1, 1, 6, 2, 3, 1, 1, 3]
def baseStart_35089 : Nat := 118140960795 + 35089 * 2 ^ 59
def prefixEnd_35089 : Nat := 4983230072969 + 3 ^ 40 * 35089 * 2
def baseEnd_35089 : Nat := 18017522685718447826135

theorem tailTrace_35089 : CollatzResearch.WordTrace tailWord_35089 prefixEnd_35089 18017522685718447826135 := by
  unfold tailWord_35089
  simp only [CollatzResearch.WordTrace]
  refine ⟨1279800969886020569204321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 853200646590680379469547 1279800969886020569204321)
  ·
    refine ⟨959850727414515426903241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1279800969886020569204321 959850727414515426903241)
    ·
      refine ⟨719888045560886570177431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 959850727414515426903241 719888045560886570177431)
      ·
        refine ⟨1079832068341329855266147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 719888045560886570177431 1079832068341329855266147)
        ·
          refine ⟨1619748102511994782899221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1079832068341329855266147 1619748102511994782899221)
          ·
            refine ⟨75925692305249755448401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1619748102511994782899221 75925692305249755448401)
            ·
              refine ⟨56944269228937316586301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75925692305249755448401 56944269228937316586301)
              ·
                refine ⟨21354100960851493719863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56944269228937316586301 21354100960851493719863)
                ·
                  refine ⟨32031151441277240579795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21354100960851493719863 32031151441277240579795)
                  ·
                    refine ⟨48046727161915860869693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32031151441277240579795 48046727161915860869693)
                    ·
                      refine ⟨18017522685718447826135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 48046727161915860869693 18017522685718447826135)
                      ·
                        rfl

theorem cell23_35089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 3, 1, 1, 3].length) (baseStart_35089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_35089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_35089 prefixEnd_35089 := by exact prefixLift 35089
  have htrace : WordTrace (prefixWord ++ tailWord_35089) baseStart_35089 baseEnd_35089 := by
    simpa [prefixWord, tailWord_35089, baseEnd_35089] using wordTrace_append hprefix tailTrace_35089
  have hstable : (prefixWord ++ tailWord_35089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35089).length < 2 ^ (prefixWord ++ tailWord_35089).sum := by decide
  have hdescent : baseEnd_35089 < baseStart_35089 := by decide
  rcases family_descends (prefixWord ++ tailWord_35089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35122 : List Nat := [3, 2, 1, 1, 5, 2, 1, 1, 1, 6]
def baseStart_35122 : Nat := 118140960795 + 35122 * 2 ^ 59
def prefixEnd_35122 : Nat := 4983230072969 + 3 ^ 40 * 35122 * 2
def baseEnd_35122 : Nat := 6011489182438939571161

theorem tailTrace_35122 : CollatzResearch.WordTrace tailWord_35122 prefixEnd_35122 6011489182438939571161 := by
  unfold tailWord_35122
  simp only [CollatzResearch.WordTrace]
  refine ⟨320251144691616801288905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 854003052510978136770413 320251144691616801288905)
  ·
    refine ⟨240188358518712600966679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 320251144691616801288905 240188358518712600966679)
    ·
      refine ⟨360282537778068901450019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240188358518712600966679 360282537778068901450019)
      ·
        refine ⟨540423806667103352175029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 360282537778068901450019 540423806667103352175029)
        ·
          refine ⟨50664731875040939266409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 540423806667103352175029 50664731875040939266409)
          ·
            refine ⟨37998548906280704449807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50664731875040939266409 37998548906280704449807)
            ·
              refine ⟨56997823359421056674711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37998548906280704449807 56997823359421056674711)
              ·
                refine ⟨85496735039131585012067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56997823359421056674711 85496735039131585012067)
                ·
                  refine ⟨128245102558697377518101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 85496735039131585012067 128245102558697377518101)
                  ·
                    refine ⟨6011489182438939571161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 128245102558697377518101 6011489182438939571161)
                    ·
                      rfl

theorem cell23_35122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 1, 1, 1, 6].length) (baseStart_35122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_35122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_35122 prefixEnd_35122 := by exact prefixLift 35122
  have htrace : WordTrace (prefixWord ++ tailWord_35122) baseStart_35122 baseEnd_35122 := by
    simpa [prefixWord, tailWord_35122, baseEnd_35122] using wordTrace_append hprefix tailTrace_35122
  have hstable : (prefixWord ++ tailWord_35122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35122).length < 2 ^ (prefixWord ++ tailWord_35122).sum := by decide
  have hdescent : baseEnd_35122 < baseStart_35122 := by decide
  rcases family_descends (prefixWord ++ tailWord_35122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35129 : List Nat := [1, 2, 1, 6, 1, 1, 2, 2, 3, 2, 2]
def baseStart_35129 : Nat := 118140960795 + 35129 * 2 ^ 59
def prefixEnd_35129 : Nat := 4983230072969 + 3 ^ 40 * 35129 * 2
def baseEnd_35129 : Nat := 18038061911898291325951

theorem tailTrace_35129 : CollatzResearch.WordTrace tailWord_35129 prefixEnd_35129 18038061911898291325951 := by
  unfold tailWord_35129
  simp only [CollatzResearch.WordTrace]
  refine ⟨1281259889741107400660441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 854173259827404933773627 1281259889741107400660441)
  ·
    refine ⟨960944917305830550495331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1281259889741107400660441 960944917305830550495331)
    ·
      refine ⟨1441417375958745825742997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 960944917305830550495331 1441417375958745825742997)
      ·
        refine ⟨67566439498066210581703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 1441417375958745825742997 67566439498066210581703)
        ·
          refine ⟨101349659247099315872555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67566439498066210581703 101349659247099315872555)
          ·
            refine ⟨152024488870648973808833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101349659247099315872555 152024488870648973808833)
            ·
              refine ⟨114018366652986730356625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 152024488870648973808833 114018366652986730356625)
              ·
                refine ⟨85513774989740047767469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 114018366652986730356625 85513774989740047767469)
                ·
                  refine ⟨32067665621152517912801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 85513774989740047767469 32067665621152517912801)
                  ·
                    refine ⟨24050749215864388434601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32067665621152517912801 24050749215864388434601)
                    ·
                      refine ⟨18038061911898291325951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 24050749215864388434601 18038061911898291325951)
                      ·
                        rfl

theorem cell23_35129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_35129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_35129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_35129 prefixEnd_35129 := by exact prefixLift 35129
  have htrace : WordTrace (prefixWord ++ tailWord_35129) baseStart_35129 baseEnd_35129 := by
    simpa [prefixWord, tailWord_35129, baseEnd_35129] using wordTrace_append hprefix tailTrace_35129
  have hstable : (prefixWord ++ tailWord_35129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35129).length < 2 ^ (prefixWord ++ tailWord_35129).sum := by decide
  have hdescent : baseEnd_35129 < baseStart_35129 := by decide
  rcases family_descends (prefixWord ++ tailWord_35129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35132 : List Nat := [2, 2, 2, 2, 1, 2, 4, 2, 1, 2, 3]
def baseStart_35132 : Nat := 118140960795 + 35132 * 2 ^ 59
def prefixEnd_35132 : Nat := 4983230072969 + 3 ^ 40 * 35132 * 2
def baseEnd_35132 : Nat := 18039602353861779588437

theorem tailTrace_35132 : CollatzResearch.WordTrace tailWord_35132 prefixEnd_35132 18039602353861779588437 := by
  unfold tailWord_35132
  simp only [CollatzResearch.WordTrace]
  refine ⟨640684654365119456509825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 854246205820159275346433 640684654365119456509825)
  ·
    refine ⟨480513490773839592382369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 640684654365119456509825 480513490773839592382369)
    ·
      refine ⟨360385118080379694286777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 480513490773839592382369 360385118080379694286777)
      ·
        refine ⟨270288838560284770715083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 360385118080379694286777 270288838560284770715083)
        ·
          refine ⟨405433257840427156072625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 270288838560284770715083 405433257840427156072625)
          ·
            refine ⟨304074943380320367054469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 405433257840427156072625 304074943380320367054469)
            ·
              refine ⟨57014051883810068822713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 304074943380320367054469 57014051883810068822713)
              ·
                refine ⟨42760538912857551617035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57014051883810068822713 42760538912857551617035)
                ·
                  refine ⟨64140808369286327425553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42760538912857551617035 64140808369286327425553)
                  ·
                    refine ⟨48105606276964745569165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 64140808369286327425553 48105606276964745569165)
                    ·
                      refine ⟨18039602353861779588437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 48105606276964745569165 18039602353861779588437)
                      ·
                        rfl

theorem cell23_35132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 2, 1, 2, 3].length) (baseStart_35132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_35132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_35132 prefixEnd_35132 := by exact prefixLift 35132
  have htrace : WordTrace (prefixWord ++ tailWord_35132) baseStart_35132 baseEnd_35132 := by
    simpa [prefixWord, tailWord_35132, baseEnd_35132] using wordTrace_append hprefix tailTrace_35132
  have hstable : (prefixWord ++ tailWord_35132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35132).length < 2 ^ (prefixWord ++ tailWord_35132).sum := by decide
  have hdescent : baseEnd_35132 < baseStart_35132 := by decide
  rcases family_descends (prefixWord ++ tailWord_35132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35140 : List Nat := [2, 3, 4, 1, 3, 1, 1, 3, 1, 1, 3]
def baseStart_35140 : Nat := 118140960795 + 35140 * 2 ^ 59
def prefixEnd_35140 : Nat := 4983230072969 + 3 ^ 40 * 35140 * 2
def baseEnd_35140 : Nat := 18043710199097748288401

theorem tailTrace_35140 : CollatzResearch.WordTrace tailWord_35140 prefixEnd_35140 18043710199097748288401 := by
  unfold tailWord_35140
  simp only [CollatzResearch.WordTrace]
  refine ⟨640830546350628139655437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 854440728467504186207249 640830546350628139655437)
  ·
    refine ⟨240311454881485552370789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 640830546350628139655437 240311454881485552370789)
    ·
      refine ⟨45058397790278541069523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 240311454881485552370789 45058397790278541069523)
      ·
        refine ⟨67587596685417811604285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45058397790278541069523 67587596685417811604285)
        ·
          refine ⟨25345348757031679351607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67587596685417811604285 25345348757031679351607)
          ·
            refine ⟨38018023135547519027411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25345348757031679351607 38018023135547519027411)
            ·
              refine ⟨57027034703321278541117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38018023135547519027411 57027034703321278541117)
              ·
                refine ⟨21385138013745479452919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57027034703321278541117 21385138013745479452919)
                ·
                  refine ⟨32077707020618219179379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21385138013745479452919 32077707020618219179379)
                  ·
                    refine ⟨48116560530927328769069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32077707020618219179379 48116560530927328769069)
                    ·
                      refine ⟨18043710199097748288401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 48116560530927328769069 18043710199097748288401)
                      ·
                        rfl

theorem cell23_35140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_35140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_35140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_35140 prefixEnd_35140 := by exact prefixLift 35140
  have htrace : WordTrace (prefixWord ++ tailWord_35140) baseStart_35140 baseEnd_35140 := by
    simpa [prefixWord, tailWord_35140, baseEnd_35140] using wordTrace_append hprefix tailTrace_35140
  have hstable : (prefixWord ++ tailWord_35140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35140).length < 2 ^ (prefixWord ++ tailWord_35140).sum := by decide
  have hdescent : baseEnd_35140 < baseStart_35140 := by decide
  rcases family_descends (prefixWord ++ tailWord_35140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35162 : List Nat := [3, 1, 1, 2, 1, 2, 1, 6, 2, 1, 3]
def baseStart_35162 : Nat := 118140960795 + 35162 * 2 ^ 59
def prefixEnd_35162 : Nat := 4983230072969 + 3 ^ 40 * 35162 * 2
def baseEnd_35162 : Nat := 18055006773496662213299

theorem tailTrace_35162 : CollatzResearch.WordTrace tailWord_35162 prefixEnd_35162 18055006773496662213299 := by
  unfold tailWord_35162
  simp only [CollatzResearch.WordTrace]
  refine ⟨320615874655388509152935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 854975665747702691074493 320615874655388509152935)
  ·
    refine ⟨480923811983082763729403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 320615874655388509152935 480923811983082763729403)
    ·
      refine ⟨721385717974624145594105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 480923811983082763729403 721385717974624145594105)
      ·
        refine ⟨541039288480968109195579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 721385717974624145594105 541039288480968109195579)
        ·
          refine ⟨811558932721452163793369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 541039288480968109195579 811558932721452163793369)
          ·
            refine ⟨608669199541089122845027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 811558932721452163793369 608669199541089122845027)
            ·
              refine ⟨913003799311633684267541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 608669199541089122845027 913003799311633684267541)
              ·
                refine ⟨42797053092732828950041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 913003799311633684267541 42797053092732828950041)
                ·
                  refine ⟨32097789819549621712531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42797053092732828950041 32097789819549621712531)
                  ·
                    refine ⟨48146684729324432568797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32097789819549621712531 48146684729324432568797)
                    ·
                      refine ⟨18055006773496662213299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 48146684729324432568797 18055006773496662213299)
                      ·
                        rfl

theorem cell23_35162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 6, 2, 1, 3].length) (baseStart_35162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_35162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_35162 prefixEnd_35162 := by exact prefixLift 35162
  have htrace : WordTrace (prefixWord ++ tailWord_35162) baseStart_35162 baseEnd_35162 := by
    simpa [prefixWord, tailWord_35162, baseEnd_35162] using wordTrace_append hprefix tailTrace_35162
  have hstable : (prefixWord ++ tailWord_35162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35162).length < 2 ^ (prefixWord ++ tailWord_35162).sum := by decide
  have hdescent : baseEnd_35162 < baseStart_35162 := by decide
  rcases family_descends (prefixWord ++ tailWord_35162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35172 : List Nat := [2, 3, 1, 1, 3, 1, 2, 2, 3, 3, 2]
def baseStart_35172 : Nat := 118140960795 + 35172 * 2 ^ 59
def prefixEnd_35172 : Nat := 4983230072969 + 3 ^ 40 * 35172 * 2
def baseEnd_35172 : Nat := 18060141580041623088253

theorem tailTrace_35172 : CollatzResearch.WordTrace tailWord_35172 prefixEnd_35172 18060141580041623088253 := by
  unfold tailWord_35172
  simp only [CollatzResearch.WordTrace]
  refine ⟨641414114292662872237885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 855218819056883829650513 641414114292662872237885)
  ·
    refine ⟨240530292859748577089207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 641414114292662872237885 240530292859748577089207)
    ·
      refine ⟨360795439289622865633811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240530292859748577089207 360795439289622865633811)
      ·
        refine ⟨541193158934434298450717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 360795439289622865633811 541193158934434298450717)
        ·
          refine ⟨202947434600412861919019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 541193158934434298450717 202947434600412861919019)
          ·
            refine ⟨304421151900619292878529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 202947434600412861919019 304421151900619292878529)
            ·
              refine ⟨228315863925464469658897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 304421151900619292878529 228315863925464469658897)
              ·
                refine ⟨171236897944098352244173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 228315863925464469658897 171236897944098352244173)
                ·
                  refine ⟨64213836729036882091565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 171236897944098352244173 64213836729036882091565)
                  ·
                    refine ⟨24080188773388830784337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 64213836729036882091565 24080188773388830784337)
                    ·
                      refine ⟨18060141580041623088253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 24080188773388830784337 18060141580041623088253)
                      ·
                        rfl

theorem cell23_35172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 2, 3, 3, 2].length) (baseStart_35172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_35172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_35172 prefixEnd_35172 := by exact prefixLift 35172
  have htrace : WordTrace (prefixWord ++ tailWord_35172) baseStart_35172 baseEnd_35172 := by
    simpa [prefixWord, tailWord_35172, baseEnd_35172] using wordTrace_append hprefix tailTrace_35172
  have hstable : (prefixWord ++ tailWord_35172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35172).length < 2 ^ (prefixWord ++ tailWord_35172).sum := by decide
  have hdescent : baseEnd_35172 < baseStart_35172 := by decide
  rcases family_descends (prefixWord ++ tailWord_35172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35189 : List Nat := [1, 3, 4, 1, 2, 2, 1, 1, 3, 3, 2]
def baseStart_35189 : Nat := 118140960795 + 35189 * 2 ^ 59
def prefixEnd_35189 : Nat := 4983230072969 + 3 ^ 40 * 35189 * 2
def baseEnd_35189 : Nat := 18068870751168056575675

theorem tailTrace_35189 : CollatzResearch.WordTrace tailWord_35189 prefixEnd_35189 18068870751168056575675 := by
  unfold tailWord_35189
  simp only [CollatzResearch.WordTrace]
  refine ⟨1283448269523737647844621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 855632179682491765229747 1283448269523737647844621)
  ·
    refine ⟨481293101071401617941733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1283448269523737647844621 481293101071401617941733)
    ·
      refine ⟨90242456450887803364075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 481293101071401617941733 90242456450887803364075)
      ·
        refine ⟨135363684676331705046113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90242456450887803364075 135363684676331705046113)
        ·
          refine ⟨101522763507248778784585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135363684676331705046113 101522763507248778784585)
          ·
            refine ⟨76142072630436584088439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101522763507248778784585 76142072630436584088439)
            ·
              refine ⟨114213108945654876132659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76142072630436584088439 114213108945654876132659)
              ·
                refine ⟨171319663418482314198989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114213108945654876132659 171319663418482314198989)
                ·
                  refine ⟨64244873781930867824621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 171319663418482314198989 64244873781930867824621)
                  ·
                    refine ⟨24091827668224075434233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 64244873781930867824621 24091827668224075434233)
                    ·
                      refine ⟨18068870751168056575675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 24091827668224075434233 18068870751168056575675)
                      ·
                        rfl

theorem cell23_35189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 1, 3, 3, 2].length) (baseStart_35189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_35189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_35189 prefixEnd_35189 := by exact prefixLift 35189
  have htrace : WordTrace (prefixWord ++ tailWord_35189) baseStart_35189 baseEnd_35189 := by
    simpa [prefixWord, tailWord_35189, baseEnd_35189] using wordTrace_append hprefix tailTrace_35189
  have hstable : (prefixWord ++ tailWord_35189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35189).length < 2 ^ (prefixWord ++ tailWord_35189).sum := by decide
  have hdescent : baseEnd_35189 < baseStart_35189 := by decide
  rcases family_descends (prefixWord ++ tailWord_35189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35235 : List Nat := [1, 1, 1, 4, 1, 4, 1, 1, 1, 5, 3]
def baseStart_35235 : Nat := 118140960795 + 35235 * 2 ^ 59
def prefixEnd_35235 : Nat := 4983230072969 + 3 ^ 40 * 35235 * 2
def baseEnd_35235 : Nat := 18092490861274876600463

theorem tailTrace_35235 : CollatzResearch.WordTrace tailWord_35235 prefixEnd_35235 18092490861274876600463 := by
  unfold tailWord_35235
  simp only [CollatzResearch.WordTrace]
  refine ⟨1285126027357087504019159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 856750684904725002679439 1285126027357087504019159)
  ·
    refine ⟨1927689041035631256028739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1285126027357087504019159 1927689041035631256028739)
    ·
      refine ⟨2891533561553446884043109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1927689041035631256028739 2891533561553446884043109)
      ·
        refine ⟨542162542791271290758083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2891533561553446884043109 542162542791271290758083)
        ·
          refine ⟨813243814186906936137125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 542162542791271290758083 813243814186906936137125)
          ·
            refine ⟨152483215160045050525711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 813243814186906936137125 152483215160045050525711)
            ·
              refine ⟨228724822740067575788567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 152483215160045050525711 228724822740067575788567)
              ·
                refine ⟨343087234110101363682851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 228724822740067575788567 343087234110101363682851)
                ·
                  refine ⟨514630851165152045524277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 343087234110101363682851 514630851165152045524277)
                  ·
                    refine ⟨48246642296733004267901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 514630851165152045524277 48246642296733004267901)
                    ·
                      refine ⟨18092490861274876600463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 48246642296733004267901 18092490861274876600463)
                      ·
                        rfl

theorem cell23_35235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 5, 3].length) (baseStart_35235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_35235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_35235 prefixEnd_35235 := by exact prefixLift 35235
  have htrace : WordTrace (prefixWord ++ tailWord_35235) baseStart_35235 baseEnd_35235 := by
    simpa [prefixWord, tailWord_35235, baseEnd_35235] using wordTrace_append hprefix tailTrace_35235
  have hstable : (prefixWord ++ tailWord_35235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35235).length < 2 ^ (prefixWord ++ tailWord_35235).sum := by decide
  have hdescent : baseEnd_35235 < baseStart_35235 := by decide
  rcases family_descends (prefixWord ++ tailWord_35235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35255 : List Nat := [1, 1, 3, 1, 3, 4, 1, 1, 1, 7]
def baseStart_35255 : Nat := 118140960795 + 35255 * 2 ^ 59
def prefixEnd_35255 : Nat := 4983230072969 + 3 ^ 40 * 35255 * 2
def baseEnd_35255 : Nat := 6034253491454932783457

theorem tailTrace_35255 : CollatzResearch.WordTrace tailWord_35255 prefixEnd_35255 6034253491454932783457 := by
  unfold tailWord_35255
  simp only [CollatzResearch.WordTrace]
  refine ⟨1285855487284630919747219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 857236991523087279831479 1285855487284630919747219)
  ·
    refine ⟨1928783230926946379620829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1285855487284630919747219 1928783230926946379620829)
    ·
      refine ⟨723293711597604892357811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1928783230926946379620829 723293711597604892357811)
      ·
        refine ⟨1084940567396407338536717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 723293711597604892357811 1084940567396407338536717)
        ·
          refine ⟨406852712773652751951269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1084940567396407338536717 406852712773652751951269)
          ·
            refine ⟨76284883645059890990863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 406852712773652751951269 76284883645059890990863)
            ·
              refine ⟨114427325467589836486295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76284883645059890990863 114427325467589836486295)
              ·
                refine ⟨171640988201384754729443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114427325467589836486295 171640988201384754729443)
                ·
                  refine ⟨257461482302077132094165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 171640988201384754729443 257461482302077132094165)
                  ·
                    refine ⟨6034253491454932783457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 257461482302077132094165 6034253491454932783457)
                    ·
                      rfl

theorem cell23_35255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 1, 1, 7].length) (baseStart_35255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_35255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_35255 prefixEnd_35255 := by exact prefixLift 35255
  have htrace : WordTrace (prefixWord ++ tailWord_35255) baseStart_35255 baseEnd_35255 := by
    simpa [prefixWord, tailWord_35255, baseEnd_35255] using wordTrace_append hprefix tailTrace_35255
  have hstable : (prefixWord ++ tailWord_35255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35255).length < 2 ^ (prefixWord ++ tailWord_35255).sum := by decide
  have hdescent : baseEnd_35255 < baseStart_35255 := by decide
  rcases family_descends (prefixWord ++ tailWord_35255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35275 : List Nat := [1, 1, 1, 1, 3, 3, 1, 3, 4, 1, 4]
def baseStart_35275 : Nat := 118140960795 + 35275 * 2 ^ 59
def prefixEnd_35275 : Nat := 4983230072969 + 3 ^ 40 * 35275 * 2
def baseEnd_35275 : Nat := 18113030087454720100279

theorem tailTrace_35275 : CollatzResearch.WordTrace tailWord_35275 prefixEnd_35275 18113030087454720100279 := by
  unfold tailWord_35275
  simp only [CollatzResearch.WordTrace]
  refine ⟨1286584947212174335475279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 857723298141449556983519 1286584947212174335475279)
  ·
    refine ⟨1929877420818261503212919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1286584947212174335475279 1929877420818261503212919)
    ·
      refine ⟨2894816131227392254819379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1929877420818261503212919 2894816131227392254819379)
      ·
        refine ⟨4342224196841088382229069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2894816131227392254819379 4342224196841088382229069)
        ·
          refine ⟨1628334073815408143335901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4342224196841088382229069 1628334073815408143335901)
          ·
            refine ⟨610625277680778053750963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1628334073815408143335901 610625277680778053750963)
            ·
              refine ⟨915937916521167080626445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 610625277680778053750963 915937916521167080626445)
              ·
                refine ⟨343476718695437655234917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 915937916521167080626445 343476718695437655234917)
                ·
                  refine ⟨64401884755394560356547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 343476718695437655234917 64401884755394560356547)
                  ·
                    refine ⟨96602827133091840534821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 64401884755394560356547 96602827133091840534821)
                    ·
                      refine ⟨18113030087454720100279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 96602827133091840534821 18113030087454720100279)
                      ·
                        rfl

theorem cell23_35275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 4, 1, 4].length) (baseStart_35275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_35275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_35275 prefixEnd_35275 := by exact prefixLift 35275
  have htrace : WordTrace (prefixWord ++ tailWord_35275) baseStart_35275 baseEnd_35275 := by
    simpa [prefixWord, tailWord_35275, baseEnd_35275] using wordTrace_append hprefix tailTrace_35275
  have hstable : (prefixWord ++ tailWord_35275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35275).length < 2 ^ (prefixWord ++ tailWord_35275).sum := by decide
  have hdescent : baseEnd_35275 < baseStart_35275 := by decide
  rcases family_descends (prefixWord ++ tailWord_35275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35312 : List Nat := [2, 1, 1, 1, 3, 3, 2, 3, 2, 2, 3]
def baseStart_35312 : Nat := 118140960795 + 35312 * 2 ^ 59
def prefixEnd_35312 : Nat := 4983230072969 + 3 ^ 40 * 35312 * 2
def baseEnd_35312 : Nat := 18132028871671075337609

theorem tailTrace_35312 : CollatzResearch.WordTrace tailWord_35312 prefixEnd_35312 18132028871671075337609 := by
  unfold tailWord_35312
  simp only [CollatzResearch.WordTrace]
  refine ⟨643967224039064827286095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 858622965385419769714793 643967224039064827286095)
  ·
    refine ⟨965950836058597240929143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 643967224039064827286095 965950836058597240929143)
    ·
      refine ⟨1448926254087895861393715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 965950836058597240929143 1448926254087895861393715)
      ·
        refine ⟨2173389381131843792090573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1448926254087895861393715 2173389381131843792090573)
        ·
          refine ⟨815021017924441422033965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2173389381131843792090573 815021017924441422033965)
          ·
            refine ⟨305632881721665533262737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 815021017924441422033965 305632881721665533262737)
            ·
              refine ⟨229224661291249149947053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 305632881721665533262737 229224661291249149947053)
              ·
                refine ⟨85959247984218431230145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 229224661291249149947053 85959247984218431230145)
                ·
                  refine ⟨64469435988163823422609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 85959247984218431230145 64469435988163823422609)
                  ·
                    refine ⟨48352076991122867566957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 64469435988163823422609 48352076991122867566957)
                    ·
                      refine ⟨18132028871671075337609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 48352076991122867566957 18132028871671075337609)
                      ·
                        rfl

theorem cell23_35312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 3, 2, 2, 3].length) (baseStart_35312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_35312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_35312 prefixEnd_35312 := by exact prefixLift 35312
  have htrace : WordTrace (prefixWord ++ tailWord_35312) baseStart_35312 baseEnd_35312 := by
    simpa [prefixWord, tailWord_35312, baseEnd_35312] using wordTrace_append hprefix tailTrace_35312
  have hstable : (prefixWord ++ tailWord_35312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35312).length < 2 ^ (prefixWord ++ tailWord_35312).sum := by decide
  have hdescent : baseEnd_35312 < baseStart_35312 := by decide
  rcases family_descends (prefixWord ++ tailWord_35312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35329 : List Nat := [1, 2, 4, 1, 3, 2, 1, 2, 2, 2, 3]
def baseStart_35329 : Nat := 118140960795 + 35329 * 2 ^ 59
def prefixEnd_35329 : Nat := 4983230072969 + 3 ^ 40 * 35329 * 2
def baseEnd_35329 : Nat := 18140758042797508825031

theorem tailTrace_35329 : CollatzResearch.WordTrace tailWord_35329 prefixEnd_35329 18140758042797508825031 := by
  unfold tailWord_35329
  simp only [CollatzResearch.WordTrace]
  refine ⟨1288554489016541557941041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 859036326011027705294027 1288554489016541557941041)
  ·
    refine ⟨966415866762406168455781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1288554489016541557941041 966415866762406168455781)
    ·
      refine ⟨181202975017951156585459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 966415866762406168455781 181202975017951156585459)
      ·
        refine ⟨271804462526926734878189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181202975017951156585459 271804462526926734878189)
        ·
          refine ⟨101926673447597525579321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 271804462526926734878189 101926673447597525579321)
          ·
            refine ⟨76445005085698144184491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101926673447597525579321 76445005085698144184491)
            ·
              refine ⟨114667507628547216276737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76445005085698144184491 114667507628547216276737)
              ·
                refine ⟨86000630721410412207553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 114667507628547216276737 86000630721410412207553)
                ·
                  refine ⟨64500473041057809155665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 86000630721410412207553 64500473041057809155665)
                  ·
                    refine ⟨48375354780793356866749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 64500473041057809155665 48375354780793356866749)
                    ·
                      refine ⟨18140758042797508825031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 48375354780793356866749 18140758042797508825031)
                      ·
                        rfl

theorem cell23_35329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 2, 2, 2, 3].length) (baseStart_35329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_35329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_35329 prefixEnd_35329 := by exact prefixLift 35329
  have htrace : WordTrace (prefixWord ++ tailWord_35329) baseStart_35329 baseEnd_35329 := by
    simpa [prefixWord, tailWord_35329, baseEnd_35329] using wordTrace_append hprefix tailTrace_35329
  have hstable : (prefixWord ++ tailWord_35329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35329).length < 2 ^ (prefixWord ++ tailWord_35329).sum := by decide
  have hdescent : baseEnd_35329 < baseStart_35329 := by decide
  rcases family_descends (prefixWord ++ tailWord_35329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35332 : List Nat := [2, 3, 2, 3, 1, 1, 2, 1, 8]
def baseStart_35332 : Nat := 118140960795 + 35332 * 2 ^ 59
def prefixEnd_35332 : Nat := 4983230072969 + 3 ^ 40 * 35332 * 2
def baseEnd_35332 : Nat := 2015810942751221898613

theorem tailTrace_35332 : CollatzResearch.WordTrace tailWord_35332 prefixEnd_35332 2015810942751221898613 := by
  unfold tailWord_35332
  simp only [CollatzResearch.WordTrace]
  refine ⟨644331954002836535150125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 859109272003782046866833 644331954002836535150125)
  ·
    refine ⟨241624482751063700681297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 644331954002836535150125 241624482751063700681297)
    ·
      refine ⟨181218362063297775510973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 241624482751063700681297 181218362063297775510973)
      ·
        refine ⟨67956885773736665816615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 181218362063297775510973 67956885773736665816615)
        ·
          refine ⟨101935328660604998724923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67956885773736665816615 101935328660604998724923)
          ·
            refine ⟨152902992990907498087385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101935328660604998724923 152902992990907498087385)
            ·
              refine ⟨114677244743180623565539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 152902992990907498087385 114677244743180623565539)
              ·
                refine ⟨172015867114770935348309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114677244743180623565539 172015867114770935348309)
                ·
                  refine ⟨2015810942751221898613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 172015867114770935348309 2015810942751221898613)
                  ·
                    rfl

theorem cell23_35332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 1, 8].length) (baseStart_35332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_35332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_35332 prefixEnd_35332 := by exact prefixLift 35332
  have htrace : WordTrace (prefixWord ++ tailWord_35332) baseStart_35332 baseEnd_35332 := by
    simpa [prefixWord, tailWord_35332, baseEnd_35332] using wordTrace_append hprefix tailTrace_35332
  have hstable : (prefixWord ++ tailWord_35332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35332).length < 2 ^ (prefixWord ++ tailWord_35332).sum := by decide
  have hdescent : baseEnd_35332 < baseStart_35332 := by decide
  rcases family_descends (prefixWord ++ tailWord_35332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35379 : List Nat := [1, 1, 1, 2, 4, 2, 5, 1, 1, 5]
def baseStart_35379 : Nat := 118140960795 + 35379 * 2 ^ 59
def prefixEnd_35379 : Nat := 4983230072969 + 3 ^ 40 * 35379 * 2
def baseEnd_35379 : Nat := 6055477358507437733267

theorem tailTrace_35379 : CollatzResearch.WordTrace tailWord_35379 prefixEnd_35379 6055477358507437733267 := by
  unfold tailWord_35379
  simp only [CollatzResearch.WordTrace]
  refine ⟨1290378138835400097261191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 860252092556933398174127 1290378138835400097261191)
  ·
    refine ⟨1935567208253100145891787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1290378138835400097261191 1935567208253100145891787)
    ·
      refine ⟨2903350812379650218837681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1935567208253100145891787 2903350812379650218837681)
      ·
        refine ⟨2177513109284737664128261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2903350812379650218837681 2177513109284737664128261)
        ·
          refine ⟨408283707990888312024049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2177513109284737664128261 408283707990888312024049)
          ·
            refine ⟨306212780993166234018037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 408283707990888312024049 306212780993166234018037)
            ·
              refine ⟨28707448218109334439191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 306212780993166234018037 28707448218109334439191)
              ·
                refine ⟨43061172327164001658787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28707448218109334439191 43061172327164001658787)
                ·
                  refine ⟨64591758490746002488181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43061172327164001658787 64591758490746002488181)
                  ·
                    refine ⟨6055477358507437733267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 64591758490746002488181 6055477358507437733267)
                    ·
                      rfl

theorem cell23_35379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 5, 1, 1, 5].length) (baseStart_35379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_35379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_35379 prefixEnd_35379 := by exact prefixLift 35379
  have htrace : WordTrace (prefixWord ++ tailWord_35379) baseStart_35379 baseEnd_35379 := by
    simpa [prefixWord, tailWord_35379, baseEnd_35379] using wordTrace_append hprefix tailTrace_35379
  have hstable : (prefixWord ++ tailWord_35379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35379).length < 2 ^ (prefixWord ++ tailWord_35379).sum := by decide
  have hdescent : baseEnd_35379 < baseStart_35379 := by decide
  rcases family_descends (prefixWord ++ tailWord_35379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35392 : List Nat := [2, 1, 1, 2, 2, 2, 2, 3, 4, 4]
def baseStart_35392 : Nat := 118140960795 + 35392 * 2 ^ 59
def prefixEnd_35392 : Nat := 4983230072969 + 3 ^ 40 * 35392 * 2
def baseEnd_35392 : Nat := 6057702441343587445747

theorem tailTrace_35392 : CollatzResearch.WordTrace tailWord_35392 prefixEnd_35392 6057702441343587445747 := by
  unfold tailWord_35392
  simp only [CollatzResearch.WordTrace]
  refine ⟨645426143894151658742215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 860568191858868878322953 645426143894151658742215)
  ·
    refine ⟨968139215841227488113323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 645426143894151658742215 968139215841227488113323)
    ·
      refine ⟨1452208823761841232169985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 968139215841227488113323 1452208823761841232169985)
      ·
        refine ⟨1089156617821380924127489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1452208823761841232169985 1089156617821380924127489)
        ·
          refine ⟨816867463366035693095617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1089156617821380924127489 816867463366035693095617)
          ·
            refine ⟨612650597524526769821713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 816867463366035693095617 612650597524526769821713)
            ·
              refine ⟨459487948143395077366285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 612650597524526769821713 459487948143395077366285)
              ·
                refine ⟨172307980553773154012357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 459487948143395077366285 172307980553773154012357)
                ·
                  refine ⟨32307746353832466377317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 172307980553773154012357 32307746353832466377317)
                  ·
                    refine ⟨6057702441343587445747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32307746353832466377317 6057702441343587445747)
                    ·
                      rfl

theorem cell23_35392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 3, 4, 4].length) (baseStart_35392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_35392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_35392 prefixEnd_35392 := by exact prefixLift 35392
  have htrace : WordTrace (prefixWord ++ tailWord_35392) baseStart_35392 baseEnd_35392 := by
    simpa [prefixWord, tailWord_35392, baseEnd_35392] using wordTrace_append hprefix tailTrace_35392
  have hstable : (prefixWord ++ tailWord_35392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35392).length < 2 ^ (prefixWord ++ tailWord_35392).sum := by decide
  have hdescent : baseEnd_35392 < baseStart_35392 := by decide
  rcases family_descends (prefixWord ++ tailWord_35392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35393 : List Nat := [1, 2, 5, 1, 1, 3, 1, 4, 1, 1, 3]
def baseStart_35393 : Nat := 118140960795 + 35393 * 2 ^ 59
def prefixEnd_35393 : Nat := 4983230072969 + 3 ^ 40 * 35393 * 2
def baseEnd_35393 : Nat := 18173620804685258424737

theorem tailTrace_35393 : CollatzResearch.WordTrace tailWord_35393 prefixEnd_35393 18173620804685258424737 := by
  unfold tailWord_35393
  simp only [CollatzResearch.WordTrace]
  refine ⟨1290888760784680488270833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 860592507189786992180555 1290888760784680488270833)
  ·
    refine ⟨968166570588510366203125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1290888760784680488270833 968166570588510366203125)
    ·
      refine ⟨90765615992672846831543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 968166570588510366203125 90765615992672846831543)
      ·
        refine ⟨136148423989009270247315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90765615992672846831543 136148423989009270247315)
        ·
          refine ⟨204222635983513905370973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136148423989009270247315 204222635983513905370973)
          ·
            refine ⟨76583488493817714514115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 204222635983513905370973 76583488493817714514115)
            ·
              refine ⟨114875232740726571771173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76583488493817714514115 114875232740726571771173)
              ·
                refine ⟨21539106138886232207095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 114875232740726571771173 21539106138886232207095)
                ·
                  refine ⟨32308659208329348310643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21539106138886232207095 32308659208329348310643)
                  ·
                    refine ⟨48462988812494022465965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32308659208329348310643 48462988812494022465965)
                    ·
                      refine ⟨18173620804685258424737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 48462988812494022465965 18173620804685258424737)
                      ·
                        rfl

theorem cell23_35393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 4, 1, 1, 3].length) (baseStart_35393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_35393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_35393 prefixEnd_35393 := by exact prefixLift 35393
  have htrace : WordTrace (prefixWord ++ tailWord_35393) baseStart_35393 baseEnd_35393 := by
    simpa [prefixWord, tailWord_35393, baseEnd_35393] using wordTrace_append hprefix tailTrace_35393
  have hstable : (prefixWord ++ tailWord_35393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35393).length < 2 ^ (prefixWord ++ tailWord_35393).sum := by decide
  have hdescent : baseEnd_35393 < baseStart_35393 := by decide
  rcases family_descends (prefixWord ++ tailWord_35393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35395 : List Nat := [1, 1, 1, 3, 1, 2, 1, 3, 3, 1, 6]
def baseStart_35395 : Nat := 118140960795 + 35395 * 2 ^ 59
def prefixEnd_35395 : Nat := 4983230072969 + 3 ^ 40 * 35395 * 2
def baseEnd_35395 : Nat := 18174647765994250599727

theorem tailTrace_35395 : CollatzResearch.WordTrace tailWord_35395 prefixEnd_35395 18174647765994250599727 := by
  unfold tailWord_35395
  simp only [CollatzResearch.WordTrace]
  refine ⟨1290961706777434829843639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 860641137851623219895759 1290961706777434829843639)
  ·
    refine ⟨1936442560166152244765459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1290961706777434829843639 1936442560166152244765459)
    ·
      refine ⟨2904663840249228367148189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1936442560166152244765459 2904663840249228367148189)
      ·
        refine ⟨1089248940093460637680571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2904663840249228367148189 1089248940093460637680571)
        ·
          refine ⟨1633873410140190956520857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1089248940093460637680571 1633873410140190956520857)
          ·
            refine ⟨1225405057605143217390643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1633873410140190956520857 1225405057605143217390643)
            ·
              refine ⟨1838107586407714826085965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1225405057605143217390643 1838107586407714826085965)
              ·
                refine ⟨689290344902893059782237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1838107586407714826085965 689290344902893059782237)
                ·
                  refine ⟨258483879338584897418339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 689290344902893059782237 258483879338584897418339)
                  ·
                    refine ⟨387725819007877346127509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 258483879338584897418339 387725819007877346127509)
                    ·
                      refine ⟨18174647765994250599727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 387725819007877346127509 18174647765994250599727)
                      ·
                        rfl

theorem cell23_35395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 3, 1, 6].length) (baseStart_35395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_35395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_35395 prefixEnd_35395 := by exact prefixLift 35395
  have htrace : WordTrace (prefixWord ++ tailWord_35395) baseStart_35395 baseEnd_35395 := by
    simpa [prefixWord, tailWord_35395, baseEnd_35395] using wordTrace_append hprefix tailTrace_35395
  have hstable : (prefixWord ++ tailWord_35395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35395).length < 2 ^ (prefixWord ++ tailWord_35395).sum := by decide
  have hdescent : baseEnd_35395 < baseStart_35395 := by decide
  rcases family_descends (prefixWord ++ tailWord_35395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35409 : List Nat := [1, 2, 2, 1, 3, 3, 2, 3, 2, 4]
def baseStart_35409 : Nat := 118140960795 + 35409 * 2 ^ 59
def prefixEnd_35409 : Nat := 4983230072969 + 3 ^ 40 * 35409 * 2
def baseEnd_35409 : Nat := 6060612165052398608221

theorem tailTrace_35409 : CollatzResearch.WordTrace tailWord_35409 prefixEnd_35409 6060612165052398608221 := by
  unfold tailWord_35409
  simp only [CollatzResearch.WordTrace]
  refine ⟨1291472328726715220853281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 860981552484476813902187 1291472328726715220853281)
  ·
    refine ⟨968604246545036415639961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1291472328726715220853281 968604246545036415639961)
    ·
      refine ⟨726453184908777311729971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 968604246545036415639961 726453184908777311729971)
      ·
        refine ⟨1089679777363165967594957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 726453184908777311729971 1089679777363165967594957)
        ·
          refine ⟨408629916511187237848109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1089679777363165967594957 408629916511187237848109)
          ·
            refine ⟨153236218691695214193041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 408629916511187237848109 153236218691695214193041)
            ·
              refine ⟨114927164018771410644781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 153236218691695214193041 114927164018771410644781)
              ·
                refine ⟨43097686507039278991793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 114927164018771410644781 43097686507039278991793)
                ·
                  refine ⟨32323264880279459243845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43097686507039278991793 32323264880279459243845)
                  ·
                    refine ⟨6060612165052398608221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32323264880279459243845 6060612165052398608221)
                    ·
                      rfl

theorem cell23_35409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 3, 2, 4].length) (baseStart_35409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_35409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_35409 prefixEnd_35409 := by exact prefixLift 35409
  have htrace : WordTrace (prefixWord ++ tailWord_35409) baseStart_35409 baseEnd_35409 := by
    simpa [prefixWord, tailWord_35409, baseEnd_35409] using wordTrace_append hprefix tailTrace_35409
  have hstable : (prefixWord ++ tailWord_35409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35409).length < 2 ^ (prefixWord ++ tailWord_35409).sum := by decide
  have hdescent : baseEnd_35409 < baseStart_35409 := by decide
  rcases family_descends (prefixWord ++ tailWord_35409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35420 : List Nat := [2, 2, 4, 1, 4, 1, 1, 1, 2, 3, 2]
def baseStart_35420 : Nat := 118140960795 + 35420 * 2 ^ 59
def prefixEnd_35420 : Nat := 4983230072969 + 3 ^ 40 * 35420 * 2
def baseEnd_35420 : Nat := 18187484782356652787113

theorem tailTrace_35420 : CollatzResearch.WordTrace tailWord_35420 prefixEnd_35420 18187484782356652787113 := by
  unfold tailWord_35420
  simp only [CollatzResearch.WordTrace]
  refine ⟨645936765843432049751857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 861249021124576066335809 645936765843432049751857)
  ·
    refine ⟨484452574382574037313893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 645936765843432049751857 484452574382574037313893)
    ·
      refine ⟨90834857696732631996355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 484452574382574037313893 90834857696732631996355)
      ·
        refine ⟨136252286545098947994533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90834857696732631996355 136252286545098947994533)
        ·
          refine ⟨25547303727206052748975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 136252286545098947994533 25547303727206052748975)
          ·
            refine ⟨38320955590809079123463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25547303727206052748975 38320955590809079123463)
            ·
              refine ⟨57481433386213618685195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38320955590809079123463 57481433386213618685195)
              ·
                refine ⟨86222150079320428027793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57481433386213618685195 86222150079320428027793)
                ·
                  refine ⟨64666612559490321020845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 86222150079320428027793 64666612559490321020845)
                  ·
                    refine ⟨24249979709808870382817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 64666612559490321020845 24249979709808870382817)
                    ·
                      refine ⟨18187484782356652787113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 24249979709808870382817 18187484782356652787113)
                      ·
                        rfl

theorem cell23_35420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 1, 2, 3, 2].length) (baseStart_35420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_35420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_35420 prefixEnd_35420 := by exact prefixLift 35420
  have htrace : WordTrace (prefixWord ++ tailWord_35420) baseStart_35420 baseEnd_35420 := by
    simpa [prefixWord, tailWord_35420, baseEnd_35420] using wordTrace_append hprefix tailTrace_35420
  have hstable : (prefixWord ++ tailWord_35420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35420).length < 2 ^ (prefixWord ++ tailWord_35420).sum := by decide
  have hdescent : baseEnd_35420 < baseStart_35420 := by decide
  rcases family_descends (prefixWord ++ tailWord_35420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35435 : List Nat := [1, 1, 1, 1, 2, 2, 1, 4, 1, 9]
def baseStart_35435 : Nat := 118140960795 + 35435 * 2 ^ 59
def prefixEnd_35435 : Nat := 4983230072969 + 3 ^ 40 * 35435 * 2
def baseEnd_35435 : Nat := 6065062330724698033181

theorem tailTrace_35435 : CollatzResearch.WordTrace tailWord_35435 prefixEnd_35435 6065062330724698033181 := by
  unfold tailWord_35435
  simp only [CollatzResearch.WordTrace]
  refine ⟨1292420626632521661299759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 861613751088347774199839 1292420626632521661299759)
  ·
    refine ⟨1938630939948782491949639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1292420626632521661299759 1938630939948782491949639)
    ·
      refine ⟨2907946409923173737924459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1938630939948782491949639 2907946409923173737924459)
      ·
        refine ⟨4361919614884760606886689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2907946409923173737924459 4361919614884760606886689)
        ·
          refine ⟨3271439711163570455165017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4361919614884760606886689 3271439711163570455165017)
          ·
            refine ⟨2453579783372677841373763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3271439711163570455165017 2453579783372677841373763)
            ·
              refine ⟨3680369675059016762060645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2453579783372677841373763 3680369675059016762060645)
              ·
                refine ⟨690069314073565642886371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3680369675059016762060645 690069314073565642886371)
                ·
                  refine ⟨1035103971110348464329557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 690069314073565642886371 1035103971110348464329557)
                  ·
                    refine ⟨6065062330724698033181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 1035103971110348464329557 6065062330724698033181)
                    ·
                      rfl

theorem cell23_35435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 9].length) (baseStart_35435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_35435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_35435 prefixEnd_35435 := by exact prefixLift 35435
  have htrace : WordTrace (prefixWord ++ tailWord_35435) baseStart_35435 baseEnd_35435 := by
    simpa [prefixWord, tailWord_35435, baseEnd_35435] using wordTrace_append hprefix tailTrace_35435
  have hstable : (prefixWord ++ tailWord_35435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35435).length < 2 ^ (prefixWord ++ tailWord_35435).sum := by decide
  have hdescent : baseEnd_35435 < baseStart_35435 := by decide
  rcases family_descends (prefixWord ++ tailWord_35435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35436 : List Nat := [2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 3]
def baseStart_35436 : Nat := 118140960795 + 35436 * 2 ^ 59
def prefixEnd_35436 : Nat := 4983230072969 + 3 ^ 40 * 35436 * 2
def baseEnd_35436 : Nat := 18195700472828590187039

theorem tailTrace_35436 : CollatzResearch.WordTrace tailWord_35436 prefixEnd_35436 18195700472828590187039 := by
  unfold tailWord_35436
  simp only [CollatzResearch.WordTrace]
  refine ⟨646228549814449416043081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 861638066419265888057441 646228549814449416043081)
  ·
    refine ⟨484671412360837062032311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 646228549814449416043081 484671412360837062032311)
    ·
      refine ⟨727007118541255593048467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 484671412360837062032311 727007118541255593048467)
      ·
        refine ⟨1090510677811883389572701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 727007118541255593048467 1090510677811883389572701)
        ·
          refine ⟨408941504179456271089763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1090510677811883389572701 408941504179456271089763)
          ·
            refine ⟨613412256269184406634645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 408941504179456271089763 613412256269184406634645)
            ·
              refine ⟨28753699512618019060999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 613412256269184406634645 28753699512618019060999)
              ·
                refine ⟨43130549268927028591499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28753699512618019060999 43130549268927028591499)
                ·
                  refine ⟨64695823903390542887249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43130549268927028591499 64695823903390542887249)
                  ·
                    refine ⟨48521867927542907165437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 64695823903390542887249 48521867927542907165437)
                    ·
                      refine ⟨18195700472828590187039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 48521867927542907165437 18195700472828590187039)
                      ·
                        rfl

theorem cell23_35436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 3].length) (baseStart_35436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_35436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_35436 prefixEnd_35436 := by exact prefixLift 35436
  have htrace : WordTrace (prefixWord ++ tailWord_35436) baseStart_35436 baseEnd_35436 := by
    simpa [prefixWord, tailWord_35436, baseEnd_35436] using wordTrace_append hprefix tailTrace_35436
  have hstable : (prefixWord ++ tailWord_35436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35436).length < 2 ^ (prefixWord ++ tailWord_35436).sum := by decide
  have hdescent : baseEnd_35436 < baseStart_35436 := by decide
  rcases family_descends (prefixWord ++ tailWord_35436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35459 : List Nat := [1, 1, 1, 3, 3, 1, 2, 1, 5, 3, 2]
def baseStart_35459 : Nat := 118140960795 + 35459 * 2 ^ 59
def prefixEnd_35459 : Nat := 4983230072969 + 3 ^ 40 * 35459 * 2
def baseEnd_35459 : Nat := 18207510527882000199433

theorem tailTrace_35459 : CollatzResearch.WordTrace tailWord_35459 prefixEnd_35459 18207510527882000199433 := by
  unfold tailWord_35459
  simp only [CollatzResearch.WordTrace]
  refine ⟨1293295978545573760173431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 862197319030382506782287 1293295978545573760173431)
  ·
    refine ⟨1939943967818360640260147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1293295978545573760173431 1939943967818360640260147)
    ·
      refine ⟨2909915951727540960390221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1939943967818360640260147 2909915951727540960390221)
      ·
        refine ⟨1091218481897827860146333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2909915951727540960390221 1091218481897827860146333)
        ·
          refine ⟨409206930711685447554875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1091218481897827860146333 409206930711685447554875)
          ·
            refine ⟨613810396067528171332313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 409206930711685447554875 613810396067528171332313)
            ·
              refine ⟨460357797050646128499235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 613810396067528171332313 460357797050646128499235)
              ·
                refine ⟨690536695575969192748853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 460357797050646128499235 690536695575969192748853)
                ·
                  refine ⟨64737815210247111820205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 690536695575969192748853 64737815210247111820205)
                  ·
                    refine ⟨24276680703842666932577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 64737815210247111820205 24276680703842666932577)
                    ·
                      refine ⟨18207510527882000199433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 24276680703842666932577 18207510527882000199433)
                      ·
                        rfl

theorem cell23_35459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 5, 3, 2].length) (baseStart_35459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_35459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_35459 prefixEnd_35459 := by exact prefixLift 35459
  have htrace : WordTrace (prefixWord ++ tailWord_35459) baseStart_35459 baseEnd_35459 := by
    simpa [prefixWord, tailWord_35459, baseEnd_35459] using wordTrace_append hprefix tailTrace_35459
  have hstable : (prefixWord ++ tailWord_35459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35459).length < 2 ^ (prefixWord ++ tailWord_35459).sum := by decide
  have hdescent : baseEnd_35459 < baseStart_35459 := by decide
  rcases family_descends (prefixWord ++ tailWord_35459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35566 : List Nat := [4, 1, 2, 1, 1, 3, 1, 1, 2, 5, 2]
def baseStart_35566 : Nat := 118140960795 + 35566 * 2 ^ 59
def prefixEnd_35566 : Nat := 4983230072969 + 3 ^ 40 * 35566 * 2
def baseEnd_35566 : Nat := 18262452957913081561441

theorem tailTrace_35566 : CollatzResearch.WordTrace tailWord_35566 prefixEnd_35566 18262452957913081561441 := by
  unfold tailWord_35566
  simp only [CollatzResearch.WordTrace]
  refine ⟨162149823644741379289819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 864799059438620689545701 162149823644741379289819)
  ·
    refine ⟨243224735467112068934729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 162149823644741379289819 243224735467112068934729)
    ·
      refine ⟨182418551600334051701047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 243224735467112068934729 182418551600334051701047)
      ·
        refine ⟨273627827400501077551571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182418551600334051701047 273627827400501077551571)
        ·
          refine ⟨410441741100751616327357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 273627827400501077551571 410441741100751616327357)
          ·
            refine ⟨153915652912781856122759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 410441741100751616327357 153915652912781856122759)
            ·
              refine ⟨230873479369172784184139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 153915652912781856122759 230873479369172784184139)
              ·
                refine ⟨346310219053759176276209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 230873479369172784184139 346310219053759176276209)
                ·
                  refine ⟨259732664290319382207157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 346310219053759176276209 259732664290319382207157)
                  ·
                    refine ⟨24349937277217442081921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 259732664290319382207157 24349937277217442081921)
                    ·
                      refine ⟨18262452957913081561441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 24349937277217442081921 18262452957913081561441)
                      ·
                        rfl

theorem cell23_35566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 2, 5, 2].length) (baseStart_35566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_35566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_35566 prefixEnd_35566 := by exact prefixLift 35566
  have htrace : WordTrace (prefixWord ++ tailWord_35566) baseStart_35566 baseEnd_35566 := by
    simpa [prefixWord, tailWord_35566, baseEnd_35566] using wordTrace_append hprefix tailTrace_35566
  have hstable : (prefixWord ++ tailWord_35566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35566).length < 2 ^ (prefixWord ++ tailWord_35566).sum := by decide
  have hdescent : baseEnd_35566 < baseStart_35566 := by decide
  rcases family_descends (prefixWord ++ tailWord_35566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35599 : List Nat := [1, 1, 2, 1, 1, 1, 7, 1, 1, 4, 3]
def baseStart_35599 : Nat := 118140960795 + 35599 * 2 ^ 59
def prefixEnd_35599 : Nat := 4983230072969 + 3 ^ 40 * 35599 * 2
def baseEnd_35599 : Nat := 18279397819511452448789

theorem tailTrace_35599 : CollatzResearch.WordTrace tailWord_35599 prefixEnd_35599 18279397819511452448789 := by
  unfold tailWord_35599
  simp only [CollatzResearch.WordTrace]
  refine ⟨1298402198038377670269851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 865601465358918446846567 1298402198038377670269851)
  ·
    refine ⟨1947603297057566505404777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1298402198038377670269851 1947603297057566505404777)
    ·
      refine ⟨1460702472793174879053583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1947603297057566505404777 1460702472793174879053583)
      ·
        refine ⟨2191053709189762318580375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1460702472793174879053583 2191053709189762318580375)
        ·
          refine ⟨3286580563784643477870563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2191053709189762318580375 3286580563784643477870563)
          ·
            refine ⟨4929870845676965216805845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3286580563784643477870563 4929870845676965216805845)
            ·
              refine ⟨115543847945553872268887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 4929870845676965216805845 115543847945553872268887)
              ·
                refine ⟨173315771918330808403331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115543847945553872268887 173315771918330808403331)
                ·
                  refine ⟨259973657877496212604997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 173315771918330808403331 259973657877496212604997)
                  ·
                    refine ⟨48745060852030539863437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 259973657877496212604997 48745060852030539863437)
                    ·
                      refine ⟨18279397819511452448789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 48745060852030539863437 18279397819511452448789)
                      ·
                        rfl

theorem cell23_35599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 1, 1, 4, 3].length) (baseStart_35599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_35599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_35599 prefixEnd_35599 := by exact prefixLift 35599
  have htrace : WordTrace (prefixWord ++ tailWord_35599) baseStart_35599 baseEnd_35599 := by
    simpa [prefixWord, tailWord_35599, baseEnd_35599] using wordTrace_append hprefix tailTrace_35599
  have hstable : (prefixWord ++ tailWord_35599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35599).length < 2 ^ (prefixWord ++ tailWord_35599).sum := by decide
  have hdescent : baseEnd_35599 < baseStart_35599 := by decide
  rcases family_descends (prefixWord ++ tailWord_35599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35656 : List Nat := [2, 1, 3, 1, 1, 3, 1, 3, 1, 5, 2]
def baseStart_35656 : Nat := 118140960795 + 35656 * 2 ^ 59
def prefixEnd_35656 : Nat := 4983230072969 + 3 ^ 40 * 35656 * 2
def baseEnd_35656 : Nat := 18308666216817729436027

theorem tailTrace_35656 : CollatzResearch.WordTrace tailWord_35656 prefixEnd_35656 18308666216817729436027 := by
  unfold tailWord_35656
  simp only [CollatzResearch.WordTrace]
  refine ⟨650240579415938202547411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 866987439221250936729881 650240579415938202547411)
  ·
    refine ⟨975360869123907303821117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 650240579415938202547411 975360869123907303821117)
    ·
      refine ⟨365760325921465238932919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 975360869123907303821117 365760325921465238932919)
      ·
        refine ⟨548640488882197858399379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 365760325921465238932919 548640488882197858399379)
        ·
          refine ⟨822960733323296787599069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 548640488882197858399379 822960733323296787599069)
          ·
            refine ⟨308610274996236295349651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 822960733323296787599069 308610274996236295349651)
            ·
              refine ⟨462915412494354443024477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 308610274996236295349651 462915412494354443024477)
              ·
                refine ⟨173593279685382916134179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 462915412494354443024477 173593279685382916134179)
                ·
                  refine ⟨260389919528074374201269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 173593279685382916134179 260389919528074374201269)
                  ·
                    refine ⟨24411554955756972581369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 260389919528074374201269 24411554955756972581369)
                    ·
                      refine ⟨18308666216817729436027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 24411554955756972581369 18308666216817729436027)
                      ·
                        rfl

theorem cell23_35656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 3, 1, 5, 2].length) (baseStart_35656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_35656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_35656 prefixEnd_35656 := by exact prefixLift 35656
  have htrace : WordTrace (prefixWord ++ tailWord_35656) baseStart_35656 baseEnd_35656 := by
    simpa [prefixWord, tailWord_35656, baseEnd_35656] using wordTrace_append hprefix tailTrace_35656
  have hstable : (prefixWord ++ tailWord_35656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35656).length < 2 ^ (prefixWord ++ tailWord_35656).sum := by decide
  have hdescent : baseEnd_35656 < baseStart_35656 := by decide
  rcases family_descends (prefixWord ++ tailWord_35656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35666 : List Nat := [3, 2, 2, 1, 1, 2, 1, 5, 1, 5]
def baseStart_35666 : Nat := 118140960795 + 35666 * 2 ^ 59
def prefixEnd_35666 : Nat := 4983230072969 + 3 ^ 40 * 35666 * 2
def baseEnd_35666 : Nat := 6104600341120896770327

theorem tailTrace_35666 : CollatzResearch.WordTrace tailWord_35666 prefixEnd_35666 6104600341120896770327 := by
  unfold tailWord_35666
  simp only [CollatzResearch.WordTrace]
  refine ⟨325211472198912028239713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 867230592530432075305901 325211472198912028239713)
  ·
    refine ⟨243908604149184021179785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 325211472198912028239713 243908604149184021179785)
    ·
      refine ⟨182931453111888015884839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 243908604149184021179785 182931453111888015884839)
      ·
        refine ⟨274397179667832023827259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182931453111888015884839 274397179667832023827259)
        ·
          refine ⟨411595769501748035740889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 274397179667832023827259 411595769501748035740889)
          ·
            refine ⟨308696827126311026805667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 411595769501748035740889 308696827126311026805667)
            ·
              refine ⟨463045240689466540208501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 308696827126311026805667 463045240689466540208501)
              ·
                refine ⟨43410491314637488144547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 463045240689466540208501 43410491314637488144547)
                ·
                  refine ⟨65115736971956232216821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43410491314637488144547 65115736971956232216821)
                  ·
                    refine ⟨6104600341120896770327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 65115736971956232216821 6104600341120896770327)
                    ·
                      rfl

theorem cell23_35666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 5, 1, 5].length) (baseStart_35666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_35666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_35666 prefixEnd_35666 := by exact prefixLift 35666
  have htrace : WordTrace (prefixWord ++ tailWord_35666) baseStart_35666 baseEnd_35666 := by
    simpa [prefixWord, tailWord_35666, baseEnd_35666] using wordTrace_append hprefix tailTrace_35666
  have hstable : (prefixWord ++ tailWord_35666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35666).length < 2 ^ (prefixWord ++ tailWord_35666).sum := by decide
  have hdescent : baseEnd_35666 < baseStart_35666 := by decide
  rcases family_descends (prefixWord ++ tailWord_35666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35673 : List Nat := [1, 2, 1, 2, 2, 5, 1, 2, 2, 3, 2]
def baseStart_35673 : Nat := 118140960795 + 35673 * 2 ^ 59
def prefixEnd_35673 : Nat := 4983230072969 + 3 ^ 40 * 35673 * 2
def baseEnd_35673 : Nat := 18317395387944162923449

theorem tailTrace_35673 : CollatzResearch.WordTrace tailWord_35673 prefixEnd_35673 18317395387944162923449 := by
  unfold tailWord_35673
  simp only [CollatzResearch.WordTrace]
  refine ⟨1301101199770288308463673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 867400799846858872309115 1301101199770288308463673)
  ·
    refine ⟨975825899827716231347755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1301101199770288308463673 975825899827716231347755)
    ·
      refine ⟨1463738849741574347021633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 975825899827716231347755 1463738849741574347021633)
      ·
        refine ⟨1097804137306180760266225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1463738849741574347021633 1097804137306180760266225)
        ·
          refine ⟨823353102979635570199669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1097804137306180760266225 823353102979635570199669)
          ·
            refine ⟨77189353404340834706219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 823353102979635570199669 77189353404340834706219)
            ·
              refine ⟨115784030106511252059329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77189353404340834706219 115784030106511252059329)
              ·
                refine ⟨86838022579883439044497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 115784030106511252059329 86838022579883439044497)
                ·
                  refine ⟨65128516934912579283373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 86838022579883439044497 65128516934912579283373)
                  ·
                    refine ⟨24423193850592217231265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 65128516934912579283373 24423193850592217231265)
                    ·
                      refine ⟨18317395387944162923449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 24423193850592217231265 18317395387944162923449)
                      ·
                        rfl

theorem cell23_35673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 2, 2, 3, 2].length) (baseStart_35673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_35673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_35673 prefixEnd_35673 := by exact prefixLift 35673
  have htrace : WordTrace (prefixWord ++ tailWord_35673) baseStart_35673 baseEnd_35673 := by
    simpa [prefixWord, tailWord_35673, baseEnd_35673] using wordTrace_append hprefix tailTrace_35673
  have hstable : (prefixWord ++ tailWord_35673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35673).length < 2 ^ (prefixWord ++ tailWord_35673).sum := by decide
  have hdescent : baseEnd_35673 < baseStart_35673 := by decide
  rcases family_descends (prefixWord ++ tailWord_35673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35689 : List Nat := [1, 2, 1, 1, 1, 3, 1, 1, 1, 8, 3]
def baseStart_35689 : Nat := 118140960795 + 35689 * 2 ^ 59
def prefixEnd_35689 : Nat := 4983230072969 + 3 ^ 40 * 35689 * 2
def baseEnd_35689 : Nat := 18325611078416100323375

theorem tailTrace_35689 : CollatzResearch.WordTrace tailWord_35689 prefixEnd_35689 18325611078416100323375 := by
  unfold tailWord_35689
  simp only [CollatzResearch.WordTrace]
  refine ⟨1301684767712323041046121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 867789845141548694030747 1301684767712323041046121)
  ·
    refine ⟨976263575784242280784591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1301684767712323041046121 976263575784242280784591)
    ·
      refine ⟨1464395363676363421176887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 976263575784242280784591 1464395363676363421176887)
      ·
        refine ⟨2196593045514545131765331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1464395363676363421176887 2196593045514545131765331)
        ·
          refine ⟨3294889568271817697647997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2196593045514545131765331 3294889568271817697647997)
          ·
            refine ⟨1235583588101931636617999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3294889568271817697647997 1235583588101931636617999)
            ·
              refine ⟨1853375382152897454926999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1235583588101931636617999 1853375382152897454926999)
              ·
                refine ⟨2780063073229346182390499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1853375382152897454926999 2780063073229346182390499)
                ·
                  refine ⟨4170094609844019273585749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2780063073229346182390499 4170094609844019273585749)
                  ·
                    refine ⟨48868296209109600862333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 4170094609844019273585749 48868296209109600862333)
                    ·
                      refine ⟨18325611078416100323375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 48868296209109600862333 18325611078416100323375)
                      ·
                        rfl

theorem cell23_35689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 8, 3].length) (baseStart_35689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_35689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_35689 prefixEnd_35689 := by exact prefixLift 35689
  have htrace : WordTrace (prefixWord ++ tailWord_35689) baseStart_35689 baseEnd_35689 := by
    simpa [prefixWord, tailWord_35689, baseEnd_35689] using wordTrace_append hprefix tailTrace_35689
  have hstable : (prefixWord ++ tailWord_35689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35689).length < 2 ^ (prefixWord ++ tailWord_35689).sum := by decide
  have hdescent : baseEnd_35689 < baseStart_35689 := by decide
  rcases family_descends (prefixWord ++ tailWord_35689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35699 : List Nat := [1, 1, 1, 2, 2, 1, 6, 1, 1, 1, 6]
def baseStart_35699 : Nat := 118140960795 + 35699 * 2 ^ 59
def prefixEnd_35699 : Nat := 4983230072969 + 3 ^ 40 * 35699 * 2
def baseEnd_35699 : Nat := 18330745884961061198329

theorem tailTrace_35699 : CollatzResearch.WordTrace tailWord_35699 prefixEnd_35699 18330745884961061198329 := by
  unfold tailWord_35699
  simp only [CollatzResearch.WordTrace]
  refine ⟨1302049497676094748910151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 868032998450729832606767 1302049497676094748910151)
  ·
    refine ⟨1953074246514142123365227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1302049497676094748910151 1953074246514142123365227)
    ·
      refine ⟨2929611369771213185047841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1953074246514142123365227 2929611369771213185047841)
      ·
        refine ⟨2197208527328409888785881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2929611369771213185047841 2197208527328409888785881)
        ·
          refine ⟨1647906395496307416589411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2197208527328409888785881 1647906395496307416589411)
          ·
            refine ⟨2471859593244461124884117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1647906395496307416589411 2471859593244461124884117)
            ·
              refine ⟨115868418433334115228943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2471859593244461124884117 115868418433334115228943)
              ·
                refine ⟨173802627650001172843415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115868418433334115228943 173802627650001172843415)
                ·
                  refine ⟨260703941475001759265123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 173802627650001172843415 260703941475001759265123)
                  ·
                    refine ⟨391055912212502638897685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 260703941475001759265123 391055912212502638897685)
                    ·
                      refine ⟨18330745884961061198329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 391055912212502638897685 18330745884961061198329)
                      ·
                        rfl

theorem cell23_35699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 1, 1, 1, 6].length) (baseStart_35699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_35699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_35699 prefixEnd_35699 := by exact prefixLift 35699
  have htrace : WordTrace (prefixWord ++ tailWord_35699) baseStart_35699 baseEnd_35699 := by
    simpa [prefixWord, tailWord_35699, baseEnd_35699] using wordTrace_append hprefix tailTrace_35699
  have hstable : (prefixWord ++ tailWord_35699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35699).length < 2 ^ (prefixWord ++ tailWord_35699).sum := by decide
  have hdescent : baseEnd_35699 < baseStart_35699 := by decide
  rcases family_descends (prefixWord ++ tailWord_35699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35703 : List Nat := [1, 1, 3, 1, 1, 2, 1, 6, 3, 2, 2]
def baseStart_35703 : Nat := 118140960795 + 35703 * 2 ^ 59
def prefixEnd_35703 : Nat := 4983230072969 + 3 ^ 40 * 35703 * 2
def baseEnd_35703 : Nat := 18332799807579045548311

theorem tailTrace_35703 : CollatzResearch.WordTrace tailWord_35703 prefixEnd_35703 18332799807579045548311 := by
  unfold tailWord_35703
  simp only [CollatzResearch.WordTrace]
  refine ⟨1302195389661603432055763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 868130259774402288037175 1302195389661603432055763)
  ·
    refine ⟨1953293084492405148083645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1302195389661603432055763 1953293084492405148083645)
    ·
      refine ⟨732484906684651930531367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1953293084492405148083645 732484906684651930531367)
      ·
        refine ⟨1098727360026977895797051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 732484906684651930531367 1098727360026977895797051)
        ·
          refine ⟨1648091040040466843695577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1098727360026977895797051 1648091040040466843695577)
          ·
            refine ⟨1236068280030350132771683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1648091040040466843695577 1236068280030350132771683)
            ·
              refine ⟨1854102420045525199157525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1236068280030350132771683 1854102420045525199157525)
              ·
                refine ⟨86911050939633993710509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1854102420045525199157525 86911050939633993710509)
                ·
                  refine ⟨32591644102362747641441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 86911050939633993710509 32591644102362747641441)
                  ·
                    refine ⟨24443733076772060731081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32591644102362747641441 24443733076772060731081)
                    ·
                      refine ⟨18332799807579045548311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 24443733076772060731081 18332799807579045548311)
                      ·
                        rfl

theorem cell23_35703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 6, 3, 2, 2].length) (baseStart_35703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_35703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_35703 prefixEnd_35703 := by exact prefixLift 35703
  have htrace : WordTrace (prefixWord ++ tailWord_35703) baseStart_35703 baseEnd_35703 := by
    simpa [prefixWord, tailWord_35703, baseEnd_35703] using wordTrace_append hprefix tailTrace_35703
  have hstable : (prefixWord ++ tailWord_35703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35703).length < 2 ^ (prefixWord ++ tailWord_35703).sum := by decide
  have hdescent : baseEnd_35703 < baseStart_35703 := by decide
  rcases family_descends (prefixWord ++ tailWord_35703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35709 : List Nat := [1, 4, 1, 1, 2, 1, 4, 9]
def baseStart_35709 : Nat := 118140960795 + 35709 * 2 ^ 59
def prefixEnd_35709 : Nat := 4983230072969 + 3 ^ 40 * 35709 * 2
def baseEnd_35709 : Nat := 679106692278000817529

theorem tailTrace_35709 : CollatzResearch.WordTrace tailWord_35709 prefixEnd_35709 679106692278000817529 := by
  unfold tailWord_35709
  simp only [CollatzResearch.WordTrace]
  refine ⟨1302414227639866456774181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 868276151759910971182787 1302414227639866456774181)
  ·
    refine ⟨244202667682474960645159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1302414227639866456774181 244202667682474960645159)
    ·
      refine ⟨366304001523712440967739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244202667682474960645159 366304001523712440967739)
      ·
        refine ⟨549456002285568661451609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 366304001523712440967739 549456002285568661451609)
        ·
          refine ⟨412092001714176496088707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 549456002285568661451609 412092001714176496088707)
          ·
            refine ⟨618138002571264744133061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 412092001714176496088707 618138002571264744133061)
            ·
              refine ⟨115900875482112139524949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 618138002571264744133061 115900875482112139524949)
              ·
                refine ⟨679106692278000817529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 115900875482112139524949 679106692278000817529)
                ·
                  rfl

theorem cell23_35709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 9].length) (baseStart_35709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_35709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_35709 prefixEnd_35709 := by exact prefixLift 35709
  have htrace : WordTrace (prefixWord ++ tailWord_35709) baseStart_35709 baseEnd_35709 := by
    simpa [prefixWord, tailWord_35709, baseEnd_35709] using wordTrace_append hprefix tailTrace_35709
  have hstable : (prefixWord ++ tailWord_35709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35709).length < 2 ^ (prefixWord ++ tailWord_35709).sum := by decide
  have hdescent : baseEnd_35709 < baseStart_35709 := by decide
  rcases family_descends (prefixWord ++ tailWord_35709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35720 : List Nat := [2, 1, 3, 3, 2, 2, 3, 1, 1, 1, 4]
def baseStart_35720 : Nat := 118140960795 + 35720 * 2 ^ 59
def prefixEnd_35720 : Nat := 4983230072969 + 3 ^ 40 * 35720 * 2
def baseEnd_35720 : Nat := 18341528978705479035733

theorem tailTrace_35720 : CollatzResearch.WordTrace tailWord_35720 prefixEnd_35720 18341528978705479035733 := by
  unfold tailWord_35720
  simp only [CollatzResearch.WordTrace]
  refine ⟨651407715300007667712307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 868543620400010223616409 651407715300007667712307)
  ·
    refine ⟨977111572950011501568461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 651407715300007667712307 977111572950011501568461)
    ·
      refine ⟨366416839856254313088173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 977111572950011501568461 366416839856254313088173)
      ·
        refine ⟨137406314946095367408065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 366416839856254313088173 137406314946095367408065)
        ·
          refine ⟨103054736209571525556049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137406314946095367408065 103054736209571525556049)
          ·
            refine ⟨77291052157178644167037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103054736209571525556049 77291052157178644167037)
            ·
              refine ⟨28984144558941991562639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77291052157178644167037 28984144558941991562639)
              ·
                refine ⟨43476216838412987343959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28984144558941991562639 43476216838412987343959)
                ·
                  refine ⟨65214325257619481015939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43476216838412987343959 65214325257619481015939)
                  ·
                    refine ⟨97821487886429221523909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 65214325257619481015939 97821487886429221523909)
                    ·
                      refine ⟨18341528978705479035733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 97821487886429221523909 18341528978705479035733)
                      ·
                        rfl

theorem cell23_35720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 3, 1, 1, 1, 4].length) (baseStart_35720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_35720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_35720 prefixEnd_35720 := by exact prefixLift 35720
  have htrace : WordTrace (prefixWord ++ tailWord_35720) baseStart_35720 baseEnd_35720 := by
    simpa [prefixWord, tailWord_35720, baseEnd_35720] using wordTrace_append hprefix tailTrace_35720
  have hstable : (prefixWord ++ tailWord_35720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35720).length < 2 ^ (prefixWord ++ tailWord_35720).sum := by decide
  have hdescent : baseEnd_35720 < baseStart_35720 := by decide
  rcases family_descends (prefixWord ++ tailWord_35720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35749 : List Nat := [1, 3, 1, 2, 1, 1, 1, 1, 3, 4, 5]
def baseStart_35749 : Nat := 118140960795 + 35749 * 2 ^ 59
def prefixEnd_35749 : Nat := 4983230072969 + 3 ^ 40 * 35749 * 2
def baseEnd_35749 : Nat := 18356419917685865573099

theorem tailTrace_35749 : CollatzResearch.WordTrace tailWord_35749 prefixEnd_35749 18356419917685865573099 := by
  unfold tailWord_35749
  simp only [CollatzResearch.WordTrace]
  refine ⟨1303873147494953288230301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 869248764996635525486867 1303873147494953288230301)
  ·
    refine ⟨488952430310607483086363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1303873147494953288230301 488952430310607483086363)
    ·
      refine ⟨733428645465911224629545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 488952430310607483086363 733428645465911224629545)
      ·
        refine ⟨550071484099433418472159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 733428645465911224629545 550071484099433418472159)
        ·
          refine ⟨825107226149150127708239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 550071484099433418472159 825107226149150127708239)
          ·
            refine ⟨1237660839223725191562359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 825107226149150127708239 1237660839223725191562359)
            ·
              refine ⟨1856491258835587787343539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1237660839223725191562359 1856491258835587787343539)
              ·
                refine ⟨2784736888253381681015309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1856491258835587787343539 2784736888253381681015309)
                ·
                  refine ⟨1044276333095018130380741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2784736888253381681015309 1044276333095018130380741)
                  ·
                    refine ⟨195801812455315899446389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1044276333095018130380741 195801812455315899446389)
                    ·
                      refine ⟨18356419917685865573099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 195801812455315899446389 18356419917685865573099)
                      ·
                        rfl

theorem cell23_35749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 4, 5].length) (baseStart_35749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_35749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_35749 prefixEnd_35749 := by exact prefixLift 35749
  have htrace : WordTrace (prefixWord ++ tailWord_35749) baseStart_35749 baseEnd_35749 := by
    simpa [prefixWord, tailWord_35749, baseEnd_35749] using wordTrace_append hprefix tailTrace_35749
  have hstable : (prefixWord ++ tailWord_35749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35749).length < 2 ^ (prefixWord ++ tailWord_35749).sum := by decide
  have hdescent : baseEnd_35749 < baseStart_35749 := by decide
  rcases family_descends (prefixWord ++ tailWord_35749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35753 : List Nat := [1, 2, 1, 1, 1, 1, 5, 5, 2, 1, 3]
def baseStart_35753 : Nat := 118140960795 + 35753 * 2 ^ 59
def prefixEnd_35753 : Nat := 4983230072969 + 3 ^ 40 * 35753 * 2
def baseEnd_35753 : Nat := 18358473840303849923081

theorem tailTrace_35753 : CollatzResearch.WordTrace tailWord_35753 prefixEnd_35753 18358473840303849923081 := by
  unfold tailWord_35753
  simp only [CollatzResearch.WordTrace]
  refine ⟨1304019039480461971375913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 869346026320307980917275 1304019039480461971375913)
  ·
    refine ⟨978014279610346478531935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1304019039480461971375913 978014279610346478531935)
    ·
      refine ⟨1467021419415519717797903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 978014279610346478531935 1467021419415519717797903)
      ·
        refine ⟨2200532129123279576696855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1467021419415519717797903 2200532129123279576696855)
        ·
          refine ⟨3300798193684919365045283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2200532129123279576696855 3300798193684919365045283)
          ·
            refine ⟨4951197290527379047567925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3300798193684919365045283 4951197290527379047567925)
            ·
              refine ⟨464174745986941785709493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4951197290527379047567925 464174745986941785709493)
              ·
                refine ⟨43516382436275792410265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 464174745986941785709493 43516382436275792410265)
                ·
                  refine ⟨32637286827206844307699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43516382436275792410265 32637286827206844307699)
                  ·
                    refine ⟨48955930240810266461549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32637286827206844307699 48955930240810266461549)
                    ·
                      refine ⟨18358473840303849923081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 48955930240810266461549 18358473840303849923081)
                      ·
                        rfl

theorem cell23_35753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 5, 2, 1, 3].length) (baseStart_35753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_35753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_35753 prefixEnd_35753 := by exact prefixLift 35753
  have htrace : WordTrace (prefixWord ++ tailWord_35753) baseStart_35753 baseEnd_35753 := by
    simpa [prefixWord, tailWord_35753, baseEnd_35753] using wordTrace_append hprefix tailTrace_35753
  have hstable : (prefixWord ++ tailWord_35753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35753).length < 2 ^ (prefixWord ++ tailWord_35753).sum := by decide
  have hdescent : baseEnd_35753 < baseStart_35753 := by decide
  rcases family_descends (prefixWord ++ tailWord_35753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35816 : List Nat := [2, 1, 4, 1, 1, 1, 4, 2, 7]
def baseStart_35816 : Nat := 118140960795 + 35816 * 2 ^ 59
def prefixEnd_35816 : Nat := 4983230072969 + 3 ^ 40 * 35816 * 2
def baseEnd_35816 : Nat := 2043424791281900381699

theorem tailTrace_35816 : CollatzResearch.WordTrace tailWord_35816 prefixEnd_35816 2043424791281900381699 := by
  unfold tailWord_35816
  simp only [CollatzResearch.WordTrace]
  refine ⟨653158419126111865459651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 870877892168149153946201 653158419126111865459651)
  ·
    refine ⟨979737628689167798189477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 653158419126111865459651 979737628689167798189477)
    ·
      refine ⟨183700805379218962160527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 979737628689167798189477 183700805379218962160527)
      ·
        refine ⟨275551208068828443240791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183700805379218962160527 275551208068828443240791)
        ·
          refine ⟨413326812103242664861187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 275551208068828443240791 413326812103242664861187)
          ·
            refine ⟨619990218154863997291781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 413326812103242664861187 619990218154863997291781)
            ·
              refine ⟨116248165904036999492209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 619990218154863997291781 116248165904036999492209)
              ·
                refine ⟨87186124428027749619157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 116248165904036999492209 87186124428027749619157)
                ·
                  refine ⟨2043424791281900381699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 87186124428027749619157 2043424791281900381699)
                  ·
                    rfl

theorem cell23_35816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 2, 7].length) (baseStart_35816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_35816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_35816 prefixEnd_35816 := by exact prefixLift 35816
  have htrace : WordTrace (prefixWord ++ tailWord_35816) baseStart_35816 baseEnd_35816 := by
    simpa [prefixWord, tailWord_35816, baseEnd_35816] using wordTrace_append hprefix tailTrace_35816
  have hstable : (prefixWord ++ tailWord_35816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35816).length < 2 ^ (prefixWord ++ tailWord_35816).sum := by decide
  have hdescent : baseEnd_35816 < baseStart_35816 := by decide
  rcases family_descends (prefixWord ++ tailWord_35816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35883 : List Nat := [1, 1, 1, 1, 2, 1, 8, 1, 2, 1, 4]
def baseStart_35883 : Nat := 118140960795 + 35883 * 2 ^ 59
def prefixEnd_35883 : Nat := 4983230072969 + 3 ^ 40 * 35883 * 2
def baseEnd_35883 : Nat := 18425226325388341297483

theorem tailTrace_35883 : CollatzResearch.WordTrace tailWord_35883 prefixEnd_35883 18425226325388341297483 := by
  unfold tailWord_35883
  simp only [CollatzResearch.WordTrace]
  refine ⟨1308760529009494173608303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 872507019339662782405535 1308760529009494173608303)
  ·
    refine ⟨1963140793514241260412455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1308760529009494173608303 1963140793514241260412455)
    ·
      refine ⟨2944711190271361890618683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1963140793514241260412455 2944711190271361890618683)
      ·
        refine ⟨4417066785407042835928025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2944711190271361890618683 4417066785407042835928025)
        ·
          refine ⟨3312800089055282126946019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4417066785407042835928025 3312800089055282126946019)
          ·
            refine ⟨4969200133582923190419029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3312800089055282126946019 4969200133582923190419029)
            ·
              refine ⟨58232814065424881137723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4969200133582923190419029 58232814065424881137723)
              ·
                refine ⟨87349221098137321706585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58232814065424881137723 87349221098137321706585)
                ·
                  refine ⟨65511915823602991279939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 87349221098137321706585 65511915823602991279939)
                  ·
                    refine ⟨98267873735404486919909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 65511915823602991279939 98267873735404486919909)
                    ·
                      refine ⟨18425226325388341297483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 98267873735404486919909 18425226325388341297483)
                      ·
                        rfl

theorem cell23_35883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 1, 2, 1, 4].length) (baseStart_35883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_35883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_35883 prefixEnd_35883 := by exact prefixLift 35883
  have htrace : WordTrace (prefixWord ++ tailWord_35883) baseStart_35883 baseEnd_35883 := by
    simpa [prefixWord, tailWord_35883, baseEnd_35883] using wordTrace_append hprefix tailTrace_35883
  have hstable : (prefixWord ++ tailWord_35883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35883).length < 2 ^ (prefixWord ++ tailWord_35883).sum := by decide
  have hdescent : baseEnd_35883 < baseStart_35883 := by decide
  rcases family_descends (prefixWord ++ tailWord_35883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35917 : List Nat := [1, 6, 1, 1, 1, 3, 1, 1, 2, 4, 2]
def baseStart_35917 : Nat := 118140960795 + 35917 * 2 ^ 59
def prefixEnd_35917 : Nat := 4983230072969 + 3 ^ 40 * 35917 * 2
def baseEnd_35917 : Nat := 18442684667641208272327

theorem tailTrace_35917 : CollatzResearch.WordTrace tailWord_35917 prefixEnd_35917 18442684667641208272327 := by
  unfold tailWord_35917
  simp only [CollatzResearch.WordTrace]
  refine ⟨1310000610886317980346005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 873333740590878653564003 1310000610886317980346005)
  ·
    refine ⟨61406278635296155328719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 1310000610886317980346005 61406278635296155328719)
    ·
      refine ⟨92109417952944232993079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61406278635296155328719 92109417952944232993079)
      ·
        refine ⟨138164126929416349489619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92109417952944232993079 138164126929416349489619)
        ·
          refine ⟨207246190394124524234429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 138164126929416349489619 207246190394124524234429)
          ·
            refine ⟨77717321397796696587911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 207246190394124524234429 77717321397796696587911)
            ·
              refine ⟨116575982096695044881867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77717321397796696587911 116575982096695044881867)
              ·
                refine ⟨174863973145042567322801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 116575982096695044881867 174863973145042567322801)
                ·
                  refine ⟨131147979858781925492101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 174863973145042567322801 131147979858781925492101)
                  ·
                    refine ⟨24590246223521611029769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 131147979858781925492101 24590246223521611029769)
                    ·
                      refine ⟨18442684667641208272327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 24590246223521611029769 18442684667641208272327)
                      ·
                        rfl

theorem cell23_35917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 1, 2, 4, 2].length) (baseStart_35917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_35917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_35917 prefixEnd_35917 := by exact prefixLift 35917
  have htrace : WordTrace (prefixWord ++ tailWord_35917) baseStart_35917 baseEnd_35917 := by
    simpa [prefixWord, tailWord_35917, baseEnd_35917] using wordTrace_append hprefix tailTrace_35917
  have hstable : (prefixWord ++ tailWord_35917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35917).length < 2 ^ (prefixWord ++ tailWord_35917).sum := by decide
  have hdescent : baseEnd_35917 < baseStart_35917 := by decide
  rcases family_descends (prefixWord ++ tailWord_35917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35934 : List Nat := [4, 4, 1, 1, 1, 1, 3, 1, 2, 1, 4]
def baseStart_35934 : Nat := 118140960795 + 35934 * 2 ^ 59
def prefixEnd_35934 : Nat := 4983230072969 + 3 ^ 40 * 35934 * 2
def baseEnd_35934 : Nat := 18451413838767641759749

theorem tailTrace_35934 : CollatzResearch.WordTrace tailWord_35934 prefixEnd_35934 18451413838767641759749 := by
  unfold tailWord_35934
  simp only [CollatzResearch.WordTrace]
  refine ⟨163827581478091235464357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 873747101216486589143237 163827581478091235464357)
  ·
    refine ⟨30717671527142106649567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 163827581478091235464357 30717671527142106649567)
    ·
      refine ⟨46076507290713159974351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30717671527142106649567 46076507290713159974351)
      ·
        refine ⟨69114760936069739961527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46076507290713159974351 69114760936069739961527)
        ·
          refine ⟨103672141404104609942291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69114760936069739961527 103672141404104609942291)
          ·
            refine ⟨155508212106156914913437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103672141404104609942291 155508212106156914913437)
            ·
              refine ⟨58315579539808843092539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 155508212106156914913437 58315579539808843092539)
              ·
                refine ⟨87473369309713264638809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58315579539808843092539 87473369309713264638809)
                ·
                  refine ⟨65605026982284948479107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 87473369309713264638809 65605026982284948479107)
                  ·
                    refine ⟨98407540473427422718661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 65605026982284948479107 98407540473427422718661)
                    ·
                      refine ⟨18451413838767641759749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 98407540473427422718661 18451413838767641759749)
                      ·
                        rfl

theorem cell23_35934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_35934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_35934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_35934 prefixEnd_35934 := by exact prefixLift 35934
  have htrace : WordTrace (prefixWord ++ tailWord_35934) baseStart_35934 baseEnd_35934 := by
    simpa [prefixWord, tailWord_35934, baseEnd_35934] using wordTrace_append hprefix tailTrace_35934
  have hstable : (prefixWord ++ tailWord_35934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35934).length < 2 ^ (prefixWord ++ tailWord_35934).sum := by decide
  have hdescent : baseEnd_35934 < baseStart_35934 := by decide
  rcases family_descends (prefixWord ++ tailWord_35934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_35960 : List Nat := [2, 1, 2, 1, 1, 1, 4, 4, 2, 3, 2]
def baseStart_35960 : Nat := 118140960795 + 35960 * 2 ^ 59
def prefixEnd_35960 : Nat := 4983230072969 + 3 ^ 40 * 35960 * 2
def baseEnd_35960 : Nat := 18464764335784540034629

theorem tailTrace_35960 : CollatzResearch.WordTrace tailWord_35960 prefixEnd_35960 18464764335784540034629 := by
  unfold tailWord_35960
  simp only [CollatzResearch.WordTrace]
  refine ⟨655784474865268162080667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 874379299820357549440889 655784474865268162080667)
  ·
    refine ⟨983676712297902243121001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 655784474865268162080667 983676712297902243121001)
    ·
      refine ⟨737757534223426682340751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 983676712297902243121001 737757534223426682340751)
      ·
        refine ⟨1106636301335140023511127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 737757534223426682340751 1106636301335140023511127)
        ·
          refine ⟨1659954452002710035266691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1106636301335140023511127 1659954452002710035266691)
          ·
            refine ⟨2489931678004065052900037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1659954452002710035266691 2489931678004065052900037)
            ·
              refine ⟨466862189625762197418757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2489931678004065052900037 466862189625762197418757)
              ·
                refine ⟨87536660554830412016017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 466862189625762197418757 87536660554830412016017)
                ·
                  refine ⟨65652495416122809012013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 87536660554830412016017 65652495416122809012013)
                  ·
                    refine ⟨24619685781046053379505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 65652495416122809012013 24619685781046053379505)
                    ·
                      refine ⟨18464764335784540034629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 24619685781046053379505 18464764335784540034629)
                      ·
                        rfl

theorem cell23_35960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 4, 2, 3, 2].length) (baseStart_35960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_35960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_35960 prefixEnd_35960 := by exact prefixLift 35960
  have htrace : WordTrace (prefixWord ++ tailWord_35960) baseStart_35960 baseEnd_35960 := by
    simpa [prefixWord, tailWord_35960, baseEnd_35960] using wordTrace_append hprefix tailTrace_35960
  have hstable : (prefixWord ++ tailWord_35960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_35960).length < 2 ^ (prefixWord ++ tailWord_35960).sum := by decide
  have hdescent : baseEnd_35960 < baseStart_35960 := by decide
  rcases family_descends (prefixWord ++ tailWord_35960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36003 : List Nat := [1, 1, 1, 4, 1, 1, 1, 6, 1, 2, 4]
def baseStart_36003 : Nat := 118140960795 + 36003 * 2 ^ 59
def prefixEnd_36003 : Nat := 4983230072969 + 3 ^ 40 * 36003 * 2
def baseEnd_36003 : Nat := 18486844003927871796931

theorem tailTrace_36003 : CollatzResearch.WordTrace tailWord_36003 prefixEnd_36003 18486844003927871796931 := by
  unfold tailWord_36003
  simp only [CollatzResearch.WordTrace]
  refine ⟨1313137288574754667976663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 875424859049836445317775 1313137288574754667976663)
  ·
    refine ⟨1969705932862132001964995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1313137288574754667976663 1969705932862132001964995)
    ·
      refine ⟨2954558899293198002947493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1969705932862132001964995 2954558899293198002947493)
      ·
        refine ⟨553979793617474625552655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2954558899293198002947493 553979793617474625552655)
        ·
          refine ⟨830969690426211938328983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 553979793617474625552655 830969690426211938328983)
          ·
            refine ⟨1246454535639317907493475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 830969690426211938328983 1246454535639317907493475)
            ·
              refine ⟨1869681803458976861240213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1246454535639317907493475 1869681803458976861240213)
              ·
                refine ⟨87641334537139540370635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1869681803458976861240213 87641334537139540370635)
                ·
                  refine ⟨131462001805709310555953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 87641334537139540370635 131462001805709310555953)
                  ·
                    refine ⟨98596501354281982916965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 131462001805709310555953 98596501354281982916965)
                    ·
                      refine ⟨18486844003927871796931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 98596501354281982916965 18486844003927871796931)
                      ·
                        rfl

theorem cell23_36003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 6, 1, 2, 4].length) (baseStart_36003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_36003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_36003 prefixEnd_36003 := by exact prefixLift 36003
  have htrace : WordTrace (prefixWord ++ tailWord_36003) baseStart_36003 baseEnd_36003 := by
    simpa [prefixWord, tailWord_36003, baseEnd_36003] using wordTrace_append hprefix tailTrace_36003
  have hstable : (prefixWord ++ tailWord_36003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36003).length < 2 ^ (prefixWord ++ tailWord_36003).sum := by decide
  have hdescent : baseEnd_36003 < baseStart_36003 := by decide
  rcases family_descends (prefixWord ++ tailWord_36003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36007 : List Nat := [1, 1, 6, 2, 1, 1, 2, 3, 1, 1, 4]
def baseStart_36007 : Nat := 118140960795 + 36007 * 2 ^ 59
def prefixEnd_36007 : Nat := 4983230072969 + 3 ^ 40 * 36007 * 2
def baseEnd_36007 : Nat := 18488897926545856146913

theorem tailTrace_36007 : CollatzResearch.WordTrace tailWord_36007 prefixEnd_36007 18488897926545856146913 := by
  unfold tailWord_36007
  simp only [CollatzResearch.WordTrace]
  refine ⟨1313283180560263351122275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 875522120373508900748183 1313283180560263351122275)
  ·
    refine ⟨1969924770840395026683413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1313283180560263351122275 1969924770840395026683413)
    ·
      refine ⟨92340223633143516875785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1969924770840395026683413 92340223633143516875785)
      ·
        refine ⟨69255167724857637656839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92340223633143516875785 69255167724857637656839)
        ·
          refine ⟨103882751587286456485259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69255167724857637656839 103882751587286456485259)
          ·
            refine ⟨155824127380929684727889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103882751587286456485259 155824127380929684727889)
            ·
              refine ⟨116868095535697263545917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 155824127380929684727889 116868095535697263545917)
              ·
                refine ⟨43825535825886473829719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 116868095535697263545917 43825535825886473829719)
                ·
                  refine ⟨65738303738829710744579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43825535825886473829719 65738303738829710744579)
                  ·
                    refine ⟨98607455608244566116869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 65738303738829710744579 98607455608244566116869)
                    ·
                      refine ⟨18488897926545856146913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 98607455608244566116869 18488897926545856146913)
                      ·
                        rfl

theorem cell23_36007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_36007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_36007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_36007 prefixEnd_36007 := by exact prefixLift 36007
  have htrace : WordTrace (prefixWord ++ tailWord_36007) baseStart_36007 baseEnd_36007 := by
    simpa [prefixWord, tailWord_36007, baseEnd_36007] using wordTrace_append hprefix tailTrace_36007
  have hstable : (prefixWord ++ tailWord_36007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36007).length < 2 ^ (prefixWord ++ tailWord_36007).sum := by decide
  have hdescent : baseEnd_36007 < baseStart_36007 := by decide
  rcases family_descends (prefixWord ++ tailWord_36007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36030 : List Nat := [4, 2, 1, 1, 3, 2, 2, 8]
def baseStart_36030 : Nat := 118140960795 + 36030 * 2 ^ 59
def prefixEnd_36030 : Nat := 4983230072969 + 3 ^ 40 * 36030 * 2
def baseEnd_36030 : Nat := 685211406725898746641

theorem tailTrace_36030 : CollatzResearch.WordTrace tailWord_36030 prefixEnd_36030 685211406725898746641 := by
  unfold tailWord_36030
  simp only [CollatzResearch.WordTrace]
  refine ⟨164265257434617284901193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 876081372984625519473029 164265257434617284901193)
  ·
    refine ⟨123198943075962963675895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 164265257434617284901193 123198943075962963675895)
    ·
      refine ⟨184798414613944445513843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123198943075962963675895 184798414613944445513843)
      ·
        refine ⟨277197621920916668270765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184798414613944445513843 277197621920916668270765)
        ·
          refine ⟨103949108220343750601537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 277197621920916668270765 103949108220343750601537)
          ·
            refine ⟨77961831165257812951153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103949108220343750601537 77961831165257812951153)
            ·
              refine ⟨58471373373943359713365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77961831165257812951153 58471373373943359713365)
              ·
                refine ⟨685211406725898746641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 58471373373943359713365 685211406725898746641)
                ·
                  rfl

theorem cell23_36030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 8].length) (baseStart_36030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_36030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_36030 prefixEnd_36030 := by exact prefixLift 36030
  have htrace : WordTrace (prefixWord ++ tailWord_36030) baseStart_36030 baseEnd_36030 := by
    simpa [prefixWord, tailWord_36030, baseEnd_36030] using wordTrace_append hprefix tailTrace_36030
  have hstable : (prefixWord ++ tailWord_36030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36030).length < 2 ^ (prefixWord ++ tailWord_36030).sum := by decide
  have hdescent : baseEnd_36030 < baseStart_36030 := by decide
  rcases family_descends (prefixWord ++ tailWord_36030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36038 : List Nat := [6, 1, 2, 2, 1, 2, 1, 2, 1, 5]
def baseStart_36038 : Nat := 118140960795 + 36038 * 2 ^ 59
def prefixEnd_36038 : Nat := 4983230072969 + 3 ^ 40 * 36038 * 2
def baseEnd_36038 : Nat := 6168271942278411619757

theorem tailTrace_36038 : CollatzResearch.WordTrace tailWord_36038 prefixEnd_36038 6168271942278411619757 := by
  unfold tailWord_36038
  simp only [CollatzResearch.WordTrace]
  refine ⟨41075432607748613921899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 876275895631970430333845 41075432607748613921899)
  ·
    refine ⟨61613148911622920882849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41075432607748613921899 61613148911622920882849)
    ·
      refine ⟨46209861683717190662137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61613148911622920882849 46209861683717190662137)
      ·
        refine ⟨34657396262787892996603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46209861683717190662137 34657396262787892996603)
        ·
          refine ⟨51986094394181839494905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34657396262787892996603 51986094394181839494905)
          ·
            refine ⟨38989570795636379621179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51986094394181839494905 38989570795636379621179)
            ·
              refine ⟨58484356193454569431769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38989570795636379621179 58484356193454569431769)
              ·
                refine ⟨43863267145090927073827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58484356193454569431769 43863267145090927073827)
                ·
                  refine ⟨65794900717636390610741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43863267145090927073827 65794900717636390610741)
                  ·
                    refine ⟨6168271942278411619757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 65794900717636390610741 6168271942278411619757)
                    ·
                      rfl

theorem cell23_36038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_36038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_36038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_36038 prefixEnd_36038 := by exact prefixLift 36038
  have htrace : WordTrace (prefixWord ++ tailWord_36038) baseStart_36038 baseEnd_36038 := by
    simpa [prefixWord, tailWord_36038, baseEnd_36038] using wordTrace_append hprefix tailTrace_36038
  have hstable : (prefixWord ++ tailWord_36038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36038).length < 2 ^ (prefixWord ++ tailWord_36038).sum := by decide
  have hdescent : baseEnd_36038 < baseStart_36038 := by decide
  rcases family_descends (prefixWord ++ tailWord_36038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36054 : List Nat := [5, 2, 1, 2, 2, 1, 1, 2, 1, 2, 4]
def baseStart_36054 : Nat := 118140960795 + 36054 * 2 ^ 59
def prefixEnd_36054 : Nat := 4983230072969 + 3 ^ 40 * 36054 * 2
def baseEnd_36054 : Nat := 18513031517307172259197

theorem tailTrace_36054 : CollatzResearch.WordTrace tailWord_36054 prefixEnd_36054 18513031517307172259197 := by
  unfold tailWord_36054
  simp only [CollatzResearch.WordTrace]
  refine ⟨82187338211874398630201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 876664940926660252055477 82187338211874398630201)
  ·
    refine ⟨61640503658905798972651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82187338211874398630201 61640503658905798972651)
    ·
      refine ⟨92460755488358698458977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61640503658905798972651 92460755488358698458977)
      ·
        refine ⟨69345566616269023844233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92460755488358698458977 69345566616269023844233)
        ·
          refine ⟨52009174962201767883175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69345566616269023844233 52009174962201767883175)
          ·
            refine ⟨78013762443302651824763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52009174962201767883175 78013762443302651824763)
            ·
              refine ⟨117020643664953977737145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78013762443302651824763 117020643664953977737145)
              ·
                refine ⟨87765482748715483302859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 117020643664953977737145 87765482748715483302859)
                ·
                  refine ⟨131648224123073224954289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 87765482748715483302859 131648224123073224954289)
                  ·
                    refine ⟨98736168092304918715717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 131648224123073224954289 98736168092304918715717)
                    ·
                      refine ⟨18513031517307172259197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 98736168092304918715717 18513031517307172259197)
                      ·
                        rfl

theorem cell23_36054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_36054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_36054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_36054 prefixEnd_36054 := by exact prefixLift 36054
  have htrace : WordTrace (prefixWord ++ tailWord_36054) baseStart_36054 baseEnd_36054 := by
    simpa [prefixWord, tailWord_36054, baseEnd_36054] using wordTrace_append hprefix tailTrace_36054
  have hstable : (prefixWord ++ tailWord_36054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36054).length < 2 ^ (prefixWord ++ tailWord_36054).sum := by decide
  have hdescent : baseEnd_36054 < baseStart_36054 := by decide
  rcases family_descends (prefixWord ++ tailWord_36054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36061 : List Nat := [1, 4, 3, 2, 2, 1, 3, 1, 1, 2, 3]
def baseStart_36061 : Nat := 118140960795 + 36061 * 2 ^ 59
def prefixEnd_36061 : Nat := 4983230072969 + 3 ^ 40 * 36061 * 2
def baseEnd_36061 : Nat := 18516625881888644871665

theorem tailTrace_36061 : CollatzResearch.WordTrace tailWord_36061 prefixEnd_36061 18516625881888644871665 := by
  unfold tailWord_36061
  simp only [CollatzResearch.WordTrace]
  refine ⟨1315252722364630573588037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 876835148243087049058691 1315252722364630573588037)
  ·
    refine ⟨246609885443368232547757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1315252722364630573588037 246609885443368232547757)
    ·
      refine ⟨92478707041263087205409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 246609885443368232547757 92478707041263087205409)
      ·
        refine ⟨69359030280947315404057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92478707041263087205409 69359030280947315404057)
        ·
          refine ⟨52019272710710486553043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69359030280947315404057 52019272710710486553043)
          ·
            refine ⟨78028909066065729829565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52019272710710486553043 78028909066065729829565)
            ·
              refine ⟨29260840899774648686087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78028909066065729829565 29260840899774648686087)
              ·
                refine ⟨43891261349661973029131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29260840899774648686087 43891261349661973029131)
                ·
                  refine ⟨65836892024492959543697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43891261349661973029131 65836892024492959543697)
                  ·
                    refine ⟨49377669018369719657773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 65836892024492959543697 49377669018369719657773)
                    ·
                      refine ⟨18516625881888644871665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 49377669018369719657773 18516625881888644871665)
                      ·
                        rfl

theorem cell23_36061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_36061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_36061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_36061 prefixEnd_36061 := by exact prefixLift 36061
  have htrace : WordTrace (prefixWord ++ tailWord_36061) baseStart_36061 baseEnd_36061 := by
    simpa [prefixWord, tailWord_36061, baseEnd_36061] using wordTrace_append hprefix tailTrace_36061
  have hstable : (prefixWord ++ tailWord_36061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36061).length < 2 ^ (prefixWord ++ tailWord_36061).sum := by decide
  have hdescent : baseEnd_36061 < baseStart_36061 := by decide
  rcases family_descends (prefixWord ++ tailWord_36061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36074 : List Nat := [3, 1, 3, 1, 1, 4, 2, 2, 2, 1, 3]
def baseStart_36074 : Nat := 118140960795 + 36074 * 2 ^ 59
def prefixEnd_36074 : Nat := 4983230072969 + 3 ^ 40 * 36074 * 2
def baseEnd_36074 : Nat := 18523301130397094009105

theorem tailTrace_36074 : CollatzResearch.WordTrace tailWord_36074 prefixEnd_36074 18523301130397094009105 := by
  unfold tailWord_36074
  simp only [CollatzResearch.WordTrace]
  refine ⟨328931717829383448452819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 877151247545022529207517 328931717829383448452819)
  ·
    refine ⟨493397576744075172679229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 328931717829383448452819 493397576744075172679229)
    ·
      refine ⟨185024091279028189754711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 493397576744075172679229 185024091279028189754711)
      ·
        refine ⟨277536136918542284632067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185024091279028189754711 277536136918542284632067)
        ·
          refine ⟨416304205377813426948101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 277536136918542284632067 416304205377813426948101)
          ·
            refine ⟨78057038508340017552769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 416304205377813426948101 78057038508340017552769)
            ·
              refine ⟨58542778881255013164577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78057038508340017552769 58542778881255013164577)
              ·
                refine ⟨43907084160941259873433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58542778881255013164577 43907084160941259873433)
                ·
                  refine ⟨32930313120705944905075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43907084160941259873433 32930313120705944905075)
                  ·
                    refine ⟨49395469681058917357613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32930313120705944905075 49395469681058917357613)
                    ·
                      refine ⟨18523301130397094009105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 49395469681058917357613 18523301130397094009105)
                      ·
                        rfl

theorem cell23_36074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 2, 2, 1, 3].length) (baseStart_36074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_36074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_36074 prefixEnd_36074 := by exact prefixLift 36074
  have htrace : WordTrace (prefixWord ++ tailWord_36074) baseStart_36074 baseEnd_36074 := by
    simpa [prefixWord, tailWord_36074, baseEnd_36074] using wordTrace_append hprefix tailTrace_36074
  have hstable : (prefixWord ++ tailWord_36074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36074).length < 2 ^ (prefixWord ++ tailWord_36074).sum := by decide
  have hdescent : baseEnd_36074 < baseStart_36074 := by decide
  rcases family_descends (prefixWord ++ tailWord_36074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36097 : List Nat := [1, 2, 4, 1, 1, 3, 1, 3, 1, 4, 2]
def baseStart_36097 : Nat := 118140960795 + 36097 * 2 ^ 59
def prefixEnd_36097 : Nat := 4983230072969 + 3 ^ 40 * 36097 * 2
def baseEnd_36097 : Nat := 18535111185450504021499

theorem tailTrace_36097 : CollatzResearch.WordTrace tailWord_36097 prefixEnd_36097 18535111185450504021499 := by
  unfold tailWord_36097
  simp only [CollatzResearch.WordTrace]
  refine ⟨1316565750234208721898545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 877710500156139147932363 1316565750234208721898545)
  ·
    refine ⟨987424312675656541423909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1316565750234208721898545 987424312675656541423909)
    ·
      refine ⟨185142058626685601516983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 987424312675656541423909 185142058626685601516983)
      ·
        refine ⟨277713087940028402275475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185142058626685601516983 277713087940028402275475)
        ·
          refine ⟨416569631910042603413213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 277713087940028402275475 416569631910042603413213)
          ·
            refine ⟨156213611966265976279955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 416569631910042603413213 156213611966265976279955)
            ·
              refine ⟨234320417949398964419933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156213611966265976279955 234320417949398964419933)
              ·
                refine ⟨87870156731024611657475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 234320417949398964419933 87870156731024611657475)
                ·
                  refine ⟨131805235096536917486213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 87870156731024611657475 131805235096536917486213)
                  ·
                    refine ⟨24713481580600672028665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 131805235096536917486213 24713481580600672028665)
                    ·
                      refine ⟨18535111185450504021499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 24713481580600672028665 18535111185450504021499)
                      ·
                        rfl

theorem cell23_36097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 3, 1, 4, 2].length) (baseStart_36097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_36097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_36097 prefixEnd_36097 := by exact prefixLift 36097
  have htrace : WordTrace (prefixWord ++ tailWord_36097) baseStart_36097 baseEnd_36097 := by
    simpa [prefixWord, tailWord_36097, baseEnd_36097] using wordTrace_append hprefix tailTrace_36097
  have hstable : (prefixWord ++ tailWord_36097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36097).length < 2 ^ (prefixWord ++ tailWord_36097).sum := by decide
  have hdescent : baseEnd_36097 < baseStart_36097 := by decide
  rcases family_descends (prefixWord ++ tailWord_36097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36131 : List Nat := [1, 1, 1, 4, 2, 5, 1, 2, 2, 2, 2]
def baseStart_36131 : Nat := 118140960795 + 36131 * 2 ^ 59
def prefixEnd_36131 : Nat := 4983230072969 + 3 ^ 40 * 36131 * 2
def baseEnd_36131 : Nat := 18552569527703370996343

theorem tailTrace_36131 : CollatzResearch.WordTrace tailWord_36131 prefixEnd_36131 18552569527703370996343 := by
  unfold tailWord_36131
  simp only [CollatzResearch.WordTrace]
  refine ⟨1317805832111032528636247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 878537221407355019090831 1317805832111032528636247)
  ·
    refine ⟨1976708748166548792954371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1317805832111032528636247 1976708748166548792954371)
    ·
      refine ⟨2965063122249823189431557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1976708748166548792954371 2965063122249823189431557)
      ·
        refine ⟨555949335421841848018417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2965063122249823189431557 555949335421841848018417)
        ·
          refine ⟨416962001566381386013813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 555949335421841848018417 416962001566381386013813)
          ·
            refine ⟨39090187646848254938795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 416962001566381386013813 39090187646848254938795)
            ·
              refine ⟨58635281470272382408193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39090187646848254938795 58635281470272382408193)
              ·
                refine ⟨43976461102704286806145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58635281470272382408193 43976461102704286806145)
                ·
                  refine ⟨32982345827028215104609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43976461102704286806145 32982345827028215104609)
                  ·
                    refine ⟨24736759370271161328457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32982345827028215104609 24736759370271161328457)
                    ·
                      refine ⟨18552569527703370996343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 24736759370271161328457 18552569527703370996343)
                      ·
                        rfl

theorem cell23_36131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 2, 2, 2, 2].length) (baseStart_36131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_36131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_36131 prefixEnd_36131 := by exact prefixLift 36131
  have htrace : WordTrace (prefixWord ++ tailWord_36131) baseStart_36131 baseEnd_36131 := by
    simpa [prefixWord, tailWord_36131, baseEnd_36131] using wordTrace_append hprefix tailTrace_36131
  have hstable : (prefixWord ++ tailWord_36131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36131).length < 2 ^ (prefixWord ++ tailWord_36131).sum := by decide
  have hdescent : baseEnd_36131 < baseStart_36131 := by decide
  rcases family_descends (prefixWord ++ tailWord_36131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36143 : List Nat := [1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 7]
def baseStart_36143 : Nat := 118140960795 + 36143 * 2 ^ 59
def prefixEnd_36143 : Nat := 4983230072969 + 3 ^ 40 * 36143 * 2
def baseEnd_36143 : Nat := 18558731295557324046287

theorem tailTrace_36143 : CollatzResearch.WordTrace tailWord_36143 prefixEnd_36143 18558731295557324046287 := by
  unfold tailWord_36143
  simp only [CollatzResearch.WordTrace]
  refine ⟨1318243508067558578073083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 878829005378372385382055 1318243508067558578073083)
  ·
    refine ⟨1977365262101337867109625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1318243508067558578073083 1977365262101337867109625)
    ·
      refine ⟨1483023946576003400332219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1977365262101337867109625 1483023946576003400332219)
      ·
        refine ⟨2224535919864005100498329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1483023946576003400332219 2224535919864005100498329)
        ·
          refine ⟨1668401939898003825373747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2224535919864005100498329 1668401939898003825373747)
          ·
            refine ⟨2502602909847005738060621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1668401939898003825373747 2502602909847005738060621)
            ·
              refine ⟨938476091192627151772733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2502602909847005738060621 938476091192627151772733)
              ·
                refine ⟨351928534197235181914775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 938476091192627151772733 351928534197235181914775)
                ·
                  refine ⟨527892801295852772872163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 351928534197235181914775 527892801295852772872163)
                  ·
                    refine ⟨791839201943779159308245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 527892801295852772872163 791839201943779159308245)
                    ·
                      refine ⟨18558731295557324046287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 791839201943779159308245 18558731295557324046287)
                      ·
                        rfl

theorem cell23_36143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 7].length) (baseStart_36143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_36143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_36143 prefixEnd_36143 := by exact prefixLift 36143
  have htrace : WordTrace (prefixWord ++ tailWord_36143) baseStart_36143 baseEnd_36143 := by
    simpa [prefixWord, tailWord_36143, baseEnd_36143] using wordTrace_append hprefix tailTrace_36143
  have hstable : (prefixWord ++ tailWord_36143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36143).length < 2 ^ (prefixWord ++ tailWord_36143).sum := by decide
  have hdescent : baseEnd_36143 < baseStart_36143 := by decide
  rcases family_descends (prefixWord ++ tailWord_36143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36148 : List Nat := [2, 5, 1, 1, 1, 1, 5, 1, 2, 2, 2]
def baseStart_36148 : Nat := 118140960795 + 36148 * 2 ^ 59
def prefixEnd_36148 : Nat := 4983230072969 + 3 ^ 40 * 36148 * 2
def baseEnd_36148 : Nat := 18561298698829804483765

theorem tailTrace_36148 : CollatzResearch.WordTrace tailWord_36148 prefixEnd_36148 18561298698829804483765 := by
  unfold tailWord_36148
  simp only [CollatzResearch.WordTrace]
  refine ⟨659212936524722216002549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 878950582032962954670065 659212936524722216002549)
  ·
    refine ⟨61801212799192707750239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 659212936524722216002549 61801212799192707750239)
    ·
      refine ⟨92701819198789061625359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61801212799192707750239 92701819198789061625359)
      ·
        refine ⟨139052728798183592438039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92701819198789061625359 139052728798183592438039)
        ·
          refine ⟨208579093197275388657059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139052728798183592438039 208579093197275388657059)
          ·
            refine ⟨312868639795913082985589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208579093197275388657059 312868639795913082985589)
            ·
              refine ⟨29331434980866851529899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 312868639795913082985589 29331434980866851529899)
              ·
                refine ⟨43997152471300277294849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29331434980866851529899 43997152471300277294849)
                ·
                  refine ⟨32997864353475207971137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43997152471300277294849 32997864353475207971137)
                  ·
                    refine ⟨24748398265106405978353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32997864353475207971137 24748398265106405978353)
                    ·
                      refine ⟨18561298698829804483765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 24748398265106405978353 18561298698829804483765)
                      ·
                        rfl

theorem cell23_36148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 5, 1, 2, 2, 2].length) (baseStart_36148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_36148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_36148 prefixEnd_36148 := by exact prefixLift 36148
  have htrace : WordTrace (prefixWord ++ tailWord_36148) baseStart_36148 baseEnd_36148 := by
    simpa [prefixWord, tailWord_36148, baseEnd_36148] using wordTrace_append hprefix tailTrace_36148
  have hstable : (prefixWord ++ tailWord_36148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36148).length < 2 ^ (prefixWord ++ tailWord_36148).sum := by decide
  have hdescent : baseEnd_36148 < baseStart_36148 := by decide
  rcases family_descends (prefixWord ++ tailWord_36148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36163 : List Nat := [1, 1, 1, 3, 1, 3, 1, 1, 1, 10]
def baseStart_36163 : Nat := 118140960795 + 36163 * 2 ^ 59
def prefixEnd_36163 : Nat := 4983230072969 + 3 ^ 40 * 36163 * 2
def baseEnd_36163 : Nat := 6189666969549081932065

theorem tailTrace_36163 : CollatzResearch.WordTrace tailWord_36163 prefixEnd_36163 6189666969549081932065 := by
  unfold tailWord_36163
  simp only [CollatzResearch.WordTrace]
  refine ⟨1318972967995101993801143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 879315311996734662534095 1318972967995101993801143)
  ·
    refine ⟨1978459451992652990701715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1318972967995101993801143 1978459451992652990701715)
    ·
      refine ⟨2967689177988979486052573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1978459451992652990701715 2967689177988979486052573)
      ·
        refine ⟨1112883441745867307269715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2967689177988979486052573 1112883441745867307269715)
        ·
          refine ⟨1669325162618800960904573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1112883441745867307269715 1669325162618800960904573)
          ·
            refine ⟨625996935982050360339215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1669325162618800960904573 625996935982050360339215)
            ·
              refine ⟨938995403973075540508823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 625996935982050360339215 938995403973075540508823)
              ·
                refine ⟨1408493105959613310763235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 938995403973075540508823 1408493105959613310763235)
                ·
                  refine ⟨2112739658939419966144853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1408493105959613310763235 2112739658939419966144853)
                  ·
                    refine ⟨6189666969549081932065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 2112739658939419966144853 6189666969549081932065)
                    ·
                      rfl

theorem cell23_36163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 10].length) (baseStart_36163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_36163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_36163 prefixEnd_36163 := by exact prefixLift 36163
  have htrace : WordTrace (prefixWord ++ tailWord_36163) baseStart_36163 baseEnd_36163 := by
    simpa [prefixWord, tailWord_36163, baseEnd_36163] using wordTrace_append hprefix tailTrace_36163
  have hstable : (prefixWord ++ tailWord_36163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36163).length < 2 ^ (prefixWord ++ tailWord_36163).sum := by decide
  have hdescent : baseEnd_36163 < baseStart_36163 := by decide
  rcases family_descends (prefixWord ++ tailWord_36163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36170 : List Nat := [3, 1, 2, 1, 1, 1, 1, 2, 6, 1, 4]
def baseStart_36170 : Nat := 118140960795 + 36170 * 2 ^ 59
def prefixEnd_36170 : Nat := 4983230072969 + 3 ^ 40 * 36170 * 2
def baseEnd_36170 : Nat := 18572595273228718408663

theorem tailTrace_36170 : CollatzResearch.WordTrace tailWord_36170 prefixEnd_36170 18572595273228718408663 := by
  unfold tailWord_36170
  simp only [CollatzResearch.WordTrace]
  refine ⟨329807069742435547326491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 879485519313161459537309 329807069742435547326491)
  ·
    refine ⟨494710604613653320989737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 329807069742435547326491 494710604613653320989737)
    ·
      refine ⟨371032953460239990742303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 494710604613653320989737 371032953460239990742303)
      ·
        refine ⟨556549430190359986113455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 371032953460239990742303 556549430190359986113455)
        ·
          refine ⟨834824145285539979170183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 556549430190359986113455 834824145285539979170183)
          ·
            refine ⟨1252236217928309968755275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 834824145285539979170183 1252236217928309968755275)
            ·
              refine ⟨1878354326892464953132913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1252236217928309968755275 1878354326892464953132913)
              ·
                refine ⟨1408765745169348714849685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1878354326892464953132913 1408765745169348714849685)
                ·
                  refine ⟨66035894304813221008579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1408765745169348714849685 66035894304813221008579)
                  ·
                    refine ⟨99053841457219831512869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 66035894304813221008579 99053841457219831512869)
                    ·
                      refine ⟨18572595273228718408663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 99053841457219831512869 18572595273228718408663)
                      ·
                        rfl

theorem cell23_36170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 6, 1, 4].length) (baseStart_36170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_36170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_36170 prefixEnd_36170 := by exact prefixLift 36170
  have htrace : WordTrace (prefixWord ++ tailWord_36170) baseStart_36170 baseEnd_36170 := by
    simpa [prefixWord, tailWord_36170, baseEnd_36170] using wordTrace_append hprefix tailTrace_36170
  have hstable : (prefixWord ++ tailWord_36170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36170).length < 2 ^ (prefixWord ++ tailWord_36170).sum := by decide
  have hdescent : baseEnd_36170 < baseStart_36170 := by decide
  rcases family_descends (prefixWord ++ tailWord_36170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36244 : List Nat := [2, 4, 2, 1, 2, 2, 2, 2, 6]
def baseStart_36244 : Nat := 118140960795 + 36244 * 2 ^ 59
def prefixEnd_36244 : Nat := 4983230072969 + 3 ^ 40 * 36244 * 2
def baseEnd_36244 : Nat := 2067843649073492098147

theorem tailTrace_36244 : CollatzResearch.WordTrace tailWord_36244 prefixEnd_36244 2067843649073492098147 := by
  unfold tailWord_36244
  simp only [CollatzResearch.WordTrace]
  refine ⟨660963640350826413749893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 881284853801101884999857 660963640350826413749893)
  ·
    refine ⟨123930682565779952578105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 660963640350826413749893 123930682565779952578105)
    ·
      refine ⟨92948011924334964433579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123930682565779952578105 92948011924334964433579)
      ·
        refine ⟨139422017886502446650369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92948011924334964433579 139422017886502446650369)
        ·
          refine ⟨104566513414876834987777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139422017886502446650369 104566513414876834987777)
          ·
            refine ⟨78424885061157626240833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104566513414876834987777 78424885061157626240833)
            ·
              refine ⟨58818663795868219680625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78424885061157626240833 58818663795868219680625)
              ·
                refine ⟨44113997846901164760469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58818663795868219680625 44113997846901164760469)
                ·
                  refine ⟨2067843649073492098147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 44113997846901164760469 2067843649073492098147)
                  ·
                    rfl

theorem cell23_36244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 2, 6].length) (baseStart_36244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_36244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_36244 prefixEnd_36244 := by exact prefixLift 36244
  have htrace : WordTrace (prefixWord ++ tailWord_36244) baseStart_36244 baseEnd_36244 := by
    simpa [prefixWord, tailWord_36244, baseEnd_36244] using wordTrace_append hprefix tailTrace_36244
  have hstable : (prefixWord ++ tailWord_36244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36244).length < 2 ^ (prefixWord ++ tailWord_36244).sum := by decide
  have hdescent : baseEnd_36244 < baseStart_36244 := by decide
  rcases family_descends (prefixWord ++ tailWord_36244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36247 : List Nat := [1, 1, 3, 3, 1, 1, 1, 2, 3, 5, 2]
def baseStart_36247 : Nat := 118140960795 + 36247 * 2 ^ 59
def prefixEnd_36247 : Nat := 4983230072969 + 3 ^ 40 * 36247 * 2
def baseEnd_36247 : Nat := 18612133283624917145809

theorem tailTrace_36247 : CollatzResearch.WordTrace tailWord_36247 prefixEnd_36247 18612133283624917145809 := by
  unfold tailWord_36247
  simp only [CollatzResearch.WordTrace]
  refine ⟨1322036699690784339858995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 881357799793856226572663 1322036699690784339858995)
  ·
    refine ⟨1983055049536176509788493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1322036699690784339858995 1983055049536176509788493)
    ·
      refine ⟨743645643576066191170685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1983055049536176509788493 743645643576066191170685)
      ·
        refine ⟨278867116341024821689007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 743645643576066191170685 278867116341024821689007)
        ·
          refine ⟨418300674511537232533511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 278867116341024821689007 418300674511537232533511)
          ·
            refine ⟨627451011767305848800267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 418300674511537232533511 627451011767305848800267)
            ·
              refine ⟨941176517650958773200401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 627451011767305848800267 941176517650958773200401)
              ·
                refine ⟨705882388238219079900301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 941176517650958773200401 705882388238219079900301)
                ·
                  refine ⟨264705895589332154962613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 705882388238219079900301 264705895589332154962613)
                  ·
                    refine ⟨24816177711499889527745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 264705895589332154962613 24816177711499889527745)
                    ·
                      refine ⟨18612133283624917145809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 24816177711499889527745 18612133283624917145809)
                      ·
                        rfl

theorem cell23_36247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 3, 5, 2].length) (baseStart_36247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_36247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_36247 prefixEnd_36247 := by exact prefixLift 36247
  have htrace : WordTrace (prefixWord ++ tailWord_36247) baseStart_36247 baseEnd_36247 := by
    simpa [prefixWord, tailWord_36247, baseEnd_36247] using wordTrace_append hprefix tailTrace_36247
  have hstable : (prefixWord ++ tailWord_36247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36247).length < 2 ^ (prefixWord ++ tailWord_36247).sum := by decide
  have hdescent : baseEnd_36247 < baseStart_36247 := by decide
  rcases family_descends (prefixWord ++ tailWord_36247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36320 : List Nat := [2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 6]
def baseStart_36320 : Nat := 118140960795 + 36320 * 2 ^ 59
def prefixEnd_36320 : Nat := 4983230072969 + 3 ^ 40 * 36320 * 2
def baseEnd_36320 : Nat := 18649617371403131532973

theorem tailTrace_36320 : CollatzResearch.WordTrace tailWord_36320 prefixEnd_36320 18649617371403131532973 := by
  unfold tailWord_36320
  simp only [CollatzResearch.WordTrace]
  refine ⟨662349614213158903633207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 883132818950878538177609 662349614213158903633207)
  ·
    refine ⟨993524421319738355449811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 662349614213158903633207 993524421319738355449811)
    ·
      refine ⟨1490286631979607533174717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 993524421319738355449811 1490286631979607533174717)
      ·
        refine ⟨558857486992352824940519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1490286631979607533174717 558857486992352824940519)
        ·
          refine ⟨838286230488529237410779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 558857486992352824940519 838286230488529237410779)
          ·
            refine ⟨1257429345732793856116169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 838286230488529237410779 1257429345732793856116169)
            ·
              refine ⟨943072009299595392087127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1257429345732793856116169 943072009299595392087127)
              ·
                refine ⟨1414608013949393088130691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 943072009299595392087127 1414608013949393088130691)
                ·
                  refine ⟨2121912020924089632196037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1414608013949393088130691 2121912020924089632196037)
                  ·
                    refine ⟨397858503923266806036757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2121912020924089632196037 397858503923266806036757)
                    ·
                      refine ⟨18649617371403131532973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 397858503923266806036757 18649617371403131532973)
                      ·
                        rfl

theorem cell23_36320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 6].length) (baseStart_36320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_36320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_36320 prefixEnd_36320 := by exact prefixLift 36320
  have htrace : WordTrace (prefixWord ++ tailWord_36320) baseStart_36320 baseEnd_36320 := by
    simpa [prefixWord, tailWord_36320, baseEnd_36320] using wordTrace_append hprefix tailTrace_36320
  have hstable : (prefixWord ++ tailWord_36320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36320).length < 2 ^ (prefixWord ++ tailWord_36320).sum := by decide
  have hdescent : baseEnd_36320 < baseStart_36320 := by decide
  rcases family_descends (prefixWord ++ tailWord_36320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36321 : List Nat := [1, 2, 3, 1, 2, 4, 3, 1, 2, 4]
def baseStart_36321 : Nat := 118140960795 + 36321 * 2 ^ 59
def prefixEnd_36321 : Nat := 4983230072969 + 3 ^ 40 * 36321 * 2
def baseEnd_36321 : Nat := 6216710284019209206823

theorem tailTrace_36321 : CollatzResearch.WordTrace tailWord_36321 prefixEnd_36321 6216710284019209206823 := by
  unfold tailWord_36321
  simp only [CollatzResearch.WordTrace]
  refine ⟨1324735701422694978052817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 883157134281796652035211 1324735701422694978052817)
  ·
    refine ⟨993551776067021233539613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1324735701422694978052817 993551776067021233539613)
    ·
      refine ⟨372581916025132962577355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 993551776067021233539613 372581916025132962577355)
      ·
        refine ⟨558872874037699443866033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 372581916025132962577355 558872874037699443866033)
        ·
          refine ⟨419154655528274582899525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 558872874037699443866033 419154655528274582899525)
          ·
            refine ⟨78591497911551484293661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 419154655528274582899525 78591497911551484293661)
            ·
              refine ⟨29471811716831806610123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78591497911551484293661 29471811716831806610123)
              ·
                refine ⟨44207717575247709915185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29471811716831806610123 44207717575247709915185)
                ·
                  refine ⟨33155788181435782436389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44207717575247709915185 33155788181435782436389)
                  ·
                    refine ⟨6216710284019209206823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33155788181435782436389 6216710284019209206823)
                    ·
                      rfl

theorem cell23_36321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 3, 1, 2, 4].length) (baseStart_36321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_36321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_36321 prefixEnd_36321 := by exact prefixLift 36321
  have htrace : WordTrace (prefixWord ++ tailWord_36321) baseStart_36321 baseEnd_36321 := by
    simpa [prefixWord, tailWord_36321, baseEnd_36321] using wordTrace_append hprefix tailTrace_36321
  have hstable : (prefixWord ++ tailWord_36321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36321).length < 2 ^ (prefixWord ++ tailWord_36321).sum := by decide
  have hdescent : baseEnd_36321 < baseStart_36321 := by decide
  rcases family_descends (prefixWord ++ tailWord_36321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36344 : List Nat := [2, 1, 2, 1, 1, 5, 1, 2, 4, 1, 3]
def baseStart_36344 : Nat := 118140960795 + 36344 * 2 ^ 59
def prefixEnd_36344 : Nat := 4983230072969 + 3 ^ 40 * 36344 * 2
def baseEnd_36344 : Nat := 18661940907111037632863

theorem tailTrace_36344 : CollatzResearch.WordTrace tailWord_36344 prefixEnd_36344 18661940907111037632863 := by
  unfold tailWord_36344
  simp only [CollatzResearch.WordTrace]
  refine ⟨662787290169684953070043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 883716386892913270760057 662787290169684953070043)
  ·
    refine ⟨994180935254527429605065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 662787290169684953070043 994180935254527429605065)
    ·
      refine ⟨745635701440895572203799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 994180935254527429605065 745635701440895572203799)
      ·
        refine ⟨1118453552161343358305699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 745635701440895572203799 1118453552161343358305699)
        ·
          refine ⟨1677680328242015037458549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1118453552161343358305699 1677680328242015037458549)
          ·
            refine ⟨157282530772688909761739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1677680328242015037458549 157282530772688909761739)
            ·
              refine ⟨235923796159033364642609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157282530772688909761739 235923796159033364642609)
              ·
                refine ⟨176942847119275023481957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 235923796159033364642609 176942847119275023481957)
                ·
                  refine ⟨33176783834864066902867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 176942847119275023481957 33176783834864066902867)
                  ·
                    refine ⟨49765175752296100354301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33176783834864066902867 49765175752296100354301)
                    ·
                      refine ⟨18661940907111037632863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 49765175752296100354301 18661940907111037632863)
                      ·
                        rfl

theorem cell23_36344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 2, 4, 1, 3].length) (baseStart_36344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_36344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_36344 prefixEnd_36344 := by exact prefixLift 36344
  have htrace : WordTrace (prefixWord ++ tailWord_36344) baseStart_36344 baseEnd_36344 := by
    simpa [prefixWord, tailWord_36344, baseEnd_36344] using wordTrace_append hprefix tailTrace_36344
  have hstable : (prefixWord ++ tailWord_36344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36344).length < 2 ^ (prefixWord ++ tailWord_36344).sum := by decide
  have hdescent : baseEnd_36344 < baseStart_36344 := by decide
  rcases family_descends (prefixWord ++ tailWord_36344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36372 : List Nat := [2, 4, 3, 1, 3, 1, 2, 1, 2, 4]
def baseStart_36372 : Nat := 118140960795 + 36372 * 2 ^ 59
def prefixEnd_36372 : Nat := 4983230072969 + 3 ^ 40 * 36372 * 2
def baseEnd_36372 : Nat := 6225439455145642694245

theorem tailTrace_36372 : CollatzResearch.WordTrace tailWord_36372 prefixEnd_36372 6225439455145642694245 := by
  unfold tailWord_36372
  simp only [CollatzResearch.WordTrace]
  refine ⟨663297912118965344079685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 884397216158620458772913 663297912118965344079685)
  ·
    refine ⟨124368358522306002014941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 663297912118965344079685 124368358522306002014941)
    ·
      refine ⟨46638134445864750755603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124368358522306002014941 46638134445864750755603)
      ·
        refine ⟨69957201668797126133405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46638134445864750755603 69957201668797126133405)
        ·
          refine ⟨26233950625798922300027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69957201668797126133405 26233950625798922300027)
          ·
            refine ⟨39350925938698383450041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26233950625798922300027 39350925938698383450041)
            ·
              refine ⟨29513194454023787587531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39350925938698383450041 29513194454023787587531)
              ·
                refine ⟨44269791681035681381297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29513194454023787587531 44269791681035681381297)
                ·
                  refine ⟨33202343760776761035973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44269791681035681381297 33202343760776761035973)
                  ·
                    refine ⟨6225439455145642694245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33202343760776761035973 6225439455145642694245)
                    ·
                      rfl

theorem cell23_36372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_36372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_36372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_36372 prefixEnd_36372 := by exact prefixLift 36372
  have htrace : WordTrace (prefixWord ++ tailWord_36372) baseStart_36372 baseEnd_36372 := by
    simpa [prefixWord, tailWord_36372, baseEnd_36372] using wordTrace_append hprefix tailTrace_36372
  have hstable : (prefixWord ++ tailWord_36372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36372).length < 2 ^ (prefixWord ++ tailWord_36372).sum := by decide
  have hdescent : baseEnd_36372 < baseStart_36372 := by decide
  rcases family_descends (prefixWord ++ tailWord_36372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36434 : List Nat := [3, 2, 2, 1, 2, 2, 1, 1, 1, 5, 3]
def baseStart_36434 : Nat := 118140960795 + 36434 * 2 ^ 59
def prefixEnd_36434 : Nat := 4983230072969 + 3 ^ 40 * 36434 * 2
def baseEnd_36434 : Nat := 18708154166015685507449

theorem tailTrace_36434 : CollatzResearch.WordTrace tailWord_36434 prefixEnd_36434 18708154166015685507449 := by
  unfold tailWord_36434
  simp only [CollatzResearch.WordTrace]
  refine ⟨332214287503328819229089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 885904766675543517944237 332214287503328819229089)
  ·
    refine ⟨249160715627496614421817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 332214287503328819229089 249160715627496614421817)
    ·
      refine ⟨186870536720622460816363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 249160715627496614421817 186870536720622460816363)
      ·
        refine ⟨280305805080933691224545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186870536720622460816363 280305805080933691224545)
        ·
          refine ⟨210229353810700268418409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 280305805080933691224545 210229353810700268418409)
          ·
            refine ⟨157672015358025201313807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 210229353810700268418409 157672015358025201313807)
            ·
              refine ⟨236508023037037801970711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157672015358025201313807 236508023037037801970711)
              ·
                refine ⟨354762034555556702956067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 236508023037037801970711 354762034555556702956067)
                ·
                  refine ⟨532143051833335054434101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 354762034555556702956067 532143051833335054434101)
                  ·
                    refine ⟨49888411109375161353197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 532143051833335054434101 49888411109375161353197)
                    ·
                      refine ⟨18708154166015685507449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 49888411109375161353197 18708154166015685507449)
                      ·
                        rfl

theorem cell23_36434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 1, 5, 3].length) (baseStart_36434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_36434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_36434 prefixEnd_36434 := by exact prefixLift 36434
  have htrace : WordTrace (prefixWord ++ tailWord_36434) baseStart_36434 baseEnd_36434 := by
    simpa [prefixWord, tailWord_36434, baseEnd_36434] using wordTrace_append hprefix tailTrace_36434
  have hstable : (prefixWord ++ tailWord_36434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36434).length < 2 ^ (prefixWord ++ tailWord_36434).sum := by decide
  have hdescent : baseEnd_36434 < baseStart_36434 := by decide
  rcases family_descends (prefixWord ++ tailWord_36434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36437 : List Nat := [1, 3, 2, 2, 1, 1, 1, 4, 1, 7]
def baseStart_36437 : Nat := 118140960795 + 36437 * 2 ^ 59
def prefixEnd_36437 : Nat := 4983230072969 + 3 ^ 40 * 36437 * 2
def baseEnd_36437 : Nat := 6236564869326391256645

theorem tailTrace_36437 : CollatzResearch.WordTrace tailWord_36437 prefixEnd_36437 6236564869326391256645 := by
  unfold tailWord_36437
  simp only [CollatzResearch.WordTrace]
  refine ⟨1328966569002446789275565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 885977712668297859517043 1328966569002446789275565)
  ·
    refine ⟨498362463375917545978337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1328966569002446789275565 498362463375917545978337)
    ·
      refine ⟨373771847531938159483753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 498362463375917545978337 373771847531938159483753)
      ·
        refine ⟨280328885648953619612815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 373771847531938159483753 280328885648953619612815)
        ·
          refine ⟨420493328473430429419223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 280328885648953619612815 420493328473430429419223)
          ·
            refine ⟨630739992710145644128835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 420493328473430429419223 630739992710145644128835)
            ·
              refine ⟨946109989065218466193253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 630739992710145644128835 946109989065218466193253)
              ·
                refine ⟨177395622949728462411235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 946109989065218466193253 177395622949728462411235)
                ·
                  refine ⟨266093434424592693616853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 177395622949728462411235 266093434424592693616853)
                  ·
                    refine ⟨6236564869326391256645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 266093434424592693616853 6236564869326391256645)
                    ·
                      rfl

theorem cell23_36437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 4, 1, 7].length) (baseStart_36437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_36437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_36437 prefixEnd_36437 := by exact prefixLift 36437
  have htrace : WordTrace (prefixWord ++ tailWord_36437) baseStart_36437 baseEnd_36437 := by
    simpa [prefixWord, tailWord_36437, baseEnd_36437] using wordTrace_append hprefix tailTrace_36437
  have hstable : (prefixWord ++ tailWord_36437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36437).length < 2 ^ (prefixWord ++ tailWord_36437).sum := by decide
  have hdescent : baseEnd_36437 < baseStart_36437 := by decide
  rcases family_descends (prefixWord ++ tailWord_36437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36535 : List Nat := [1, 1, 3, 1, 5, 2, 3, 2, 1, 4]
def baseStart_36535 : Nat := 118140960795 + 36535 * 2 ^ 59
def prefixEnd_36535 : Nat := 4983230072969 + 3 ^ 40 * 36535 * 2
def baseEnd_36535 : Nat := 6253338570706596781495

theorem tailTrace_36535 : CollatzResearch.WordTrace tailWord_36535 prefixEnd_36535 6253338570706596781495 := by
  unfold tailWord_36535
  simp only [CollatzResearch.WordTrace]
  refine ⟨1332540922647409526343059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 888360615098273017562039 1332540922647409526343059)
  ·
    refine ⟨1998811383971114289514589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1332540922647409526343059 1998811383971114289514589)
    ·
      refine ⟨749554268989167858567971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1998811383971114289514589 749554268989167858567971)
      ·
        refine ⟨1124331403483751787851957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 749554268989167858567971 1124331403483751787851957)
        ·
          refine ⟨105406069076601730111121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1124331403483751787851957 105406069076601730111121)
          ·
            refine ⟨79054551807451297583341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105406069076601730111121 79054551807451297583341)
            ·
              refine ⟨29645456927794236593753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79054551807451297583341 29645456927794236593753)
              ·
                refine ⟨22234092695845677445315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29645456927794236593753 22234092695845677445315)
                ·
                  refine ⟨33351139043768516167973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22234092695845677445315 33351139043768516167973)
                  ·
                    refine ⟨6253338570706596781495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33351139043768516167973 6253338570706596781495)
                    ·
                      rfl

theorem cell23_36535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 3, 2, 1, 4].length) (baseStart_36535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_36535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_36535 prefixEnd_36535 := by exact prefixLift 36535
  have htrace : WordTrace (prefixWord ++ tailWord_36535) baseStart_36535 baseEnd_36535 := by
    simpa [prefixWord, tailWord_36535, baseEnd_36535] using wordTrace_append hprefix tailTrace_36535
  have hstable : (prefixWord ++ tailWord_36535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36535).length < 2 ^ (prefixWord ++ tailWord_36535).sum := by decide
  have hdescent : baseEnd_36535 < baseStart_36535 := by decide
  rcases family_descends (prefixWord ++ tailWord_36535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36544 : List Nat := [2, 1, 1, 2, 4, 1, 2, 2, 3, 5]
def baseStart_36544 : Nat := 118140960795 + 36544 * 2 ^ 59
def prefixEnd_36544 : Nat := 4983230072969 + 3 ^ 40 * 36544 * 2
def baseEnd_36544 : Nat := 6254879012670085043981

theorem tailTrace_36544 : CollatzResearch.WordTrace tailWord_36544 prefixEnd_36544 6254879012670085043981 := by
  unfold tailWord_36544
  simp only [CollatzResearch.WordTrace]
  refine ⟨666434589807402031710343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 888579453076536042280457 666434589807402031710343)
  ·
    refine ⟨999651884711103047565515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 666434589807402031710343 999651884711103047565515)
    ·
      refine ⟨1499477827066654571348273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 999651884711103047565515 1499477827066654571348273)
      ·
        refine ⟨1124608370299990928511205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1499477827066654571348273 1124608370299990928511205)
        ·
          refine ⟨210864069431248299095851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1124608370299990928511205 210864069431248299095851)
          ·
            refine ⟨316296104146872448643777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 210864069431248299095851 316296104146872448643777)
            ·
              refine ⟨237222078110154336482833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 316296104146872448643777 237222078110154336482833)
              ·
                refine ⟨177916558582615752362125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 237222078110154336482833 177916558582615752362125)
                ·
                  refine ⟨66718709468480907135797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 177916558582615752362125 66718709468480907135797)
                  ·
                    refine ⟨6254879012670085043981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 66718709468480907135797 6254879012670085043981)
                    ·
                      rfl

theorem cell23_36544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 2, 3, 5].length) (baseStart_36544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_36544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_36544 prefixEnd_36544 := by exact prefixLift 36544
  have htrace : WordTrace (prefixWord ++ tailWord_36544) baseStart_36544 baseEnd_36544 := by
    simpa [prefixWord, tailWord_36544, baseEnd_36544] using wordTrace_append hprefix tailTrace_36544
  have hstable : (prefixWord ++ tailWord_36544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36544).length < 2 ^ (prefixWord ++ tailWord_36544).sum := by decide
  have hdescent : baseEnd_36544 < baseStart_36544 := by decide
  rcases family_descends (prefixWord ++ tailWord_36544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36547 : List Nat := [1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 10]
def baseStart_36547 : Nat := 118140960795 + 36547 * 2 ^ 59
def prefixEnd_36547 : Nat := 4983230072969 + 3 ^ 40 * 36547 * 2
def baseEnd_36547 : Nat := 18766177479973743394429

theorem tailTrace_36547 : CollatzResearch.WordTrace tailWord_36547 prefixEnd_36547 18766177479973743394429 := by
  unfold tailWord_36547
  simp only [CollatzResearch.WordTrace]
  refine ⟨1332978598603935575779895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 888652399069290383853263 1332978598603935575779895)
  ·
    refine ⟨1999467897905903363669843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1332978598603935575779895 1999467897905903363669843)
    ·
      refine ⟨2999201846858855045504765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1999467897905903363669843 2999201846858855045504765)
      ·
        refine ⟨1124700692572070642064287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2999201846858855045504765 1124700692572070642064287)
        ·
          refine ⟨1687051038858105963096431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1124700692572070642064287 1687051038858105963096431)
          ·
            refine ⟨2530576558287158944644647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1687051038858105963096431 2530576558287158944644647)
            ·
              refine ⟨3795864837430738416966971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2530576558287158944644647 3795864837430738416966971)
              ·
                refine ⟨5693797256146107625450457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3795864837430738416966971 5693797256146107625450457)
                ·
                  refine ⟨4270347942109580719087843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5693797256146107625450457 4270347942109580719087843)
                  ·
                    refine ⟨6405521913164371078631765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4270347942109580719087843 6405521913164371078631765)
                    ·
                      refine ⟨18766177479973743394429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 6405521913164371078631765 18766177479973743394429)
                      ·
                        rfl

theorem cell23_36547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 10].length) (baseStart_36547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_36547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_36547 prefixEnd_36547 := by exact prefixLift 36547
  have htrace : WordTrace (prefixWord ++ tailWord_36547) baseStart_36547 baseEnd_36547 := by
    simpa [prefixWord, tailWord_36547, baseEnd_36547] using wordTrace_append hprefix tailTrace_36547
  have hstable : (prefixWord ++ tailWord_36547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36547).length < 2 ^ (prefixWord ++ tailWord_36547).sum := by decide
  have hdescent : baseEnd_36547 < baseStart_36547 := by decide
  rcases family_descends (prefixWord ++ tailWord_36547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36551 : List Nat := [1, 1, 4, 1, 1, 1, 3, 2, 4, 3, 2]
def baseStart_36551 : Nat := 118140960795 + 36551 * 2 ^ 59
def prefixEnd_36551 : Nat := 4983230072969 + 3 ^ 40 * 36551 * 2
def baseEnd_36551 : Nat := 18768231402591727744411

theorem tailTrace_36551 : CollatzResearch.WordTrace tailWord_36551 prefixEnd_36551 18768231402591727744411 := by
  unfold tailWord_36551
  simp only [CollatzResearch.WordTrace]
  refine ⟨1333124490589444258925507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 888749660392962839283671 1333124490589444258925507)
  ·
    refine ⟨1999686735884166388388261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1333124490589444258925507 1999686735884166388388261)
    ·
      refine ⟨374941262978281197822799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1999686735884166388388261 374941262978281197822799)
      ·
        refine ⟨562411894467421796734199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 374941262978281197822799 562411894467421796734199)
        ·
          refine ⟨843617841701132695101299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 562411894467421796734199 843617841701132695101299)
          ·
            refine ⟨1265426762551699042651949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 843617841701132695101299 1265426762551699042651949)
            ·
              refine ⟨474535035956887140994481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1265426762551699042651949 474535035956887140994481)
              ·
                refine ⟨355901276967665355745861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 474535035956887140994481 355901276967665355745861)
                ·
                  refine ⟨66731489431437254202349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 355901276967665355745861 66731489431437254202349)
                  ·
                    refine ⟨25024308536788970325881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 66731489431437254202349 25024308536788970325881)
                    ·
                      refine ⟨18768231402591727744411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 25024308536788970325881 18768231402591727744411)
                      ·
                        rfl

theorem cell23_36551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 4, 3, 2].length) (baseStart_36551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_36551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_36551 prefixEnd_36551 := by exact prefixLift 36551
  have htrace : WordTrace (prefixWord ++ tailWord_36551) baseStart_36551 baseEnd_36551 := by
    simpa [prefixWord, tailWord_36551, baseEnd_36551] using wordTrace_append hprefix tailTrace_36551
  have hstable : (prefixWord ++ tailWord_36551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36551).length < 2 ^ (prefixWord ++ tailWord_36551).sum := by decide
  have hdescent : baseEnd_36551 < baseStart_36551 := by decide
  rcases family_descends (prefixWord ++ tailWord_36551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36561 : List Nat := [1, 2, 2, 1, 2, 4, 3, 2, 1, 5]
def baseStart_36561 : Nat := 118140960795 + 36561 * 2 ^ 59
def prefixEnd_36561 : Nat := 4983230072969 + 3 ^ 40 * 36561 * 2
def baseEnd_36561 : Nat := 6257788736378896206455

theorem tailTrace_36561 : CollatzResearch.WordTrace tailWord_36561 prefixEnd_36561 6257788736378896206455 := by
  unfold tailWord_36561
  simp only [CollatzResearch.WordTrace]
  refine ⟨1333489220553215966789537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 888992813702143977859691 1333489220553215966789537)
  ·
    refine ⟨1000116915414911975092153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1333489220553215966789537 1000116915414911975092153)
    ·
      refine ⟨750087686561183981319115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1000116915414911975092153 750087686561183981319115)
      ·
        refine ⟨1125131529841775971978673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 750087686561183981319115 1125131529841775971978673)
        ·
          refine ⟨843848647381331978984005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1125131529841775971978673 843848647381331978984005)
          ·
            refine ⟨158221621383999746059501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 843848647381331978984005 158221621383999746059501)
            ·
              refine ⟨59333108018999904772313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 158221621383999746059501 59333108018999904772313)
              ·
                refine ⟨44499831014249928579235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59333108018999904772313 44499831014249928579235)
                ·
                  refine ⟨66749746521374892868853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44499831014249928579235 66749746521374892868853)
                  ·
                    refine ⟨6257788736378896206455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 66749746521374892868853 6257788736378896206455)
                    ·
                      rfl

theorem cell23_36561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 2, 1, 5].length) (baseStart_36561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_36561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_36561 prefixEnd_36561 := by exact prefixLift 36561
  have htrace : WordTrace (prefixWord ++ tailWord_36561) baseStart_36561 baseEnd_36561 := by
    simpa [prefixWord, tailWord_36561, baseEnd_36561] using wordTrace_append hprefix tailTrace_36561
  have hstable : (prefixWord ++ tailWord_36561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36561).length < 2 ^ (prefixWord ++ tailWord_36561).sum := by decide
  have hdescent : baseEnd_36561 < baseStart_36561 := by decide
  rcases family_descends (prefixWord ++ tailWord_36561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36568 : List Nat := [2, 1, 2, 2, 3, 1, 4, 1, 2, 3, 2]
def baseStart_36568 : Nat := 118140960795 + 36568 * 2 ^ 59
def prefixEnd_36568 : Nat := 4983230072969 + 3 ^ 40 * 36568 * 2
def baseEnd_36568 : Nat := 18776960573718161231833

theorem tailTrace_36568 : CollatzResearch.WordTrace tailWord_36568 prefixEnd_36568 18776960573718161231833 := by
  unfold tailWord_36568
  simp only [CollatzResearch.WordTrace]
  refine ⟨666872265763928081147179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 889163021018570774862905 666872265763928081147179)
  ·
    refine ⟨1000308398645892121720769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 666872265763928081147179 1000308398645892121720769)
    ·
      refine ⟨750231298984419091290577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1000308398645892121720769 750231298984419091290577)
      ·
        refine ⟨562673474238314318467933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 750231298984419091290577 562673474238314318467933)
        ·
          refine ⟨211002552839367869425475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 562673474238314318467933 211002552839367869425475)
          ·
            refine ⟨316503829259051804138213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 211002552839367869425475 316503829259051804138213)
            ·
              refine ⟨59344467986072213275915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 316503829259051804138213 59344467986072213275915)
              ·
                refine ⟨89016701979108319913873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59344467986072213275915 89016701979108319913873)
                ·
                  refine ⟨66762526484331239935405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 89016701979108319913873 66762526484331239935405)
                  ·
                    refine ⟨25035947431624214975777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 66762526484331239935405 25035947431624214975777)
                    ·
                      refine ⟨18776960573718161231833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 25035947431624214975777 18776960573718161231833)
                      ·
                        rfl

theorem cell23_36568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 1, 2, 3, 2].length) (baseStart_36568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_36568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_36568 prefixEnd_36568 := by exact prefixLift 36568
  have htrace : WordTrace (prefixWord ++ tailWord_36568) baseStart_36568 baseEnd_36568 := by
    simpa [prefixWord, tailWord_36568, baseEnd_36568] using wordTrace_append hprefix tailTrace_36568
  have hstable : (prefixWord ++ tailWord_36568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36568).length < 2 ^ (prefixWord ++ tailWord_36568).sum := by decide
  have hdescent : baseEnd_36568 < baseStart_36568 := by decide
  rcases family_descends (prefixWord ++ tailWord_36568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36675 : List Nat := [1, 1, 1, 3, 1, 6, 2, 2, 1, 3, 2]
def baseStart_36675 : Nat := 118140960795 + 36675 * 2 ^ 59
def prefixEnd_36675 : Nat := 4983230072969 + 3 ^ 40 * 36675 * 2
def baseEnd_36675 : Nat := 18831903003749242593841

theorem tailTrace_36675 : CollatzResearch.WordTrace tailWord_36675 prefixEnd_36675 18831903003749242593841 := by
  unfold tailWord_36675
  simp only [CollatzResearch.WordTrace]
  refine ⟨1337647142140213436439479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 891764761426808957626319 1337647142140213436439479)
  ·
    refine ⟨2006470713210320154659219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1337647142140213436439479 2006470713210320154659219)
    ·
      refine ⟨3009706069815480231988829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2006470713210320154659219 3009706069815480231988829)
      ·
        refine ⟨1128639776180805086995811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3009706069815480231988829 1128639776180805086995811)
        ·
          refine ⟨1692959664271207630493717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1128639776180805086995811 1692959664271207630493717)
          ·
            refine ⟨79357484262712857679393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1692959664271207630493717 79357484262712857679393)
            ·
              refine ⟨59518113197034643259545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79357484262712857679393 59518113197034643259545)
              ·
                refine ⟨44638584897775982444659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59518113197034643259545 44638584897775982444659)
                ·
                  refine ⟨66957877346663973666989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44638584897775982444659 66957877346663973666989)
                  ·
                    refine ⟨25109204004998990125121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 66957877346663973666989 25109204004998990125121)
                    ·
                      refine ⟨18831903003749242593841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 25109204004998990125121 18831903003749242593841)
                      ·
                        rfl

theorem cell23_36675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 2, 1, 3, 2].length) (baseStart_36675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_36675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_36675 prefixEnd_36675 := by exact prefixLift 36675
  have htrace : WordTrace (prefixWord ++ tailWord_36675) baseStart_36675 baseEnd_36675 := by
    simpa [prefixWord, tailWord_36675, baseEnd_36675] using wordTrace_append hprefix tailTrace_36675
  have hstable : (prefixWord ++ tailWord_36675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36675).length < 2 ^ (prefixWord ++ tailWord_36675).sum := by decide
  have hdescent : baseEnd_36675 < baseStart_36675 := by decide
  rcases family_descends (prefixWord ++ tailWord_36675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36705 : List Nat := [1, 2, 3, 1, 1, 1, 4, 4, 2, 2, 2]
def baseStart_36705 : Nat := 118140960795 + 36705 * 2 ^ 59
def prefixEnd_36705 : Nat := 4983230072969 + 3 ^ 40 * 36705 * 2
def baseEnd_36705 : Nat := 18847307423384125218703

theorem tailTrace_36705 : CollatzResearch.WordTrace tailWord_36705 prefixEnd_36705 18847307423384125218703 := by
  unfold tailWord_36705
  simp only [CollatzResearch.WordTrace]
  refine ⟨1338741332031528560031569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 892494221354352373354379 1338741332031528560031569)
  ·
    refine ⟨1004055999023646420023677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1338741332031528560031569 1004055999023646420023677)
    ·
      refine ⟨376520999633867407508879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1004055999023646420023677 376520999633867407508879)
      ·
        refine ⟨564781499450801111263319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 376520999633867407508879 564781499450801111263319)
        ·
          refine ⟨847172249176201666894979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 564781499450801111263319 847172249176201666894979)
          ·
            refine ⟨1270758373764302500342469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 847172249176201666894979 1270758373764302500342469)
            ·
              refine ⟨238267195080806718814213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1270758373764302500342469 238267195080806718814213)
              ·
                refine ⟨44675099077651259777665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 238267195080806718814213 44675099077651259777665)
                ·
                  refine ⟨33506324308238444833249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44675099077651259777665 33506324308238444833249)
                  ·
                    refine ⟨25129743231178833624937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33506324308238444833249 25129743231178833624937)
                    ·
                      refine ⟨18847307423384125218703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 25129743231178833624937 18847307423384125218703)
                      ·
                        rfl

theorem cell23_36705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 4, 2, 2, 2].length) (baseStart_36705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_36705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_36705 prefixEnd_36705 := by exact prefixLift 36705
  have htrace : WordTrace (prefixWord ++ tailWord_36705) baseStart_36705 baseEnd_36705 := by
    simpa [prefixWord, tailWord_36705, baseEnd_36705] using wordTrace_append hprefix tailTrace_36705
  have hstable : (prefixWord ++ tailWord_36705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36705).length < 2 ^ (prefixWord ++ tailWord_36705).sum := by decide
  have hdescent : baseEnd_36705 < baseStart_36705 := by decide
  rcases family_descends (prefixWord ++ tailWord_36705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36721 : List Nat := [1, 2, 2, 2, 1, 3, 2, 1, 1, 5, 3]
def baseStart_36721 : Nat := 118140960795 + 36721 * 2 ^ 59
def prefixEnd_36721 : Nat := 4983230072969 + 3 ^ 40 * 36721 * 2
def baseEnd_36721 : Nat := 18855523113856062618629

theorem tailTrace_36721 : CollatzResearch.WordTrace tailWord_36721 prefixEnd_36721 18855523113856062618629 := by
  unfold tailWord_36721
  simp only [CollatzResearch.WordTrace]
  refine ⟨1339324899973563292614017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 892883266649042195076011 1339324899973563292614017)
  ·
    refine ⟨1004493674980172469460513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1339324899973563292614017 1004493674980172469460513)
    ·
      refine ⟨753370256235129352095385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1004493674980172469460513 753370256235129352095385)
      ·
        refine ⟨565027692176347014071539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 753370256235129352095385 565027692176347014071539)
        ·
          refine ⟨847541538264520521107309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 565027692176347014071539 847541538264520521107309)
          ·
            refine ⟨317828076849195195415241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 847541538264520521107309 317828076849195195415241)
            ·
              refine ⟨238371057636896396561431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 317828076849195195415241 238371057636896396561431)
              ·
                refine ⟨357556586455344594842147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 238371057636896396561431 357556586455344594842147)
                ·
                  refine ⟨536334879683016892263221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 357556586455344594842147 536334879683016892263221)
                  ·
                    refine ⟨50281394970282833649677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 536334879683016892263221 50281394970282833649677)
                    ·
                      refine ⟨18855523113856062618629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 50281394970282833649677 18855523113856062618629)
                      ·
                        rfl

theorem cell23_36721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 5, 3].length) (baseStart_36721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_36721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_36721 prefixEnd_36721 := by exact prefixLift 36721
  have htrace : WordTrace (prefixWord ++ tailWord_36721) baseStart_36721 baseEnd_36721 := by
    simpa [prefixWord, tailWord_36721, baseEnd_36721] using wordTrace_append hprefix tailTrace_36721
  have hstable : (prefixWord ++ tailWord_36721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36721).length < 2 ^ (prefixWord ++ tailWord_36721).sum := by decide
  have hdescent : baseEnd_36721 < baseStart_36721 := by decide
  rcases family_descends (prefixWord ++ tailWord_36721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36726 : List Nat := [5, 1, 1, 3, 3, 1, 1, 2, 1, 3, 2]
def baseStart_36726 : Nat := 118140960795 + 36726 * 2 ^ 59
def prefixEnd_36726 : Nat := 4983230072969 + 3 ^ 40 * 36726 * 2
def baseEnd_36726 : Nat := 18858090517128543056107

theorem tailTrace_36726 : CollatzResearch.WordTrace tailWord_36726 prefixEnd_36726 18858090517128543056107 := by
  unfold tailWord_36726
  simp only [CollatzResearch.WordTrace]
  refine ⟨83719204059715571659127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 893004843303632764364021 83719204059715571659127)
  ·
    refine ⟨125578806089573357488691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83719204059715571659127 125578806089573357488691)
    ·
      refine ⟨188368209134360036233037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125578806089573357488691 188368209134360036233037)
      ·
        refine ⟨70638078425385013587389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 188368209134360036233037 70638078425385013587389)
        ·
          refine ⟨26489279409519380095271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70638078425385013587389 26489279409519380095271)
          ·
            refine ⟨39733919114279070142907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26489279409519380095271 39733919114279070142907)
            ·
              refine ⟨59600878671418605214361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39733919114279070142907 59600878671418605214361)
              ·
                refine ⟨44700659003563953910771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59600878671418605214361 44700659003563953910771)
                ·
                  refine ⟨67050988505345930866157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44700659003563953910771 67050988505345930866157)
                  ·
                    refine ⟨25144120689504724074809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 67050988505345930866157 25144120689504724074809)
                    ·
                      refine ⟨18858090517128543056107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 25144120689504724074809 18858090517128543056107)
                      ·
                        rfl

theorem cell23_36726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_36726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_36726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_36726 prefixEnd_36726 := by exact prefixLift 36726
  have htrace : WordTrace (prefixWord ++ tailWord_36726) baseStart_36726 baseEnd_36726 := by
    simpa [prefixWord, tailWord_36726, baseEnd_36726] using wordTrace_append hprefix tailTrace_36726
  have hstable : (prefixWord ++ tailWord_36726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36726).length < 2 ^ (prefixWord ++ tailWord_36726).sum := by decide
  have hdescent : baseEnd_36726 < baseStart_36726 := by decide
  rcases family_descends (prefixWord ++ tailWord_36726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36762 : List Nat := [3, 1, 1, 4, 2, 3, 2, 2, 5]
def baseStart_36762 : Nat := 118140960795 + 36762 * 2 ^ 59
def prefixEnd_36762 : Nat := 4983230072969 + 3 ^ 40 * 36762 * 2
def baseEnd_36762 : Nat := 2097397313410044689549

theorem tailTrace_36762 : CollatzResearch.WordTrace tailWord_36762 prefixEnd_36762 2097397313410044689549 := by
  unfold tailWord_36762
  simp only [CollatzResearch.WordTrace]
  refine ⟨335205073206256823714135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 893880195216684863237693 335205073206256823714135)
  ·
    refine ⟨502807609809385235571203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 335205073206256823714135 502807609809385235571203)
    ·
      refine ⟨754211414714077853356805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 502807609809385235571203 754211414714077853356805)
      ·
        refine ⟨141414640258889597504401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 754211414714077853356805 141414640258889597504401)
        ·
          refine ⟨106060980194167198128301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141414640258889597504401 106060980194167198128301)
          ·
            refine ⟨39772867572812699298113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106060980194167198128301 39772867572812699298113)
            ·
              refine ⟨29829650679609524473585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39772867572812699298113 29829650679609524473585)
              ·
                refine ⟨22372238009707143355189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29829650679609524473585 22372238009707143355189)
                ·
                  refine ⟨2097397313410044689549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22372238009707143355189 2097397313410044689549)
                  ·
                    rfl

theorem cell23_36762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 2, 2, 5].length) (baseStart_36762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_36762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_36762 prefixEnd_36762 := by exact prefixLift 36762
  have htrace : WordTrace (prefixWord ++ tailWord_36762) baseStart_36762 baseEnd_36762 := by
    simpa [prefixWord, tailWord_36762, baseEnd_36762] using wordTrace_append hprefix tailTrace_36762
  have hstable : (prefixWord ++ tailWord_36762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36762).length < 2 ^ (prefixWord ++ tailWord_36762).sum := by decide
  have hdescent : baseEnd_36762 < baseStart_36762 := by decide
  rcases family_descends (prefixWord ++ tailWord_36762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36835 : List Nat := [1, 1, 1, 6, 1, 3, 3, 1, 6]
def baseStart_36835 : Nat := 118140960795 + 36835 * 2 ^ 59
def prefixEnd_36835 : Nat := 4983230072969 + 3 ^ 40 * 36835 * 2
def baseEnd_36835 : Nat := 2101562212052068510345

theorem tailTrace_36835 : CollatzResearch.WordTrace tailWord_36835 prefixEnd_36835 2101562212052068510345 := by
  unfold tailWord_36835
  simp only [CollatzResearch.WordTrace]
  refine ⟨1343482821560560762263959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 895655214373707174842639 1343482821560560762263959)
  ·
    refine ⟨2015224232340841143395939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1343482821560560762263959 2015224232340841143395939)
    ·
      refine ⟨3022836348511261715093909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2015224232340841143395939 3022836348511261715093909)
      ·
        refine ⟨141695453836465392895027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 3022836348511261715093909 141695453836465392895027)
        ·
          refine ⟨212543180754698089342541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141695453836465392895027 212543180754698089342541)
          ·
            refine ⟨79703692783011783503453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 212543180754698089342541 79703692783011783503453)
            ·
              refine ⟨29888884793629418813795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79703692783011783503453 29888884793629418813795)
              ·
                refine ⟨44833327190444128220693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29888884793629418813795 44833327190444128220693)
                ·
                  refine ⟨2101562212052068510345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 44833327190444128220693 2101562212052068510345)
                  ·
                    rfl

theorem cell23_36835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 3, 1, 6].length) (baseStart_36835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_36835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_36835 prefixEnd_36835 := by exact prefixLift 36835
  have htrace : WordTrace (prefixWord ++ tailWord_36835) baseStart_36835 baseEnd_36835 := by
    simpa [prefixWord, tailWord_36835, baseEnd_36835] using wordTrace_append hprefix tailTrace_36835
  have hstable : (prefixWord ++ tailWord_36835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36835).length < 2 ^ (prefixWord ++ tailWord_36835).sum := by decide
  have hdescent : baseEnd_36835 < baseStart_36835 := by decide
  rcases family_descends (prefixWord ++ tailWord_36835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36848 : List Nat := [2, 1, 1, 1, 3, 2, 3, 4, 1, 5]
def baseStart_36848 : Nat := 118140960795 + 36848 * 2 ^ 59
def prefixEnd_36848 : Nat := 4983230072969 + 3 ^ 40 * 36848 * 2
def baseEnd_36848 : Nat := 6306911718992355243515

theorem tailTrace_36848 : CollatzResearch.WordTrace tailWord_36848 prefixEnd_36848 6306911718992355243515 := by
  unfold tailWord_36848
  simp only [CollatzResearch.WordTrace]
  refine ⟨671978485256731991243599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 895971313675642654991465 671978485256731991243599)
  ·
    refine ⟨1007967727885097986865399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 671978485256731991243599 1007967727885097986865399)
    ·
      refine ⟨1511951591827646980298099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1007967727885097986865399 1511951591827646980298099)
      ·
        refine ⟨2267927387741470470447149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1511951591827646980298099 2267927387741470470447149)
        ·
          refine ⟨850472770403051426417681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2267927387741470470447149 850472770403051426417681)
          ·
            refine ⟨637854577802288569813261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 850472770403051426417681 637854577802288569813261)
            ·
              refine ⟨239195466675858213679973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 637854577802288569813261 239195466675858213679973)
              ·
                refine ⟨44849150001723415064995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 239195466675858213679973 44849150001723415064995)
                ·
                  refine ⟨67273725002585122597493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44849150001723415064995 67273725002585122597493)
                  ·
                    refine ⟨6306911718992355243515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 67273725002585122597493 6306911718992355243515)
                    ·
                      rfl

theorem cell23_36848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 4, 1, 5].length) (baseStart_36848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_36848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_36848 prefixEnd_36848 := by exact prefixLift 36848
  have htrace : WordTrace (prefixWord ++ tailWord_36848) baseStart_36848 baseEnd_36848 := by
    simpa [prefixWord, tailWord_36848, baseEnd_36848] using wordTrace_append hprefix tailTrace_36848
  have hstable : (prefixWord ++ tailWord_36848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36848).length < 2 ^ (prefixWord ++ tailWord_36848).sum := by decide
  have hdescent : baseEnd_36848 < baseStart_36848 := by decide
  rcases family_descends (prefixWord ++ tailWord_36848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36851 : List Nat := [1, 1, 1, 2, 2, 2, 1, 2, 2, 5, 4]
def baseStart_36851 : Nat := 118140960795 + 36851 * 2 ^ 59
def prefixEnd_36851 : Nat := 4983230072969 + 3 ^ 40 * 36851 * 2
def baseEnd_36851 : Nat := 18922275598940553993031

theorem tailTrace_36851 : CollatzResearch.WordTrace tailWord_36851 prefixEnd_36851 18922275598940553993031 := by
  unfold tailWord_36851
  simp only [CollatzResearch.WordTrace]
  refine ⟨1344066389502595494846407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 896044259668396996564271 1344066389502595494846407)
  ·
    refine ⟨2016099584253893242269611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1344066389502595494846407 2016099584253893242269611)
    ·
      refine ⟨3024149376380839863404417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2016099584253893242269611 3024149376380839863404417)
      ·
        refine ⟨2268112032285629897553313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3024149376380839863404417 2268112032285629897553313)
        ·
          refine ⟨1701084024214222423164985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2268112032285629897553313 1701084024214222423164985)
          ·
            refine ⟨1275813018160666817373739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1701084024214222423164985 1275813018160666817373739)
            ·
              refine ⟨1913719527241000226060609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1275813018160666817373739 1913719527241000226060609)
              ·
                refine ⟨1435289645430750169545457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1913719527241000226060609 1435289645430750169545457)
                ·
                  refine ⟨1076467234073062627159093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1435289645430750169545457 1076467234073062627159093)
                  ·
                    refine ⟨100918803194349621296165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1076467234073062627159093 100918803194349621296165)
                    ·
                      refine ⟨18922275598940553993031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 100918803194349621296165 18922275598940553993031)
                      ·
                        rfl

theorem cell23_36851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 5, 4].length) (baseStart_36851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_36851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_36851 prefixEnd_36851 := by exact prefixLift 36851
  have htrace : WordTrace (prefixWord ++ tailWord_36851) baseStart_36851 baseEnd_36851 := by
    simpa [prefixWord, tailWord_36851, baseEnd_36851] using wordTrace_append hprefix tailTrace_36851
  have hstable : (prefixWord ++ tailWord_36851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36851).length < 2 ^ (prefixWord ++ tailWord_36851).sum := by decide
  have hdescent : baseEnd_36851 < baseStart_36851 := by decide
  rcases family_descends (prefixWord ++ tailWord_36851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36888 : List Nat := [2, 1, 2, 3, 2, 1, 1, 4, 1, 1, 5]
def baseStart_36888 : Nat := 118140960795 + 36888 * 2 ^ 59
def prefixEnd_36888 : Nat := 4983230072969 + 3 ^ 40 * 36888 * 2
def baseEnd_36888 : Nat := 18941274383156909230361

theorem tailTrace_36888 : CollatzResearch.WordTrace tailWord_36888 prefixEnd_36888 18941274383156909230361 := by
  unfold tailWord_36888
  simp only [CollatzResearch.WordTrace]
  refine ⟨672707945184275406971659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 896943926912367209295545 672707945184275406971659)
  ·
    refine ⟨1009061917776413110457489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 672707945184275406971659 1009061917776413110457489)
    ·
      refine ⟨756796438332309832843117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1009061917776413110457489 756796438332309832843117)
      ·
        refine ⟨283798664374616187316169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 756796438332309832843117 283798664374616187316169)
        ·
          refine ⟨212848998280962140487127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 283798664374616187316169 212848998280962140487127)
          ·
            refine ⟨319273497421443210730691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 212848998280962140487127 319273497421443210730691)
            ·
              refine ⟨478910246132164816096037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 319273497421443210730691 478910246132164816096037)
              ·
                refine ⟨89795671149780903018007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 478910246132164816096037 89795671149780903018007)
                ·
                  refine ⟨134693506724671354527011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 89795671149780903018007 134693506724671354527011)
                  ·
                    refine ⟨202040260087007031790517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 134693506724671354527011 202040260087007031790517)
                    ·
                      refine ⟨18941274383156909230361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 202040260087007031790517 18941274383156909230361)
                      ·
                        rfl

theorem cell23_36888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_36888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_36888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_36888 prefixEnd_36888 := by exact prefixLift 36888
  have htrace : WordTrace (prefixWord ++ tailWord_36888) baseStart_36888 baseEnd_36888 := by
    simpa [prefixWord, tailWord_36888, baseEnd_36888] using wordTrace_append hprefix tailTrace_36888
  have hstable : (prefixWord ++ tailWord_36888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36888).length < 2 ^ (prefixWord ++ tailWord_36888).sum := by decide
  have hdescent : baseEnd_36888 < baseStart_36888 := by decide
  rcases family_descends (prefixWord ++ tailWord_36888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36895 : List Nat := [1, 1, 2, 4, 1, 2, 3, 3, 2, 4]
def baseStart_36895 : Nat := 118140960795 + 36895 * 2 ^ 59
def prefixEnd_36895 : Nat := 4983230072969 + 3 ^ 40 * 36895 * 2
def baseEnd_36895 : Nat := 6314956249246127280943

theorem tailTrace_36895 : CollatzResearch.WordTrace tailWord_36895 prefixEnd_36895 6314956249246127280943 := by
  unfold tailWord_36895
  simp only [CollatzResearch.WordTrace]
  refine ⟨1345671201343191009448139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 897114134228794006298759 1345671201343191009448139)
  ·
    refine ⟨2018506802014786514172209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1345671201343191009448139 2018506802014786514172209)
    ·
      refine ⟨1513880101511089885629157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2018506802014786514172209 1513880101511089885629157)
      ·
        refine ⟨283852519033329353555467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1513880101511089885629157 283852519033329353555467)
        ·
          refine ⟨425778778549994030333201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 283852519033329353555467 425778778549994030333201)
          ·
            refine ⟨319334083912495522749901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 425778778549994030333201 319334083912495522749901)
            ·
              refine ⟨119750281467185821031213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 319334083912495522749901 119750281467185821031213)
              ·
                refine ⟨44906355550194682886705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 119750281467185821031213 44906355550194682886705)
                ·
                  refine ⟨33679766662646012165029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44906355550194682886705 33679766662646012165029)
                  ·
                    refine ⟨6314956249246127280943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33679766662646012165029 6314956249246127280943)
                    ·
                      rfl

theorem cell23_36895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 3, 2, 4].length) (baseStart_36895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_36895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_36895 prefixEnd_36895 := by exact prefixLift 36895
  have htrace : WordTrace (prefixWord ++ tailWord_36895) baseStart_36895 baseEnd_36895 := by
    simpa [prefixWord, tailWord_36895, baseEnd_36895] using wordTrace_append hprefix tailTrace_36895
  have hstable : (prefixWord ++ tailWord_36895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36895).length < 2 ^ (prefixWord ++ tailWord_36895).sum := by decide
  have hdescent : baseEnd_36895 < baseStart_36895 := by decide
  rcases family_descends (prefixWord ++ tailWord_36895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36898 : List Nat := [3, 3, 1, 1, 1, 2, 1, 3, 1, 1, 6]
def baseStart_36898 : Nat := 118140960795 + 36898 * 2 ^ 59
def prefixEnd_36898 : Nat := 4983230072969 + 3 ^ 40 * 36898 * 2
def baseEnd_36898 : Nat := 18946409189701870105315

theorem tailTrace_36898 : CollatzResearch.WordTrace tailWord_36898 prefixEnd_36898 18946409189701870105315 := by
  unfold tailWord_36898
  simp only [CollatzResearch.WordTrace]
  refine ⟨336445155083080630451837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 897187080221548347871565 336445155083080630451837)
  ·
    refine ⟨126166933156155236419439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 336445155083080630451837 126166933156155236419439)
    ·
      refine ⟨189250399734232854629159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126166933156155236419439 189250399734232854629159)
      ·
        refine ⟨283875599601349281943739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189250399734232854629159 283875599601349281943739)
        ·
          refine ⟨425813399402023922915609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 283875599601349281943739 425813399402023922915609)
          ·
            refine ⟨319360049551517942186707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 425813399402023922915609 319360049551517942186707)
            ·
              refine ⟨479040074327276913280061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 319360049551517942186707 479040074327276913280061)
              ·
                refine ⟨179640027872728842480023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 479040074327276913280061 179640027872728842480023)
                ·
                  refine ⟨269460041809093263720035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 179640027872728842480023 269460041809093263720035)
                  ·
                    refine ⟨404190062713639895580053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 269460041809093263720035 404190062713639895580053)
                    ·
                      refine ⟨18946409189701870105315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 404190062713639895580053 18946409189701870105315)
                      ·
                        rfl

theorem cell23_36898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_36898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_36898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_36898 prefixEnd_36898 := by exact prefixLift 36898
  have htrace : WordTrace (prefixWord ++ tailWord_36898) baseStart_36898 baseEnd_36898 := by
    simpa [prefixWord, tailWord_36898, baseEnd_36898] using wordTrace_append hprefix tailTrace_36898
  have hstable : (prefixWord ++ tailWord_36898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36898).length < 2 ^ (prefixWord ++ tailWord_36898).sum := by decide
  have hdescent : baseEnd_36898 < baseStart_36898 := by decide
  rcases family_descends (prefixWord ++ tailWord_36898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36948 : List Nat := [2, 4, 1, 1, 1, 1, 1, 2, 1, 4, 5]
def baseStart_36948 : Nat := 118140960795 + 36948 * 2 ^ 59
def prefixEnd_36948 : Nat := 4983230072969 + 3 ^ 40 * 36948 * 2
def baseEnd_36948 : Nat := 18972083222426674480085

theorem tailTrace_36948 : CollatzResearch.WordTrace tailWord_36948 prefixEnd_36948 18972083222426674480085 := by
  unfold tailWord_36948
  simp only [CollatzResearch.WordTrace]
  refine ⟨673802135075590530563749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 898402846767454040751665 673802135075590530563749)
  ·
    refine ⟨126337900326673224480703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 673802135075590530563749 126337900326673224480703)
    ·
      refine ⟨189506850490009836721055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126337900326673224480703 189506850490009836721055)
      ·
        refine ⟨284260275735014755081583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189506850490009836721055 284260275735014755081583)
        ·
          refine ⟨426390413602522132622375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 284260275735014755081583 426390413602522132622375)
          ·
            refine ⟨639585620403783198933563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 426390413602522132622375 639585620403783198933563)
            ·
              refine ⟨959378430605674798400345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 639585620403783198933563 959378430605674798400345)
              ·
                refine ⟨719533822954256098800259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 959378430605674798400345 719533822954256098800259)
                ·
                  refine ⟨1079300734431384148200389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 719533822954256098800259 1079300734431384148200389)
                  ·
                    refine ⟨202368887705884527787573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1079300734431384148200389 202368887705884527787573)
                    ·
                      refine ⟨18972083222426674480085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 202368887705884527787573 18972083222426674480085)
                      ·
                        rfl

theorem cell23_36948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_36948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_36948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_36948 prefixEnd_36948 := by exact prefixLift 36948
  have htrace : WordTrace (prefixWord ++ tailWord_36948) baseStart_36948 baseEnd_36948 := by
    simpa [prefixWord, tailWord_36948, baseEnd_36948] using wordTrace_append hprefix tailTrace_36948
  have hstable : (prefixWord ++ tailWord_36948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36948).length < 2 ^ (prefixWord ++ tailWord_36948).sum := by decide
  have hdescent : baseEnd_36948 < baseStart_36948 := by decide
  rcases family_descends (prefixWord ++ tailWord_36948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_36952 : List Nat := [2, 1, 2, 2, 1, 4, 2, 3, 2, 1, 3]
def baseStart_36952 : Nat := 118140960795 + 36952 * 2 ^ 59
def prefixEnd_36952 : Nat := 4983230072969 + 3 ^ 40 * 36952 * 2
def baseEnd_36952 : Nat := 18974137145044658830067

theorem tailTrace_36952 : CollatzResearch.WordTrace tailWord_36952 prefixEnd_36952 18974137145044658830067 := by
  unfold tailWord_36952
  simp only [CollatzResearch.WordTrace]
  refine ⟨673875081068344872136555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 898500108091126496182073 673875081068344872136555)
  ·
    refine ⟨1010812621602517308204833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 673875081068344872136555 1010812621602517308204833)
    ·
      refine ⟨758109466201887981153625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1010812621602517308204833 758109466201887981153625)
      ·
        refine ⟨568582099651415985865219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 758109466201887981153625 568582099651415985865219)
        ·
          refine ⟨852873149477123978797829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 568582099651415985865219 852873149477123978797829)
          ·
            refine ⟨159913715526960746024593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 852873149477123978797829 159913715526960746024593)
            ·
              refine ⟨119935286645220559518445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 159913715526960746024593 119935286645220559518445)
              ·
                refine ⟨44975732491957709819417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 119935286645220559518445 44975732491957709819417)
                ·
                  refine ⟨33731799368968282364563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44975732491957709819417 33731799368968282364563)
                  ·
                    refine ⟨50597699053452423546845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33731799368968282364563 50597699053452423546845)
                    ·
                      refine ⟨18974137145044658830067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 50597699053452423546845 18974137145044658830067)
                      ·
                        rfl

theorem cell23_36952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 3, 2, 1, 3].length) (baseStart_36952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_36952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_36952 prefixEnd_36952 := by exact prefixLift 36952
  have htrace : WordTrace (prefixWord ++ tailWord_36952) baseStart_36952 baseEnd_36952 := by
    simpa [prefixWord, tailWord_36952, baseEnd_36952] using wordTrace_append hprefix tailTrace_36952
  have hstable : (prefixWord ++ tailWord_36952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_36952).length < 2 ^ (prefixWord ++ tailWord_36952).sum := by decide
  have hdescent : baseEnd_36952 < baseStart_36952 := by decide
  rcases family_descends (prefixWord ++ tailWord_36952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37105 : List Nat := [1, 2, 2, 2, 2, 1, 3, 4, 6]
def baseStart_37105 : Nat := 118140960795 + 37105 * 2 ^ 59
def prefixEnd_37105 : Nat := 4983230072969 + 3 ^ 40 * 37105 * 2
def baseEnd_37105 : Nat := 2116966631686951135207

theorem tailTrace_37105 : CollatzResearch.WordTrace tailWord_37105 prefixEnd_37105 2116966631686951135207 := by
  unfold tailWord_37105
  simp only [CollatzResearch.WordTrace]
  refine ⟨1353330530582396874592769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 902220353721597916395179 1353330530582396874592769)
  ·
    refine ⟨1014997897936797655944577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1353330530582396874592769 1014997897936797655944577)
    ·
      refine ⟨761248423452598241958433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1014997897936797655944577 761248423452598241958433)
      ·
        refine ⟨570936317589448681468825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 761248423452598241958433 570936317589448681468825)
        ·
          refine ⟨428202238192086511101619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 570936317589448681468825 428202238192086511101619)
          ·
            refine ⟨642303357288129766652429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 428202238192086511101619 642303357288129766652429)
            ·
              refine ⟨240863758983048662494661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 642303357288129766652429 240863758983048662494661)
              ·
                refine ⟨45161954809321624217749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 240863758983048662494661 45161954809321624217749)
                ·
                  refine ⟨2116966631686951135207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 45161954809321624217749 2116966631686951135207)
                  ·
                    rfl

theorem cell23_37105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 4, 6].length) (baseStart_37105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_37105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_37105 prefixEnd_37105 := by exact prefixLift 37105
  have htrace : WordTrace (prefixWord ++ tailWord_37105) baseStart_37105 baseEnd_37105 := by
    simpa [prefixWord, tailWord_37105, baseEnd_37105] using wordTrace_append hprefix tailTrace_37105
  have hstable : (prefixWord ++ tailWord_37105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37105).length < 2 ^ (prefixWord ++ tailWord_37105).sum := by decide
  have hdescent : baseEnd_37105 < baseStart_37105 := by decide
  rcases family_descends (prefixWord ++ tailWord_37105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37192 : List Nat := [2, 1, 3, 1, 1, 2, 2, 3, 3, 2, 3]
def baseStart_37192 : Nat := 118140960795 + 37192 * 2 ^ 59
def prefixEnd_37192 : Nat := 4983230072969 + 3 ^ 40 * 37192 * 2
def baseEnd_37192 : Nat := 19097372502123719828963

theorem tailTrace_37192 : CollatzResearch.WordTrace tailWord_37192 prefixEnd_37192 19097372502123719828963 := by
  unfold tailWord_37192
  simp only [CollatzResearch.WordTrace]
  refine ⟨678251840633605366504915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 904335787511473822006553 678251840633605366504915)
  ·
    refine ⟨1017377760950408049757373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 678251840633605366504915 1017377760950408049757373)
    ·
      refine ⟨381516660356403018659015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1017377760950408049757373 381516660356403018659015)
      ·
        refine ⟨572274990534604527988523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 381516660356403018659015 572274990534604527988523)
        ·
          refine ⟨858412485801906791982785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 572274990534604527988523 858412485801906791982785)
          ·
            refine ⟨643809364351430093987089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 858412485801906791982785 643809364351430093987089)
            ·
              refine ⟨482857023263572570490317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 643809364351430093987089 482857023263572570490317)
              ·
                refine ⟨181071383723839713933869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 482857023263572570490317 181071383723839713933869)
                ·
                  refine ⟨67901768896439892725201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 181071383723839713933869 67901768896439892725201)
                  ·
                    refine ⟨50926326672329919543901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 67901768896439892725201 50926326672329919543901)
                    ·
                      refine ⟨19097372502123719828963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 50926326672329919543901 19097372502123719828963)
                      ·
                        rfl

theorem cell23_37192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 3, 3, 2, 3].length) (baseStart_37192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_37192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_37192 prefixEnd_37192 := by exact prefixLift 37192
  have htrace : WordTrace (prefixWord ++ tailWord_37192) baseStart_37192 baseEnd_37192 := by
    simpa [prefixWord, tailWord_37192, baseEnd_37192] using wordTrace_append hprefix tailTrace_37192
  have hstable : (prefixWord ++ tailWord_37192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37192).length < 2 ^ (prefixWord ++ tailWord_37192).sum := by decide
  have hdescent : baseEnd_37192 < baseStart_37192 := by decide
  rcases family_descends (prefixWord ++ tailWord_37192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37202 : List Nat := [3, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4]
def baseStart_37202 : Nat := 118140960795 + 37202 * 2 ^ 59
def prefixEnd_37202 : Nat := 4983230072969 + 3 ^ 40 * 37202 * 2
def baseEnd_37202 : Nat := 19102507308668680703917

theorem tailTrace_37202 : CollatzResearch.WordTrace tailWord_37202 prefixEnd_37202 19102507308668680703917 := by
  unfold tailWord_37202
  simp only [CollatzResearch.WordTrace]
  refine ⟨339217102807745610218465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 904578940820654960582573 339217102807745610218465)
  ·
    refine ⟨254412827105809207663849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 339217102807745610218465 254412827105809207663849)
    ·
      refine ⟨190809620329356905747887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 254412827105809207663849 190809620329356905747887)
      ·
        refine ⟨286214430494035358621831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190809620329356905747887 286214430494035358621831)
        ·
          refine ⟨429321645741053037932747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 286214430494035358621831 429321645741053037932747)
          ·
            refine ⟨643982468611579556899121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 429321645741053037932747 643982468611579556899121)
            ·
              refine ⟨482986851458684667674341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 643982468611579556899121 482986851458684667674341)
              ·
                refine ⟨90560034648503375188939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 482986851458684667674341 90560034648503375188939)
                ·
                  refine ⟨135840051972755062783409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90560034648503375188939 135840051972755062783409)
                  ·
                    refine ⟨101880038979566297087557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 135840051972755062783409 101880038979566297087557)
                    ·
                      refine ⟨19102507308668680703917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 101880038979566297087557 19102507308668680703917)
                      ·
                        rfl

theorem cell23_37202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_37202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_37202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_37202 prefixEnd_37202 := by exact prefixLift 37202
  have htrace : WordTrace (prefixWord ++ tailWord_37202) baseStart_37202 baseEnd_37202 := by
    simpa [prefixWord, tailWord_37202, baseEnd_37202] using wordTrace_append hprefix tailTrace_37202
  have hstable : (prefixWord ++ tailWord_37202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37202).length < 2 ^ (prefixWord ++ tailWord_37202).sum := by decide
  have hdescent : baseEnd_37202 < baseStart_37202 := by decide
  rcases family_descends (prefixWord ++ tailWord_37202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37223 : List Nat := [1, 1, 5, 1, 3, 3, 1, 1, 3, 2, 2]
def baseStart_37223 : Nat := 118140960795 + 37223 * 2 ^ 59
def prefixEnd_37223 : Nat := 4983230072969 + 3 ^ 40 * 37223 * 2
def baseEnd_37223 : Nat := 19113290402413098541321

theorem tailTrace_37223 : CollatzResearch.WordTrace tailWord_37223 prefixEnd_37223 19113290402413098541321 := by
  unfold tailWord_37223
  simp only [CollatzResearch.WordTrace]
  refine ⟨1357634344154903027388323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 905089562769935351592215 1357634344154903027388323)
  ·
    refine ⟨2036451516232354541082485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1357634344154903027388323 2036451516232354541082485)
    ·
      refine ⟨190917329646783238226483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2036451516232354541082485 190917329646783238226483)
      ·
        refine ⟨286375994470174857339725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190917329646783238226483 286375994470174857339725)
        ·
          refine ⟨107390997926315571502397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 286375994470174857339725 107390997926315571502397)
          ·
            refine ⟨40271624222368339313399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107390997926315571502397 40271624222368339313399)
            ·
              refine ⟨60407436333552508970099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40271624222368339313399 60407436333552508970099)
              ·
                refine ⟨90611154500328763455149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60407436333552508970099 90611154500328763455149)
                ·
                  refine ⟨33979182937623286295681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 90611154500328763455149 33979182937623286295681)
                  ·
                    refine ⟨25484387203217464721761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33979182937623286295681 25484387203217464721761)
                    ·
                      refine ⟨19113290402413098541321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 25484387203217464721761 19113290402413098541321)
                      ·
                        rfl

theorem cell23_37223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 1, 3, 2, 2].length) (baseStart_37223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_37223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_37223 prefixEnd_37223 := by exact prefixLift 37223
  have htrace : WordTrace (prefixWord ++ tailWord_37223) baseStart_37223 baseEnd_37223 := by
    simpa [prefixWord, tailWord_37223, baseEnd_37223] using wordTrace_append hprefix tailTrace_37223
  have hstable : (prefixWord ++ tailWord_37223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37223).length < 2 ^ (prefixWord ++ tailWord_37223).sum := by decide
  have hdescent : baseEnd_37223 < baseStart_37223 := by decide
  rcases family_descends (prefixWord ++ tailWord_37223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37225 : List Nat := [1, 2, 1, 1, 1, 3, 4, 1, 2, 7]
def baseStart_37225 : Nat := 118140960795 + 37225 * 2 ^ 59
def prefixEnd_37225 : Nat := 4983230072969 + 3 ^ 40 * 37225 * 2
def baseEnd_37225 : Nat := 6371439121240696905437

theorem tailTrace_37225 : CollatzResearch.WordTrace tailWord_37225 prefixEnd_37225 6371439121240696905437 := by
  unfold tailWord_37225
  simp only [CollatzResearch.WordTrace]
  refine ⟨1357707290147657368961129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 905138193431771579307419 1357707290147657368961129)
  ·
    refine ⟨1018280467610743026720847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1357707290147657368961129 1018280467610743026720847)
    ·
      refine ⟨1527420701416114540081271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1018280467610743026720847 1527420701416114540081271)
      ·
        refine ⟨2291131052124171810121907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1527420701416114540081271 2291131052124171810121907)
        ·
          refine ⟨3436696578186257715182861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2291131052124171810121907 3436696578186257715182861)
          ·
            refine ⟨1288761216819846643193573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3436696578186257715182861 1288761216819846643193573)
            ·
              refine ⟨241642728153721245598795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1288761216819846643193573 241642728153721245598795)
              ·
                refine ⟨362464092230581868398193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 241642728153721245598795 362464092230581868398193)
                ·
                  refine ⟨271848069172936401298645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 362464092230581868398193 271848069172936401298645)
                  ·
                    refine ⟨6371439121240696905437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 271848069172936401298645 6371439121240696905437)
                    ·
                      rfl

theorem cell23_37225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 2, 7].length) (baseStart_37225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_37225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_37225 prefixEnd_37225 := by exact prefixLift 37225
  have htrace : WordTrace (prefixWord ++ tailWord_37225) baseStart_37225 baseEnd_37225 := by
    simpa [prefixWord, tailWord_37225, baseEnd_37225] using wordTrace_append hprefix tailTrace_37225
  have hstable : (prefixWord ++ tailWord_37225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37225).length < 2 ^ (prefixWord ++ tailWord_37225).sum := by decide
  have hdescent : baseEnd_37225 < baseStart_37225 := by decide
  rcases family_descends (prefixWord ++ tailWord_37225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37235 : List Nat := [1, 1, 1, 2, 2, 1, 2, 2, 4, 2, 5]
def baseStart_37235 : Nat := 118140960795 + 37235 * 2 ^ 59
def prefixEnd_37235 : Nat := 4983230072969 + 3 ^ 40 * 37235 * 2
def baseEnd_37235 : Nat := 19119452170267051591265

theorem tailTrace_37235 : CollatzResearch.WordTrace tailWord_37235 prefixEnd_37235 19119452170267051591265 := by
  unfold tailWord_37235
  simp only [CollatzResearch.WordTrace]
  refine ⟨1358072020111429076825159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 905381346740952717883439 1358072020111429076825159)
  ·
    refine ⟨2037108030167143615237739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1358072020111429076825159 2037108030167143615237739)
    ·
      refine ⟨3055662045250715422856609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2037108030167143615237739 3055662045250715422856609)
      ·
        refine ⟨2291746533938036567142457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3055662045250715422856609 2291746533938036567142457)
        ·
          refine ⟨1718809900453527425356843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2291746533938036567142457 1718809900453527425356843)
          ·
            refine ⟨2578214850680291138035265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1718809900453527425356843 2578214850680291138035265)
            ·
              refine ⟨1933661138010218353526449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2578214850680291138035265 1933661138010218353526449)
              ·
                refine ⟨1450245853507663765144837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1933661138010218353526449 1450245853507663765144837)
                ·
                  refine ⟨271921097532686955964657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1450245853507663765144837 271921097532686955964657)
                  ·
                    refine ⟨203940823149515216973493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 271921097532686955964657 203940823149515216973493)
                    ·
                      refine ⟨19119452170267051591265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 203940823149515216973493 19119452170267051591265)
                      ·
                        rfl

theorem cell23_37235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 4, 2, 5].length) (baseStart_37235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_37235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_37235 prefixEnd_37235 := by exact prefixLift 37235
  have htrace : WordTrace (prefixWord ++ tailWord_37235) baseStart_37235 baseEnd_37235 := by
    simpa [prefixWord, tailWord_37235, baseEnd_37235] using wordTrace_append hprefix tailTrace_37235
  have hstable : (prefixWord ++ tailWord_37235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37235).length < 2 ^ (prefixWord ++ tailWord_37235).sum := by decide
  have hdescent : baseEnd_37235 < baseStart_37235 := by decide
  rcases family_descends (prefixWord ++ tailWord_37235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37279 : List Nat := [1, 1, 2, 5, 1, 1, 1, 2, 3, 4, 2]
def baseStart_37279 : Nat := 118140960795 + 37279 * 2 ^ 59
def prefixEnd_37279 : Nat := 4983230072969 + 3 ^ 40 * 37279 * 2
def baseEnd_37279 : Nat := 19142045319064879441063

theorem tailTrace_37279 : CollatzResearch.WordTrace tailWord_37279 prefixEnd_37279 19142045319064879441063 := by
  unfold tailWord_37279
  simp only [CollatzResearch.WordTrace]
  refine ⟨1359676831952024591426891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 906451221301349727617927 1359676831952024591426891)
  ·
    refine ⟨2039515247928036887140337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1359676831952024591426891 2039515247928036887140337)
    ·
      refine ⟨1529636435946027665355253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2039515247928036887140337 1529636435946027665355253)
      ·
        refine ⟨143403415869940093627055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1529636435946027665355253 143403415869940093627055)
        ·
          refine ⟨215105123804910140440583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143403415869940093627055 215105123804910140440583)
          ·
            refine ⟨322657685707365210660875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215105123804910140440583 322657685707365210660875)
            ·
              refine ⟨483986528561047815991313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 322657685707365210660875 483986528561047815991313)
              ·
                refine ⟨362989896420785861993485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 483986528561047815991313 362989896420785861993485)
                ·
                  refine ⟨136121211157794698247557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 362989896420785861993485 136121211157794698247557)
                  ·
                    refine ⟨25522727092086505921417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 136121211157794698247557 25522727092086505921417)
                    ·
                      refine ⟨19142045319064879441063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 25522727092086505921417 19142045319064879441063)
                      ·
                        rfl

theorem cell23_37279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 3, 4, 2].length) (baseStart_37279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_37279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_37279 prefixEnd_37279 := by exact prefixLift 37279
  have htrace : WordTrace (prefixWord ++ tailWord_37279) baseStart_37279 baseEnd_37279 := by
    simpa [prefixWord, tailWord_37279, baseEnd_37279] using wordTrace_append hprefix tailTrace_37279
  have hstable : (prefixWord ++ tailWord_37279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37279).length < 2 ^ (prefixWord ++ tailWord_37279).sum := by decide
  have hdescent : baseEnd_37279 < baseStart_37279 := by decide
  rcases family_descends (prefixWord ++ tailWord_37279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37290 : List Nat := [3, 1, 6, 1, 1, 1, 2, 1, 1, 3, 3]
def baseStart_37290 : Nat := 118140960795 + 37290 * 2 ^ 59
def prefixEnd_37290 : Nat := 4983230072969 + 3 ^ 40 * 37290 * 2
def baseEnd_37290 : Nat := 19147693606264336403513

theorem tailTrace_37290 : CollatzResearch.WordTrace tailWord_37290 prefixEnd_37290 19147693606264336403513 := by
  unfold tailWord_37290
  simp only [CollatzResearch.WordTrace]
  refine ⟨340019508728043367519331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 906718689941448980051549 340019508728043367519331)
  ·
    refine ⟨510029263092065051278997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 340019508728043367519331 510029263092065051278997)
    ·
      refine ⟨23907621707440549278703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 510029263092065051278997 23907621707440549278703)
      ·
        refine ⟨35861432561160823918055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23907621707440549278703 35861432561160823918055)
        ·
          refine ⟨53792148841741235877083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35861432561160823918055 53792148841741235877083)
          ·
            refine ⟨80688223262611853815625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53792148841741235877083 80688223262611853815625)
            ·
              refine ⟨60516167446958890361719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80688223262611853815625 60516167446958890361719)
              ·
                refine ⟨90774251170438335542579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60516167446958890361719 90774251170438335542579)
                ·
                  refine ⟨136161376755657503313869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90774251170438335542579 136161376755657503313869)
                  ·
                    refine ⟨51060516283371563742701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 136161376755657503313869 51060516283371563742701)
                    ·
                      refine ⟨19147693606264336403513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 51060516283371563742701 19147693606264336403513)
                      ·
                        rfl

theorem cell23_37290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_37290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_37290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_37290 prefixEnd_37290 := by exact prefixLift 37290
  have htrace : WordTrace (prefixWord ++ tailWord_37290) baseStart_37290 baseEnd_37290 := by
    simpa [prefixWord, tailWord_37290, baseEnd_37290] using wordTrace_append hprefix tailTrace_37290
  have hstable : (prefixWord ++ tailWord_37290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37290).length < 2 ^ (prefixWord ++ tailWord_37290).sum := by decide
  have hdescent : baseEnd_37290 < baseStart_37290 := by decide
  rcases family_descends (prefixWord ++ tailWord_37290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37312 : List Nat := [2, 1, 1, 2, 3, 1, 1, 1, 3, 5, 3]
def baseStart_37312 : Nat := 118140960795 + 37312 * 2 ^ 59
def prefixEnd_37312 : Nat := 4983230072969 + 3 ^ 40 * 37312 * 2
def baseEnd_37312 : Nat := 19158990180663250328411

theorem tailTrace_37312 : CollatzResearch.WordTrace tailWord_37312 prefixEnd_37312 19158990180663250328411 := by
  unfold tailWord_37312
  simp only [CollatzResearch.WordTrace]
  refine ⟨680440220416235613689095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 907253627221647484918793 680440220416235613689095)
  ·
    refine ⟨1020660330624353420533643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 680440220416235613689095 1020660330624353420533643)
    ·
      refine ⟨1530990495936530130800465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1020660330624353420533643 1530990495936530130800465)
      ·
        refine ⟨1148242871952397598100349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1530990495936530130800465 1148242871952397598100349)
        ·
          refine ⟨430591076982149099287631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1148242871952397598100349 430591076982149099287631)
          ·
            refine ⟨645886615473223648931447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 430591076982149099287631 645886615473223648931447)
            ·
              refine ⟨968829923209835473397171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 645886615473223648931447 968829923209835473397171)
              ·
                refine ⟨1453244884814753210095757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 968829923209835473397171 1453244884814753210095757)
                ·
                  refine ⟨544966831805532453785909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1453244884814753210095757 544966831805532453785909)
                  ·
                    refine ⟨51090640481768667542429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 544966831805532453785909 51090640481768667542429)
                    ·
                      refine ⟨19158990180663250328411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 51090640481768667542429 19158990180663250328411)
                      ·
                        rfl

theorem cell23_37312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 3, 5, 3].length) (baseStart_37312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_37312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_37312 prefixEnd_37312 := by exact prefixLift 37312
  have htrace : WordTrace (prefixWord ++ tailWord_37312) baseStart_37312 baseEnd_37312 := by
    simpa [prefixWord, tailWord_37312, baseEnd_37312] using wordTrace_append hprefix tailTrace_37312
  have hstable : (prefixWord ++ tailWord_37312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37312).length < 2 ^ (prefixWord ++ tailWord_37312).sum := by decide
  have hdescent : baseEnd_37312 < baseStart_37312 := by decide
  rcases family_descends (prefixWord ++ tailWord_37312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37319 : List Nat := [1, 1, 4, 1, 1, 4, 1, 5, 5]
def baseStart_37319 : Nat := 118140960795 + 37319 * 2 ^ 59
def prefixEnd_37319 : Nat := 4983230072969 + 3 ^ 40 * 37319 * 2
def baseEnd_37319 : Nat := 2129176060582746993431

theorem tailTrace_37319 : CollatzResearch.WordTrace tailWord_37319 prefixEnd_37319 2129176060582746993431 := by
  unfold tailWord_37319
  simp only [CollatzResearch.WordTrace]
  refine ⟨1361135751807111422883011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 907423834538074281922007 1361135751807111422883011)
  ·
    refine ⟨2041703627710667134324517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1361135751807111422883011 2041703627710667134324517)
    ·
      refine ⟨382819430195750087685847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2041703627710667134324517 382819430195750087685847)
      ·
        refine ⟨574229145293625131528771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 382819430195750087685847 574229145293625131528771)
        ·
          refine ⟨861343717940437697293157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 574229145293625131528771 861343717940437697293157)
          ·
            refine ⟨161501947113832068242467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 861343717940437697293157 161501947113832068242467)
            ·
              refine ⟨242252920670748102363701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 161501947113832068242467 242252920670748102363701)
              ·
                refine ⟨22711211312882634596597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 242252920670748102363701 22711211312882634596597)
                ·
                  refine ⟨2129176060582746993431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22711211312882634596597 2129176060582746993431)
                  ·
                    rfl

theorem cell23_37319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 5, 5].length) (baseStart_37319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_37319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_37319 prefixEnd_37319 := by exact prefixLift 37319
  have htrace : WordTrace (prefixWord ++ tailWord_37319) baseStart_37319 baseEnd_37319 := by
    simpa [prefixWord, tailWord_37319, baseEnd_37319] using wordTrace_append hprefix tailTrace_37319
  have hstable : (prefixWord ++ tailWord_37319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37319).length < 2 ^ (prefixWord ++ tailWord_37319).sum := by decide
  have hdescent : baseEnd_37319 < baseStart_37319 := by decide
  rcases family_descends (prefixWord ++ tailWord_37319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37330 : List Nat := [3, 2, 2, 4, 1, 1, 1, 1, 4, 2, 2]
def baseStart_37330 : Nat := 118140960795 + 37330 * 2 ^ 59
def prefixEnd_37330 : Nat := 4983230072969 + 3 ^ 40 * 37330 * 2
def baseEnd_37330 : Nat := 19168232832444179903329

theorem tailTrace_37330 : CollatzResearch.WordTrace tailWord_37330 prefixEnd_37330 19168232832444179903329 := by
  unfold tailWord_37330
  simp only [CollatzResearch.WordTrace]
  refine ⟨340384238691815075383361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 907691303178173534355629 340384238691815075383361)
  ·
    refine ⟨255288179018861306537521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 340384238691815075383361 255288179018861306537521)
    ·
      refine ⟨191466134264145979903141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 255288179018861306537521 191466134264145979903141)
      ·
        refine ⟨35899900174527371231839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 191466134264145979903141 35899900174527371231839)
        ·
          refine ⟨53849850261791056847759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35899900174527371231839 53849850261791056847759)
          ·
            refine ⟨80774775392686585271639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53849850261791056847759 80774775392686585271639)
            ·
              refine ⟨121162163089029877907459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80774775392686585271639 121162163089029877907459)
              ·
                refine ⟨181743244633544816861189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 121162163089029877907459 181743244633544816861189)
                ·
                  refine ⟨34076858368789653161473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 181743244633544816861189 34076858368789653161473)
                  ·
                    refine ⟨25557643776592239871105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34076858368789653161473 25557643776592239871105)
                    ·
                      refine ⟨19168232832444179903329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 25557643776592239871105 19168232832444179903329)
                      ·
                        rfl

theorem cell23_37330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_37330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_37330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_37330 prefixEnd_37330 := by exact prefixLift 37330
  have htrace : WordTrace (prefixWord ++ tailWord_37330) baseStart_37330 baseEnd_37330 := by
    simpa [prefixWord, tailWord_37330, baseEnd_37330] using wordTrace_append hprefix tailTrace_37330
  have hstable : (prefixWord ++ tailWord_37330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37330).length < 2 ^ (prefixWord ++ tailWord_37330).sum := by decide
  have hdescent : baseEnd_37330 < baseStart_37330 := by decide
  rcases family_descends (prefixWord ++ tailWord_37330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37369 : List Nat := [1, 2, 1, 3, 1, 2, 2, 2, 1, 6, 2]
def baseStart_37369 : Nat := 118140960795 + 37369 * 2 ^ 59
def prefixEnd_37369 : Nat := 4983230072969 + 3 ^ 40 * 37369 * 2
def baseEnd_37369 : Nat := 19188258577969527315649

theorem tailTrace_37369 : CollatzResearch.WordTrace tailWord_37369 prefixEnd_37369 19188258577969527315649 := by
  unfold tailWord_37369
  simp only [CollatzResearch.WordTrace]
  refine ⟨1362959401625969962203161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 908639601083979974802107 1362959401625969962203161)
  ·
    refine ⟨1022219551219477471652371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1362959401625969962203161 1022219551219477471652371)
    ·
      refine ⟨1533329326829216207478557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1022219551219477471652371 1533329326829216207478557)
      ·
        refine ⟨574998497560956077804459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1533329326829216207478557 574998497560956077804459)
        ·
          refine ⟨862497746341434116706689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 574998497560956077804459 862497746341434116706689)
          ·
            refine ⟨646873309756075587530017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 862497746341434116706689 646873309756075587530017)
            ·
              refine ⟨485154982317056690647513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 646873309756075587530017 485154982317056690647513)
              ·
                refine ⟨363866236737792517985635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 485154982317056690647513 363866236737792517985635)
                ·
                  refine ⟨545799355106688776978453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 363866236737792517985635 545799355106688776978453)
                  ·
                    refine ⟨25584344770626036420865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 545799355106688776978453 25584344770626036420865)
                    ·
                      refine ⟨19188258577969527315649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 25584344770626036420865 19188258577969527315649)
                      ·
                        rfl

theorem cell23_37369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 6, 2].length) (baseStart_37369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_37369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_37369 prefixEnd_37369 := by exact prefixLift 37369
  have htrace : WordTrace (prefixWord ++ tailWord_37369) baseStart_37369 baseEnd_37369 := by
    simpa [prefixWord, tailWord_37369, baseEnd_37369] using wordTrace_append hprefix tailTrace_37369
  have hstable : (prefixWord ++ tailWord_37369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37369).length < 2 ^ (prefixWord ++ tailWord_37369).sum := by decide
  have hdescent : baseEnd_37369 < baseStart_37369 := by decide
  rcases family_descends (prefixWord ++ tailWord_37369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37372 : List Nat := [2, 2, 2, 1, 2, 1, 1, 2, 2, 3, 5]
def baseStart_37372 : Nat := 118140960795 + 37372 * 2 ^ 59
def prefixEnd_37372 : Nat := 4983230072969 + 3 ^ 40 * 37372 * 2
def baseEnd_37372 : Nat := 19189799019933015578135

theorem tailTrace_37372 : CollatzResearch.WordTrace tailWord_37372 prefixEnd_37372 19189799019933015578135 := by
  unfold tailWord_37372
  simp only [CollatzResearch.WordTrace]
  refine ⟨681534410307550737281185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 908712547076734316374913 681534410307550737281185)
  ·
    refine ⟨511150807730663052960889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 681534410307550737281185 511150807730663052960889)
    ·
      refine ⟨383363105797997289720667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 511150807730663052960889 383363105797997289720667)
      ·
        refine ⟨575044658696995934581001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 383363105797997289720667 575044658696995934581001)
        ·
          refine ⟨431283494022746950935751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 575044658696995934581001 431283494022746950935751)
          ·
            refine ⟨646925241034120426403627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 431283494022746950935751 646925241034120426403627)
            ·
              refine ⟨970387861551180639605441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 646925241034120426403627 970387861551180639605441)
              ·
                refine ⟨727790896163385479704081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 970387861551180639605441 727790896163385479704081)
                ·
                  refine ⟨545843172122539109778061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 727790896163385479704081 545843172122539109778061)
                  ·
                    refine ⟨204691189545952166166773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 545843172122539109778061 204691189545952166166773)
                    ·
                      refine ⟨19189799019933015578135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 204691189545952166166773 19189799019933015578135)
                      ·
                        rfl

theorem cell23_37372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 2, 3, 5].length) (baseStart_37372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_37372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_37372 prefixEnd_37372 := by exact prefixLift 37372
  have htrace : WordTrace (prefixWord ++ tailWord_37372) baseStart_37372 baseEnd_37372 := by
    simpa [prefixWord, tailWord_37372, baseEnd_37372] using wordTrace_append hprefix tailTrace_37372
  have hstable : (prefixWord ++ tailWord_37372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37372).length < 2 ^ (prefixWord ++ tailWord_37372).sum := by decide
  have hdescent : baseEnd_37372 < baseStart_37372 := by decide
  rcases family_descends (prefixWord ++ tailWord_37372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37409 : List Nat := [1, 2, 3, 2, 2, 1, 3, 3, 6]
def baseStart_37409 : Nat := 118140960795 + 37409 * 2 ^ 59
def prefixEnd_37409 : Nat := 4983230072969 + 3 ^ 40 * 37409 * 2
def baseEnd_37409 : Nat := 2134310867127707868385

theorem tailTrace_37409 : CollatzResearch.WordTrace tailWord_37409 prefixEnd_37409 2134310867127707868385 := by
  unfold tailWord_37409
  simp only [CollatzResearch.WordTrace]
  refine ⟨1364418321481056793659281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 909612214320704529106187 1364418321481056793659281)
  ·
    refine ⟨1023313741110792595244461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1364418321481056793659281 1023313741110792595244461)
    ·
      refine ⟨383742652916547223216673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1023313741110792595244461 383742652916547223216673)
      ·
        refine ⟨287806989687410417412505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 383742652916547223216673 287806989687410417412505)
        ·
          refine ⟨215855242265557813059379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 287806989687410417412505 215855242265557813059379)
          ·
            refine ⟨323782863398336719589069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215855242265557813059379 323782863398336719589069)
            ·
              refine ⟨121418573774376269845901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 323782863398336719589069 121418573774376269845901)
              ·
                refine ⟨45531965165391101192213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 121418573774376269845901 45531965165391101192213)
                ·
                  refine ⟨2134310867127707868385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 45531965165391101192213 2134310867127707868385)
                  ·
                    rfl

theorem cell23_37409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 3, 6].length) (baseStart_37409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_37409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_37409 prefixEnd_37409 := by exact prefixLift 37409
  have htrace : WordTrace (prefixWord ++ tailWord_37409) baseStart_37409 baseEnd_37409 := by
    simpa [prefixWord, tailWord_37409, baseEnd_37409] using wordTrace_append hprefix tailTrace_37409
  have hstable : (prefixWord ++ tailWord_37409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37409).length < 2 ^ (prefixWord ++ tailWord_37409).sum := by decide
  have hdescent : baseEnd_37409 < baseStart_37409 := by decide
  rcases family_descends (prefixWord ++ tailWord_37409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37476 : List Nat := [2, 3, 1, 1, 2, 2, 2, 4, 1, 1, 4]
def baseStart_37476 : Nat := 118140960795 + 37476 * 2 ^ 59
def prefixEnd_37476 : Nat := 4983230072969 + 3 ^ 40 * 37476 * 2
def baseEnd_37476 : Nat := 19243201008000608677657

theorem tailTrace_37476 : CollatzResearch.WordTrace tailWord_37476 prefixEnd_37476 19243201008000608677657 := by
  unfold tailWord_37476
  simp only [CollatzResearch.WordTrace]
  refine ⟨683431006119163618174141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 911241341492218157565521 683431006119163618174141)
  ·
    refine ⟨256286627294686356815303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 683431006119163618174141 256286627294686356815303)
    ·
      refine ⟨384429940942029535222955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256286627294686356815303 384429940942029535222955)
      ·
        refine ⟨576644911413044302834433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 384429940942029535222955 576644911413044302834433)
        ·
          refine ⟨432483683559783227125825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 576644911413044302834433 432483683559783227125825)
          ·
            refine ⟨324362762669837420344369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 432483683559783227125825 324362762669837420344369)
            ·
              refine ⟨243272072002378065258277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 324362762669837420344369 243272072002378065258277)
              ·
                refine ⟨45613513500445887235927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 243272072002378065258277 45613513500445887235927)
                ·
                  refine ⟨68420270250668830853891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45613513500445887235927 68420270250668830853891)
                  ·
                    refine ⟨102630405376003246280837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 68420270250668830853891 102630405376003246280837)
                    ·
                      refine ⟨19243201008000608677657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 102630405376003246280837 19243201008000608677657)
                      ·
                        rfl

theorem cell23_37476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 4, 1, 1, 4].length) (baseStart_37476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_37476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_37476 prefixEnd_37476 := by exact prefixLift 37476
  have htrace : WordTrace (prefixWord ++ tailWord_37476) baseStart_37476 baseEnd_37476 := by
    simpa [prefixWord, tailWord_37476, baseEnd_37476] using wordTrace_append hprefix tailTrace_37476
  have hstable : (prefixWord ++ tailWord_37476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37476).length < 2 ^ (prefixWord ++ tailWord_37476).sum := by decide
  have hdescent : baseEnd_37476 < baseStart_37476 := by decide
  rcases family_descends (prefixWord ++ tailWord_37476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37486 : List Nat := [4, 1, 2, 2, 2, 1, 2, 2, 1, 6]
def baseStart_37486 : Nat := 118140960795 + 37486 * 2 ^ 59
def prefixEnd_37486 : Nat := 4983230072969 + 3 ^ 40 * 37486 * 2
def baseEnd_37486 : Nat := 6416111938181856517537

theorem tailTrace_37486 : CollatzResearch.WordTrace tailWord_37486 prefixEnd_37486 6416111938181856517537 := by
  unfold tailWord_37486
  simp only [CollatzResearch.WordTrace]
  refine ⟨170903342775262368026539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 911484494801399296141541 170903342775262368026539)
  ·
    refine ⟨256355014162893552039809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 170903342775262368026539 256355014162893552039809)
    ·
      refine ⟨192266260622170164029857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 256355014162893552039809 192266260622170164029857)
      ·
        refine ⟨144199695466627623022393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192266260622170164029857 144199695466627623022393)
        ·
          refine ⟨108149771599970717266795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144199695466627623022393 108149771599970717266795)
          ·
            refine ⟨162224657399956075900193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108149771599970717266795 162224657399956075900193)
            ·
              refine ⟨121668493049967056925145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 162224657399956075900193 121668493049967056925145)
              ·
                refine ⟨91251369787475292693859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121668493049967056925145 91251369787475292693859)
                ·
                  refine ⟨136877054681212939040789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 91251369787475292693859 136877054681212939040789)
                  ·
                    refine ⟨6416111938181856517537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 136877054681212939040789 6416111938181856517537)
                    ·
                      rfl

theorem cell23_37486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 2, 1, 6].length) (baseStart_37486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_37486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_37486 prefixEnd_37486 := by exact prefixLift 37486
  have htrace : WordTrace (prefixWord ++ tailWord_37486) baseStart_37486 baseEnd_37486 := by
    simpa [prefixWord, tailWord_37486, baseEnd_37486] using wordTrace_append hprefix tailTrace_37486
  have hstable : (prefixWord ++ tailWord_37486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37486).length < 2 ^ (prefixWord ++ tailWord_37486).sum := by decide
  have hdescent : baseEnd_37486 < baseStart_37486 := by decide
  rcases family_descends (prefixWord ++ tailWord_37486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37490 : List Nat := [3, 2, 1, 2, 4, 2, 2, 1, 1, 5]
def baseStart_37490 : Nat := 118140960795 + 37490 * 2 ^ 59
def prefixEnd_37490 : Nat := 4983230072969 + 3 ^ 40 * 37490 * 2
def baseEnd_37490 : Nat := 6416796579054517967531

theorem tailTrace_37490 : CollatzResearch.WordTrace tailWord_37490 prefixEnd_37490 6416796579054517967531 := by
  unfold tailWord_37490
  simp only [CollatzResearch.WordTrace]
  refine ⟨341843158546901906839481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 911581756125071751571949 341843158546901906839481)
  ·
    refine ⟨256382368910176430129611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 341843158546901906839481 256382368910176430129611)
    ·
      refine ⟨384573553365264645194417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 256382368910176430129611 384573553365264645194417)
      ·
        refine ⟨288430165023948483895813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 384573553365264645194417 288430165023948483895813)
        ·
          refine ⟨54080655941990340730465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 288430165023948483895813 54080655941990340730465)
          ·
            refine ⟨40560491956492755547849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54080655941990340730465 40560491956492755547849)
            ·
              refine ⟨30420368967369566660887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40560491956492755547849 30420368967369566660887)
              ·
                refine ⟨45630553451054349991331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30420368967369566660887 45630553451054349991331)
                ·
                  refine ⟨68445830176581524986997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45630553451054349991331 68445830176581524986997)
                  ·
                    refine ⟨6416796579054517967531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 68445830176581524986997 6416796579054517967531)
                    ·
                      rfl

theorem cell23_37490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 2, 1, 1, 5].length) (baseStart_37490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_37490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_37490 prefixEnd_37490 := by exact prefixLift 37490
  have htrace : WordTrace (prefixWord ++ tailWord_37490) baseStart_37490 baseEnd_37490 := by
    simpa [prefixWord, tailWord_37490, baseEnd_37490] using wordTrace_append hprefix tailTrace_37490
  have hstable : (prefixWord ++ tailWord_37490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37490).length < 2 ^ (prefixWord ++ tailWord_37490).sum := by decide
  have hdescent : baseEnd_37490 < baseStart_37490 := by decide
  rcases family_descends (prefixWord ++ tailWord_37490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37496 : List Nat := [2, 1, 2, 1, 1, 1, 2, 7, 1, 2, 3]
def baseStart_37496 : Nat := 118140960795 + 37496 * 2 ^ 59
def prefixEnd_37496 : Nat := 4983230072969 + 3 ^ 40 * 37496 * 2
def baseEnd_37496 : Nat := 19253470621090530427565

theorem tailTrace_37496 : CollatzResearch.WordTrace tailWord_37496 prefixEnd_37496 19253470621090530427565 := by
  unfold tailWord_37496
  simp only [CollatzResearch.WordTrace]
  refine ⟨683795736082935326038171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 911727648110580434717561 683795736082935326038171)
  ·
    refine ⟨1025693604124402989057257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 683795736082935326038171 1025693604124402989057257)
    ·
      refine ⟨769270203093302241792943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1025693604124402989057257 769270203093302241792943)
      ·
        refine ⟨1153905304639953362689415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 769270203093302241792943 1153905304639953362689415)
        ·
          refine ⟨1730857956959930044034123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1153905304639953362689415 1730857956959930044034123)
          ·
            refine ⟨2596286935439895066051185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1730857956959930044034123 2596286935439895066051185)
            ·
              refine ⟨1947215201579921299538389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2596286935439895066051185 1947215201579921299538389)
              ·
                refine ⟨45637856287029405457931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1947215201579921299538389 45637856287029405457931)
                ·
                  refine ⟨68456784430544108186897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45637856287029405457931 68456784430544108186897)
                  ·
                    refine ⟨51342588322908081140173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 68456784430544108186897 51342588322908081140173)
                    ·
                      refine ⟨19253470621090530427565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 51342588322908081140173 19253470621090530427565)
                      ·
                        rfl

theorem cell23_37496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 7, 1, 2, 3].length) (baseStart_37496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_37496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_37496 prefixEnd_37496 := by exact prefixLift 37496
  have htrace : WordTrace (prefixWord ++ tailWord_37496) baseStart_37496 baseEnd_37496 := by
    simpa [prefixWord, tailWord_37496, baseEnd_37496] using wordTrace_append hprefix tailTrace_37496
  have hstable : (prefixWord ++ tailWord_37496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37496).length < 2 ^ (prefixWord ++ tailWord_37496).sum := by decide
  have hdescent : baseEnd_37496 < baseStart_37496 := by decide
  rcases family_descends (prefixWord ++ tailWord_37496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37566 : List Nat := [4, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4]
def baseStart_37566 : Nat := 118140960795 + 37566 * 2 ^ 59
def prefixEnd_37566 : Nat := 4983230072969 + 3 ^ 40 * 37566 * 2
def baseEnd_37566 : Nat := 19289414266905256552243

theorem tailTrace_37566 : CollatzResearch.WordTrace tailWord_37566 prefixEnd_37566 19289414266905256552243 := by
  unfold tailWord_37566
  simp only [CollatzResearch.WordTrace]
  refine ⟨171268072739034075890569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 913429721274848404749701 171268072739034075890569)
  ·
    refine ⟨128451054554275556917927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 171268072739034075890569 128451054554275556917927)
    ·
      refine ⟨192676581831413335376891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128451054554275556917927 192676581831413335376891)
      ·
        refine ⟨289014872747120003065337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 192676581831413335376891 289014872747120003065337)
        ·
          refine ⟨216761154560340002299003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 289014872747120003065337 216761154560340002299003)
          ·
            refine ⟨325141731840510003448505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 216761154560340002299003 325141731840510003448505)
            ·
              refine ⟨243856298880382502586379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 325141731840510003448505 243856298880382502586379)
              ·
                refine ⟨365784448320573753879569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 243856298880382502586379 365784448320573753879569)
                ·
                  refine ⟨274338336240430315409677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 365784448320573753879569 274338336240430315409677)
                  ·
                    refine ⟨102876876090161368278629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 274338336240430315409677 102876876090161368278629)
                    ·
                      refine ⟨19289414266905256552243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 102876876090161368278629 19289414266905256552243)
                      ·
                        rfl

theorem cell23_37566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_37566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_37566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_37566 prefixEnd_37566 := by exact prefixLift 37566
  have htrace : WordTrace (prefixWord ++ tailWord_37566) baseStart_37566 baseEnd_37566 := by
    simpa [prefixWord, tailWord_37566, baseEnd_37566] using wordTrace_append hprefix tailTrace_37566
  have hstable : (prefixWord ++ tailWord_37566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37566).length < 2 ^ (prefixWord ++ tailWord_37566).sum := by decide
  have hdescent : baseEnd_37566 < baseStart_37566 := by decide
  rcases family_descends (prefixWord ++ tailWord_37566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37616 : List Nat := [2, 1, 1, 1, 3, 1, 4, 2, 2, 3, 3]
def baseStart_37616 : Nat := 118140960795 + 37616 * 2 ^ 59
def prefixEnd_37616 : Nat := 4983230072969 + 3 ^ 40 * 37616 * 2
def baseEnd_37616 : Nat := 19315088299630060927013

theorem tailTrace_37616 : CollatzResearch.WordTrace tailWord_37616 prefixEnd_37616 19315088299630060927013 := by
  unfold tailWord_37616
  simp only [CollatzResearch.WordTrace]
  refine ⟨685984115865565573222351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 914645487820754097629801 685984115865565573222351)
  ·
    refine ⟨1028976173798348359833527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 685984115865565573222351 1028976173798348359833527)
    ·
      refine ⟨1543464260697522539750291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1028976173798348359833527 1543464260697522539750291)
      ·
        refine ⟨2315196391046283809625437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1543464260697522539750291 2315196391046283809625437)
        ·
          refine ⟨868198646642356428609539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2315196391046283809625437 868198646642356428609539)
          ·
            refine ⟨1302297969963534642914309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 868198646642356428609539 1302297969963534642914309)
            ·
              refine ⟨244180869368162745546433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1302297969963534642914309 244180869368162745546433)
              ·
                refine ⟨183135652026122059159825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 244180869368162745546433 183135652026122059159825)
                ·
                  refine ⟨137351739019591544369869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 183135652026122059159825 137351739019591544369869)
                  ·
                    refine ⟨51506902132346829138701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 137351739019591544369869 51506902132346829138701)
                    ·
                      refine ⟨19315088299630060927013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 51506902132346829138701 19315088299630060927013)
                      ·
                        rfl

theorem cell23_37616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 2, 2, 3, 3].length) (baseStart_37616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_37616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_37616 prefixEnd_37616 := by exact prefixLift 37616
  have htrace : WordTrace (prefixWord ++ tailWord_37616) baseStart_37616 baseEnd_37616 := by
    simpa [prefixWord, tailWord_37616, baseEnd_37616] using wordTrace_append hprefix tailTrace_37616
  have hstable : (prefixWord ++ tailWord_37616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37616).length < 2 ^ (prefixWord ++ tailWord_37616).sum := by decide
  have hdescent : baseEnd_37616 < baseStart_37616 := by decide
  rcases family_descends (prefixWord ++ tailWord_37616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37619 : List Nat := [1, 1, 1, 2, 2, 3, 1, 2, 3, 7]
def baseStart_37619 : Nat := 118140960795 + 37619 * 2 ^ 59
def prefixEnd_37619 : Nat := 4983230072969 + 3 ^ 40 * 37619 * 2
def baseEnd_37619 : Nat := 6438876247197849729833

theorem tailTrace_37619 : CollatzResearch.WordTrace tailWord_37619 prefixEnd_37619 6438876247197849729833 := by
  unfold tailWord_37619
  simp only [CollatzResearch.WordTrace]
  refine ⟨1372077650720262658803911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 914718433813508439202607 1372077650720262658803911)
  ·
    refine ⟨2058116476080393988205867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1372077650720262658803911 2058116476080393988205867)
    ·
      refine ⟨3087174714120590982308801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2058116476080393988205867 3087174714120590982308801)
      ·
        refine ⟨2315381035590443236731601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3087174714120590982308801 2315381035590443236731601)
        ·
          refine ⟨1736535776692832427548701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2315381035590443236731601 1736535776692832427548701)
          ·
            refine ⟨651200916259812160330763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1736535776692832427548701 651200916259812160330763)
            ·
              refine ⟨976801374389718240496145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 651200916259812160330763 976801374389718240496145)
              ·
                refine ⟨732601030792288680372109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 976801374389718240496145 732601030792288680372109)
                ·
                  refine ⟨274725386547108255139541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 732601030792288680372109 274725386547108255139541)
                  ·
                    refine ⟨6438876247197849729833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 274725386547108255139541 6438876247197849729833)
                    ·
                      rfl

theorem cell23_37619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 3, 7].length) (baseStart_37619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_37619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_37619 prefixEnd_37619 := by exact prefixLift 37619
  have htrace : WordTrace (prefixWord ++ tailWord_37619) baseStart_37619 baseEnd_37619 := by
    simpa [prefixWord, tailWord_37619, baseEnd_37619] using wordTrace_append hprefix tailTrace_37619
  have hstable : (prefixWord ++ tailWord_37619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37619).length < 2 ^ (prefixWord ++ tailWord_37619).sum := by decide
  have hdescent : baseEnd_37619 < baseStart_37619 := by decide
  rcases family_descends (prefixWord ++ tailWord_37619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37636 : List Nat := [2, 3, 2, 2, 1, 1, 2, 2, 1, 7]
def baseStart_37636 : Nat := 118140960795 + 37636 * 2 ^ 59
def prefixEnd_37636 : Nat := 4983230072969 + 3 ^ 40 * 37636 * 2
def baseEnd_37636 : Nat := 6441785970906660892307

theorem tailTrace_37636 : CollatzResearch.WordTrace tailWord_37636 prefixEnd_37636 6441785970906660892307 := by
  unfold tailWord_37636
  simp only [CollatzResearch.WordTrace]
  refine ⟨686348845829337281086381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 915131794439116374781841 686348845829337281086381)
  ·
    refine ⟨257380817186001480407393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 686348845829337281086381 257380817186001480407393)
    ·
      refine ⟨193035612889501110305545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 257380817186001480407393 193035612889501110305545)
      ·
        refine ⟨144776709667125832729159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193035612889501110305545 144776709667125832729159)
        ·
          refine ⟨217165064500688749093739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144776709667125832729159 217165064500688749093739)
          ·
            refine ⟨325747596751033123640609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217165064500688749093739 325747596751033123640609)
            ·
              refine ⟨244310697563274842730457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 325747596751033123640609 244310697563274842730457)
              ·
                refine ⟨183233023172456132047843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 244310697563274842730457 183233023172456132047843)
                ·
                  refine ⟨274849534758684198071765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 183233023172456132047843 274849534758684198071765)
                  ·
                    refine ⟨6441785970906660892307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 274849534758684198071765 6441785970906660892307)
                    ·
                      rfl

theorem cell23_37636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 2, 1, 7].length) (baseStart_37636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_37636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_37636 prefixEnd_37636 := by exact prefixLift 37636
  have htrace : WordTrace (prefixWord ++ tailWord_37636) baseStart_37636 baseEnd_37636 := by
    simpa [prefixWord, tailWord_37636, baseEnd_37636] using wordTrace_append hprefix tailTrace_37636
  have hstable : (prefixWord ++ tailWord_37636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37636).length < 2 ^ (prefixWord ++ tailWord_37636).sum := by decide
  have hdescent : baseEnd_37636 < baseStart_37636 := by decide
  rcases family_descends (prefixWord ++ tailWord_37636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37659 : List Nat := [1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 9]
def baseStart_37659 : Nat := 118140960795 + 37659 * 2 ^ 59
def prefixEnd_37659 : Nat := 4983230072969 + 3 ^ 40 * 37659 * 2
def baseEnd_37659 : Nat := 19337167967773392689315

theorem tailTrace_37659 : CollatzResearch.WordTrace tailWord_37659 prefixEnd_37659 19337167967773392689315 := by
  unfold tailWord_37659
  simp only [CollatzResearch.WordTrace]
  refine ⟨1373536570575349490260031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 915691047050232993506687 1373536570575349490260031)
  ·
    refine ⟨2060304855863024235390047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1373536570575349490260031 2060304855863024235390047)
    ·
      refine ⟨3090457283794536353085071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2060304855863024235390047 3090457283794536353085071)
      ·
        refine ⟨4635685925691804529627607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3090457283794536353085071 4635685925691804529627607)
        ·
          refine ⟨6953528888537706794441411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4635685925691804529627607 6953528888537706794441411)
          ·
            refine ⟨10430293332806560191662117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6953528888537706794441411 10430293332806560191662117)
            ·
              refine ⟨1955679999901230035936647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10430293332806560191662117 1955679999901230035936647)
              ·
                refine ⟨2933519999851845053904971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1955679999901230035936647 2933519999851845053904971)
                ·
                  refine ⟨4400279999777767580857457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2933519999851845053904971 4400279999777767580857457)
                  ·
                    refine ⟨3300209999833325685643093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4400279999777767580857457 3300209999833325685643093)
                    ·
                      refine ⟨19337167967773392689315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 3300209999833325685643093 19337167967773392689315)
                      ·
                        rfl

theorem cell23_37659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 9].length) (baseStart_37659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_37659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_37659 prefixEnd_37659 := by exact prefixLift 37659
  have htrace : WordTrace (prefixWord ++ tailWord_37659) baseStart_37659 baseEnd_37659 := by
    simpa [prefixWord, tailWord_37659, baseEnd_37659] using wordTrace_append hprefix tailTrace_37659
  have hstable : (prefixWord ++ tailWord_37659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37659).length < 2 ^ (prefixWord ++ tailWord_37659).sum := by decide
  have hdescent : baseEnd_37659 < baseStart_37659 := by decide
  rcases family_descends (prefixWord ++ tailWord_37659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37683 : List Nat := [1, 1, 1, 2, 6, 1, 1, 3, 3, 4]
def baseStart_37683 : Nat := 118140960795 + 37683 * 2 ^ 59
def prefixEnd_37683 : Nat := 4983230072969 + 3 ^ 40 * 37683 * 2
def baseEnd_37683 : Nat := 6449830501160432929735

theorem tailTrace_37683 : CollatzResearch.WordTrace tailWord_37683 prefixEnd_37683 6449830501160432929735 := by
  unfold tailWord_37683
  simp only [CollatzResearch.WordTrace]
  refine ⟨1374411922488401589133703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 916274614992267726089135 1374411922488401589133703)
  ·
    refine ⟨2061617883732602383700555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1374411922488401589133703 2061617883732602383700555)
    ·
      refine ⟨3092426825598903575550833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2061617883732602383700555 3092426825598903575550833)
      ·
        refine ⟨2319320119199177681663125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3092426825598903575550833 2319320119199177681663125)
        ·
          refine ⟨108718130587461453827959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 2319320119199177681663125 108718130587461453827959)
          ·
            refine ⟨163077195881192180741939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108718130587461453827959 163077195881192180741939)
            ·
              refine ⟨244615793821788271112909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163077195881192180741939 244615793821788271112909)
              ·
                refine ⟨91730922683170601667341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 244615793821788271112909 91730922683170601667341)
                ·
                  refine ⟨34399096006188975625253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 91730922683170601667341 34399096006188975625253)
                  ·
                    refine ⟨6449830501160432929735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34399096006188975625253 6449830501160432929735)
                    ·
                      rfl

theorem cell23_37683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 3, 3, 4].length) (baseStart_37683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_37683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_37683 prefixEnd_37683 := by exact prefixLift 37683
  have htrace : WordTrace (prefixWord ++ tailWord_37683) baseStart_37683 baseEnd_37683 := by
    simpa [prefixWord, tailWord_37683, baseEnd_37683] using wordTrace_append hprefix tailTrace_37683
  have hstable : (prefixWord ++ tailWord_37683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37683).length < 2 ^ (prefixWord ++ tailWord_37683).sum := by decide
  have hdescent : baseEnd_37683 < baseStart_37683 := by decide
  rcases family_descends (prefixWord ++ tailWord_37683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37696 : List Nat := [2, 1, 1, 2, 2, 1, 1, 7, 6]
def baseStart_37696 : Nat := 118140960795 + 37696 * 2 ^ 59
def prefixEnd_37696 : Nat := 4983230072969 + 3 ^ 40 * 37696 * 2
def baseEnd_37696 : Nat := 2150685194665527547405

theorem tailTrace_37696 : CollatzResearch.WordTrace tailWord_37696 prefixEnd_37696 2150685194665527547405 := by
  unfold tailWord_37696
  simp only [CollatzResearch.WordTrace]
  refine ⟨687443035720652404678471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 916590714294203206237961 687443035720652404678471)
  ·
    refine ⟨1031164553580978607017707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 687443035720652404678471 1031164553580978607017707)
    ·
      refine ⟨1546746830371467910526561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1031164553580978607017707 1546746830371467910526561)
      ·
        refine ⟨1160060122778600932894921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1546746830371467910526561 1160060122778600932894921)
        ·
          refine ⟨870045092083950699671191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1160060122778600932894921 870045092083950699671191)
          ·
            refine ⟨1305067638125926049506787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 870045092083950699671191 1305067638125926049506787)
            ·
              refine ⟨1957601457188889074260181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1305067638125926049506787 1957601457188889074260181)
              ·
                refine ⟨45881284152864587677973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1957601457188889074260181 45881284152864587677973)
                ·
                  refine ⟨2150685194665527547405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 45881284152864587677973 2150685194665527547405)
                  ·
                    rfl

theorem cell23_37696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 7, 6].length) (baseStart_37696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_37696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_37696 prefixEnd_37696 := by exact prefixLift 37696
  have htrace : WordTrace (prefixWord ++ tailWord_37696) baseStart_37696 baseEnd_37696 := by
    simpa [prefixWord, tailWord_37696, baseEnd_37696] using wordTrace_append hprefix tailTrace_37696
  have hstable : (prefixWord ++ tailWord_37696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37696).length < 2 ^ (prefixWord ++ tailWord_37696).sum := by decide
  have hdescent : baseEnd_37696 < baseStart_37696 := by decide
  rcases family_descends (prefixWord ++ tailWord_37696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37756 : List Nat := [2, 2, 2, 1, 1, 1, 1, 2, 5, 6]
def baseStart_37756 : Nat := 118140960795 + 37756 * 2 ^ 59
def prefixEnd_37756 : Nat := 4983230072969 + 3 ^ 40 * 37756 * 2
def baseEnd_37756 : Nat := 6462325197086504392123

theorem tailTrace_37756 : CollatzResearch.WordTrace tailWord_37756 prefixEnd_37756 6462325197086504392123 := by
  unfold tailWord_37756
  simp only [CollatzResearch.WordTrace]
  refine ⟨688537225611967528270561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 918049634149290037694081 688537225611967528270561)
  ·
    refine ⟨516402919208975646202921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 688537225611967528270561 516402919208975646202921)
    ·
      refine ⟨387302189406731734652191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 516402919208975646202921 387302189406731734652191)
      ·
        refine ⟨580953284110097601978287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 387302189406731734652191 580953284110097601978287)
        ·
          refine ⟨871429926165146402967431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 580953284110097601978287 871429926165146402967431)
          ·
            refine ⟨1307144889247719604451147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 871429926165146402967431 1307144889247719604451147)
            ·
              refine ⟨1960717333871579406676721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1307144889247719604451147 1960717333871579406676721)
              ·
                refine ⟨1470538000403684555007541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1960717333871579406676721 1470538000403684555007541)
                ·
                  refine ⟨137862937537845427031957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1470538000403684555007541 137862937537845427031957)
                  ·
                    refine ⟨6462325197086504392123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 137862937537845427031957 6462325197086504392123)
                    ·
                      rfl

theorem cell23_37756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 5, 6].length) (baseStart_37756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_37756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_37756 prefixEnd_37756 := by exact prefixLift 37756
  have htrace : WordTrace (prefixWord ++ tailWord_37756) baseStart_37756 baseEnd_37756 := by
    simpa [prefixWord, tailWord_37756, baseEnd_37756] using wordTrace_append hprefix tailTrace_37756
  have hstable : (prefixWord ++ tailWord_37756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37756).length < 2 ^ (prefixWord ++ tailWord_37756).sum := by decide
  have hdescent : baseEnd_37756 < baseStart_37756 := by decide
  rcases family_descends (prefixWord ++ tailWord_37756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37763 : List Nat := [1, 1, 1, 3, 4, 1, 3, 1, 3, 1, 4]
def baseStart_37763 : Nat := 118140960795 + 37763 * 2 ^ 59
def prefixEnd_37763 : Nat := 4983230072969 + 3 ^ 40 * 37763 * 2
def baseEnd_37763 : Nat := 19390569955840985788837

theorem tailTrace_37763 : CollatzResearch.WordTrace tailWord_37763 prefixEnd_37763 19390569955840985788837 := by
  unfold tailWord_37763
  simp only [CollatzResearch.WordTrace]
  refine ⟨1377329762198575252045943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 918219841465716834697295 1377329762198575252045943)
  ·
    refine ⟨2065994643297862878068915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1377329762198575252045943 2065994643297862878068915)
    ·
      refine ⟨3098991964946794317103373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2065994643297862878068915 3098991964946794317103373)
      ·
        refine ⟨1162121986855047868913765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3098991964946794317103373 1162121986855047868913765)
        ·
          refine ⟨217897872535321475421331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1162121986855047868913765 217897872535321475421331)
          ·
            refine ⟨326846808802982213131997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217897872535321475421331 326846808802982213131997)
            ·
              refine ⟨122567553301118329924499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 326846808802982213131997 122567553301118329924499)
              ·
                refine ⟨183851329951677494886749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 122567553301118329924499 183851329951677494886749)
                ·
                  refine ⟨68944248731879060582531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 183851329951677494886749 68944248731879060582531)
                  ·
                    refine ⟨103416373097818590873797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 68944248731879060582531 103416373097818590873797)
                    ·
                      refine ⟨19390569955840985788837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 103416373097818590873797 19390569955840985788837)
                      ·
                        rfl

theorem cell23_37763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 1, 3, 1, 4].length) (baseStart_37763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_37763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_37763 prefixEnd_37763 := by exact prefixLift 37763
  have htrace : WordTrace (prefixWord ++ tailWord_37763) baseStart_37763 baseEnd_37763 := by
    simpa [prefixWord, tailWord_37763, baseEnd_37763] using wordTrace_append hprefix tailTrace_37763
  have hstable : (prefixWord ++ tailWord_37763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37763).length < 2 ^ (prefixWord ++ tailWord_37763).sum := by decide
  have hdescent : baseEnd_37763 < baseStart_37763 := by decide
  rcases family_descends (prefixWord ++ tailWord_37763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37767 : List Nat := [1, 1, 4, 2, 3, 2, 2, 1, 2, 3, 2]
def baseStart_37767 : Nat := 118140960795 + 37767 * 2 ^ 59
def prefixEnd_37767 : Nat := 4983230072969 + 3 ^ 40 * 37767 * 2
def baseEnd_37767 : Nat := 19392623878458970138819

theorem tailTrace_37767 : CollatzResearch.WordTrace tailWord_37767 prefixEnd_37767 19392623878458970138819 := by
  unfold tailWord_37767
  simp only [CollatzResearch.WordTrace]
  refine ⟨1377475654184083935191555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 918317102789389290127703 1377475654184083935191555)
  ·
    refine ⟨2066213481276125902787333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1377475654184083935191555 2066213481276125902787333)
    ·
      refine ⟨387415027739273606772625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2066213481276125902787333 387415027739273606772625)
      ·
        refine ⟨290561270804455205079469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 387415027739273606772625 290561270804455205079469)
        ·
          refine ⟨108960476551670701904801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 290561270804455205079469 108960476551670701904801)
          ·
            refine ⟨81720357413753026428601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108960476551670701904801 81720357413753026428601)
            ·
              refine ⟨61290268060314769821451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81720357413753026428601 61290268060314769821451)
              ·
                refine ⟨91935402090472154732177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61290268060314769821451 91935402090472154732177)
                ·
                  refine ⟨68951551567854116049133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 91935402090472154732177 68951551567854116049133)
                  ·
                    refine ⟨25856831837945293518425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 68951551567854116049133 25856831837945293518425)
                    ·
                      refine ⟨19392623878458970138819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 25856831837945293518425 19392623878458970138819)
                      ·
                        rfl

theorem cell23_37767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 1, 2, 3, 2].length) (baseStart_37767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_37767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_37767 prefixEnd_37767 := by exact prefixLift 37767
  have htrace : WordTrace (prefixWord ++ tailWord_37767) baseStart_37767 baseEnd_37767 := by
    simpa [prefixWord, tailWord_37767, baseEnd_37767] using wordTrace_append hprefix tailTrace_37767
  have hstable : (prefixWord ++ tailWord_37767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37767).length < 2 ^ (prefixWord ++ tailWord_37767).sum := by decide
  have hdescent : baseEnd_37767 < baseStart_37767 := by decide
  rcases family_descends (prefixWord ++ tailWord_37767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37776 : List Nat := [2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 4]
def baseStart_37776 : Nat := 118140960795 + 37776 * 2 ^ 59
def prefixEnd_37776 : Nat := 4983230072969 + 3 ^ 40 * 37776 * 2
def baseEnd_37776 : Nat := 19397245204349434926277

theorem tailTrace_37776 : CollatzResearch.WordTrace tailWord_37776 prefixEnd_37776 19397245204349434926277 := by
  unfold tailWord_37776
  simp only [CollatzResearch.WordTrace]
  refine ⟨688901955575739236134591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 918535940767652314846121 688901955575739236134591)
  ·
    refine ⟨1033352933363608854201887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 688901955575739236134591 1033352933363608854201887)
    ·
      refine ⟨1550029400045413281302831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1033352933363608854201887 1550029400045413281302831)
      ·
        refine ⟨2325044100068119921954247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1550029400045413281302831 2325044100068119921954247)
        ·
          refine ⟨3487566150102179882931371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2325044100068119921954247 3487566150102179882931371)
          ·
            refine ⟨5231349225153269824397057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3487566150102179882931371 5231349225153269824397057)
            ·
              refine ⟨3923511918864952368297793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5231349225153269824397057 3923511918864952368297793)
              ·
                refine ⟨2942633939148714276223345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3923511918864952368297793 2942633939148714276223345)
                ·
                  refine ⟨2206975454361535707167509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2942633939148714276223345 2206975454361535707167509)
                  ·
                    refine ⟨103451974423196986273477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2206975454361535707167509 103451974423196986273477)
                    ·
                      refine ⟨19397245204349434926277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 103451974423196986273477 19397245204349434926277)
                      ·
                        rfl

theorem cell23_37776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 4].length) (baseStart_37776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_37776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_37776 prefixEnd_37776 := by exact prefixLift 37776
  have htrace : WordTrace (prefixWord ++ tailWord_37776) baseStart_37776 baseEnd_37776 := by
    simpa [prefixWord, tailWord_37776, baseEnd_37776] using wordTrace_append hprefix tailTrace_37776
  have hstable : (prefixWord ++ tailWord_37776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37776).length < 2 ^ (prefixWord ++ tailWord_37776).sum := by decide
  have hdescent : baseEnd_37776 < baseStart_37776 := by decide
  rcases family_descends (prefixWord ++ tailWord_37776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37786 : List Nat := [3, 1, 1, 4, 14]
def baseStart_37786 : Nat := 118140960795 + 37786 * 2 ^ 59
def prefixEnd_37786 : Nat := 4983230072969 + 3 ^ 40 * 37786 * 2
def baseEnd_37786 : Nat := 26615061743339363239

theorem tailTrace_37786 : CollatzResearch.WordTrace tailWord_37786 prefixEnd_37786 26615061743339363239 := by
  unfold tailWord_37786
  simp only [CollatzResearch.WordTrace]
  refine ⟨344542160278812545033303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 918779094076833453422141 344542160278812545033303)
  ·
    refine ⟨516813240418218817549955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 344542160278812545033303 516813240418218817549955)
    ·
      refine ⟨775219860627328226324933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 516813240418218817549955 775219860627328226324933)
      ·
        refine ⟨145353723867624042435925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 775219860627328226324933 145353723867624042435925)
        ·
          refine ⟨26615061743339363239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 145353723867624042435925 26615061743339363239)
          ·
            rfl

theorem cell23_37786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 14].length) (baseStart_37786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_37786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_37786 prefixEnd_37786 := by exact prefixLift 37786
  have htrace : WordTrace (prefixWord ++ tailWord_37786) baseStart_37786 baseEnd_37786 := by
    simpa [prefixWord, tailWord_37786, baseEnd_37786] using wordTrace_append hprefix tailTrace_37786
  have hstable : (prefixWord ++ tailWord_37786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37786).length < 2 ^ (prefixWord ++ tailWord_37786).sum := by decide
  have hdescent : baseEnd_37786 < baseStart_37786 := by decide
  rcases family_descends (prefixWord ++ tailWord_37786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37791 : List Nat := [1, 1, 2, 5, 2, 3, 2, 2, 1, 1, 3]
def baseStart_37791 : Nat := 118140960795 + 37791 * 2 ^ 59
def prefixEnd_37791 : Nat := 4983230072969 + 3 ^ 40 * 37791 * 2
def baseEnd_37791 : Nat := 19404947414166876238709

theorem tailTrace_37791 : CollatzResearch.WordTrace tailWord_37791 prefixEnd_37791 19404947414166876238709 := by
  unfold tailWord_37791
  simp only [CollatzResearch.WordTrace]
  refine ⟨1378351006097136034065227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 918900670731424022710151 1378351006097136034065227)
  ·
    refine ⟨2067526509145704051097841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1378351006097136034065227 2067526509145704051097841)
    ·
      refine ⟨1550644881859278038323381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2067526509145704051097841 1550644881859278038323381)
      ·
        refine ⟨145372957674307316092817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1550644881859278038323381 145372957674307316092817)
        ·
          refine ⟨109029718255730487069613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145372957674307316092817 109029718255730487069613)
          ·
            refine ⟨40886144345898932651105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109029718255730487069613 40886144345898932651105)
            ·
              refine ⟨30664608259424199488329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40886144345898932651105 30664608259424199488329)
              ·
                refine ⟨22998456194568149616247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30664608259424199488329 22998456194568149616247)
                ·
                  refine ⟨34497684291852224424371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22998456194568149616247 34497684291852224424371)
                  ·
                    refine ⟨51746526437778336636557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34497684291852224424371 51746526437778336636557)
                    ·
                      refine ⟨19404947414166876238709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 51746526437778336636557 19404947414166876238709)
                      ·
                        rfl

theorem cell23_37791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 2, 2, 1, 1, 3].length) (baseStart_37791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_37791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_37791 prefixEnd_37791 := by exact prefixLift 37791
  have htrace : WordTrace (prefixWord ++ tailWord_37791) baseStart_37791 baseEnd_37791 := by
    simpa [prefixWord, tailWord_37791, baseEnd_37791] using wordTrace_append hprefix tailTrace_37791
  have hstable : (prefixWord ++ tailWord_37791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37791).length < 2 ^ (prefixWord ++ tailWord_37791).sum := by decide
  have hdescent : baseEnd_37791 < baseStart_37791 := by decide
  rcases family_descends (prefixWord ++ tailWord_37791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37903 : List Nat := [1, 1, 2, 1, 1, 1, 2, 1, 5, 5, 3]
def baseStart_37903 : Nat := 118140960795 + 37903 * 2 ^ 59
def prefixEnd_37903 : Nat := 4983230072969 + 3 ^ 40 * 37903 * 2
def baseEnd_37903 : Nat := 19462457247470438038193

theorem tailTrace_37903 : CollatzResearch.WordTrace tailWord_37903 prefixEnd_37903 19462457247470438038193 := by
  unfold tailWord_37903
  simp only [CollatzResearch.WordTrace]
  refine ⟨1382435981691379162142363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 921623987794252774761575 1382435981691379162142363)
  ·
    refine ⟨2073653972537068743213545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1382435981691379162142363 2073653972537068743213545)
    ·
      refine ⟨1555240479402801557410159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2073653972537068743213545 1555240479402801557410159)
      ·
        refine ⟨2332860719104202336115239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1555240479402801557410159 2332860719104202336115239)
        ·
          refine ⟨3499291078656303504172859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2332860719104202336115239 3499291078656303504172859)
          ·
            refine ⟨5248936617984455256259289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3499291078656303504172859 5248936617984455256259289)
            ·
              refine ⟨3936702463488341442194467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5248936617984455256259289 3936702463488341442194467)
              ·
                refine ⟨5905053695232512163291701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3936702463488341442194467 5905053695232512163291701)
                ·
                  refine ⟨553598783928048015308597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5905053695232512163291701 553598783928048015308597)
                  ·
                    refine ⟨51899885993254501435181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 553598783928048015308597 51899885993254501435181)
                    ·
                      refine ⟨19462457247470438038193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 51899885993254501435181 19462457247470438038193)
                      ·
                        rfl

theorem cell23_37903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 5, 3].length) (baseStart_37903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_37903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_37903 prefixEnd_37903 := by exact prefixLift 37903
  have htrace : WordTrace (prefixWord ++ tailWord_37903) baseStart_37903 baseEnd_37903 := by
    simpa [prefixWord, tailWord_37903, baseEnd_37903] using wordTrace_append hprefix tailTrace_37903
  have hstable : (prefixWord ++ tailWord_37903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37903).length < 2 ^ (prefixWord ++ tailWord_37903).sum := by decide
  have hdescent : baseEnd_37903 < baseStart_37903 := by decide
  rcases family_descends (prefixWord ++ tailWord_37903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37921 : List Nat := [1, 2, 3, 2, 3, 1, 4, 1, 2, 2, 2]
def baseStart_37921 : Nat := 118140960795 + 37921 * 2 ^ 59
def prefixEnd_37921 : Nat := 4983230072969 + 3 ^ 40 * 37921 * 2
def baseEnd_37921 : Nat := 19471699899251367613111

theorem tailTrace_37921 : CollatzResearch.WordTrace tailWord_37921 prefixEnd_37921 19471699899251367613111 := by
  unfold tailWord_37921
  simp only [CollatzResearch.WordTrace]
  refine ⟨1383092495626168236297617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 922061663750778824198411 1383092495626168236297617)
  ·
    refine ⟨1037319371719626177223213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1383092495626168236297617 1037319371719626177223213)
    ·
      refine ⟨388994764394859816458705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1037319371719626177223213 388994764394859816458705)
      ·
        refine ⟨291746073296144862344029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 388994764394859816458705 291746073296144862344029)
        ·
          refine ⟨109404777486054323379011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 291746073296144862344029 109404777486054323379011)
          ·
            refine ⟨164107166229081485068517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109404777486054323379011 164107166229081485068517)
            ·
              refine ⟨30770093667952778450347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 164107166229081485068517 30770093667952778450347)
              ·
                refine ⟨46155140501929167675521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30770093667952778450347 46155140501929167675521)
                ·
                  refine ⟨34616355376446875756641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46155140501929167675521 34616355376446875756641)
                  ·
                    refine ⟨25962266532335156817481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34616355376446875756641 25962266532335156817481)
                    ·
                      refine ⟨19471699899251367613111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 25962266532335156817481 19471699899251367613111)
                      ·
                        rfl

theorem cell23_37921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 4, 1, 2, 2, 2].length) (baseStart_37921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_37921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_37921 prefixEnd_37921 := by exact prefixLift 37921
  have htrace : WordTrace (prefixWord ++ tailWord_37921) baseStart_37921 baseEnd_37921 := by
    simpa [prefixWord, tailWord_37921, baseEnd_37921] using wordTrace_append hprefix tailTrace_37921
  have hstable : (prefixWord ++ tailWord_37921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37921).length < 2 ^ (prefixWord ++ tailWord_37921).sum := by decide
  have hdescent : baseEnd_37921 < baseStart_37921 := by decide
  rcases family_descends (prefixWord ++ tailWord_37921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37960 : List Nat := [2, 1, 3, 1, 1, 1, 3, 4, 2, 1, 4]
def baseStart_37960 : Nat := 118140960795 + 37960 * 2 ^ 59
def prefixEnd_37960 : Nat := 4983230072969 + 3 ^ 40 * 37960 * 2
def baseEnd_37960 : Nat := 19491725644776715025431

theorem tailTrace_37960 : CollatzResearch.WordTrace tailWord_37960 prefixEnd_37960 19491725644776715025431 := by
  unfold tailWord_37960
  simp only [CollatzResearch.WordTrace]
  refine ⟨692257471242438948483667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 923009961656585264644889 692257471242438948483667)
  ·
    refine ⟨1038386206863658422725501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 692257471242438948483667 1038386206863658422725501)
    ·
      refine ⟨389394827573871908522063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1038386206863658422725501 389394827573871908522063)
      ·
        refine ⟨584092241360807862783095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 389394827573871908522063 584092241360807862783095)
        ·
          refine ⟨876138362041211794174643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 584092241360807862783095 876138362041211794174643)
          ·
            refine ⟨1314207543061817691261965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 876138362041211794174643 1314207543061817691261965)
            ·
              refine ⟨492827828648181634223237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1314207543061817691261965 492827828648181634223237)
              ·
                refine ⟨92405217871534056416857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 492827828648181634223237 92405217871534056416857)
                ·
                  refine ⟨69303913403650542312643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 92405217871534056416857 69303913403650542312643)
                  ·
                    refine ⟨103955870105475813468965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 69303913403650542312643 103955870105475813468965)
                    ·
                      refine ⟨19491725644776715025431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 103955870105475813468965 19491725644776715025431)
                      ·
                        rfl

theorem cell23_37960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 4, 2, 1, 4].length) (baseStart_37960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_37960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_37960 prefixEnd_37960 := by exact prefixLift 37960
  have htrace : WordTrace (prefixWord ++ tailWord_37960) baseStart_37960 baseEnd_37960 := by
    simpa [prefixWord, tailWord_37960, baseEnd_37960] using wordTrace_append hprefix tailTrace_37960
  have hstable : (prefixWord ++ tailWord_37960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37960).length < 2 ^ (prefixWord ++ tailWord_37960).sum := by decide
  have hdescent : baseEnd_37960 < baseStart_37960 := by decide
  rcases family_descends (prefixWord ++ tailWord_37960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37994 : List Nat := [3, 1, 3, 2, 2, 3, 1, 1, 2, 1, 4]
def baseStart_37994 : Nat := 118140960795 + 37994 * 2 ^ 59
def prefixEnd_37994 : Nat := 4983230072969 + 3 ^ 40 * 37994 * 2
def baseEnd_37994 : Nat := 19509183987029582000275

theorem tailTrace_37994 : CollatzResearch.WordTrace tailWord_37994 prefixEnd_37994 19509183987029582000275 := by
  unfold tailWord_37994
  simp only [CollatzResearch.WordTrace]
  refine ⟨346438756090425425926259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 923836682907801135803357 346438756090425425926259)
  ·
    refine ⟨519658134135638138889389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 346438756090425425926259 519658134135638138889389)
    ·
      refine ⟨194871800300864302083521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 519658134135638138889389 194871800300864302083521)
      ·
        refine ⟨146153850225648226562641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194871800300864302083521 146153850225648226562641)
        ·
          refine ⟨109615387669236169921981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146153850225648226562641 109615387669236169921981)
          ·
            refine ⟨41105770375963563720743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109615387669236169921981 41105770375963563720743)
            ·
              refine ⟨61658655563945345581115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41105770375963563720743 61658655563945345581115)
              ·
                refine ⟨92487983345918018371673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61658655563945345581115 92487983345918018371673)
                ·
                  refine ⟨69365987509438513778755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 92487983345918018371673 69365987509438513778755)
                  ·
                    refine ⟨104048981264157770668133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 69365987509438513778755 104048981264157770668133)
                    ·
                      refine ⟨19509183987029582000275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 104048981264157770668133 19509183987029582000275)
                      ·
                        rfl

theorem cell23_37994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_37994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_37994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_37994 prefixEnd_37994 := by exact prefixLift 37994
  have htrace : WordTrace (prefixWord ++ tailWord_37994) baseStart_37994 baseEnd_37994 := by
    simpa [prefixWord, tailWord_37994, baseEnd_37994] using wordTrace_append hprefix tailTrace_37994
  have hstable : (prefixWord ++ tailWord_37994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37994).length < 2 ^ (prefixWord ++ tailWord_37994).sum := by decide
  have hdescent : baseEnd_37994 < baseStart_37994 := by decide
  rcases family_descends (prefixWord ++ tailWord_37994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_37997 : List Nat := [1, 5, 1, 1, 2, 3, 1, 1, 1, 4, 3]
def baseStart_37997 : Nat := 118140960795 + 37997 * 2 ^ 59
def prefixEnd_37997 : Nat := 4983230072969 + 3 ^ 40 * 37997 * 2
def baseEnd_37997 : Nat := 19510724428993070262761

theorem tailTrace_37997 : CollatzResearch.WordTrace tailWord_37997 prefixEnd_37997 19510724428993070262761 := by
  unfold tailWord_37997
  simp only [CollatzResearch.WordTrace]
  refine ⟨1385864443350833216064245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 923909628900555477376163 1385864443350833216064245)
  ·
    refine ⟨129924791564140614006023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1385864443350833216064245 129924791564140614006023)
    ·
      refine ⟨194887187346210921009035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129924791564140614006023 194887187346210921009035)
      ·
        refine ⟨292330781019316381513553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194887187346210921009035 292330781019316381513553)
        ·
          refine ⟨219248085764487286135165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 292330781019316381513553 219248085764487286135165)
          ·
            refine ⟨82218032161682732300687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 219248085764487286135165 82218032161682732300687)
            ·
              refine ⟨123327048242524098451031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82218032161682732300687 123327048242524098451031)
              ·
                refine ⟨184990572363786147676547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123327048242524098451031 184990572363786147676547)
                ·
                  refine ⟨277485858545679221514821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 184990572363786147676547 277485858545679221514821)
                  ·
                    refine ⟨52028598477314854034029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 277485858545679221514821 52028598477314854034029)
                    ·
                      refine ⟨19510724428993070262761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 52028598477314854034029 19510724428993070262761)
                      ·
                        rfl

theorem cell23_37997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 1, 1, 4, 3].length) (baseStart_37997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_37997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_37997 prefixEnd_37997 := by exact prefixLift 37997
  have htrace : WordTrace (prefixWord ++ tailWord_37997) baseStart_37997 baseEnd_37997 := by
    simpa [prefixWord, tailWord_37997, baseEnd_37997] using wordTrace_append hprefix tailTrace_37997
  have hstable : (prefixWord ++ tailWord_37997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_37997).length < 2 ^ (prefixWord ++ tailWord_37997).sum := by decide
  have hdescent : baseEnd_37997 < baseStart_37997 := by decide
  rcases family_descends (prefixWord ++ tailWord_37997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38003 : List Nat := [1, 1, 1, 2, 2, 1, 1, 1, 5, 2, 6]
def baseStart_38003 : Nat := 118140960795 + 38003 * 2 ^ 59
def prefixEnd_38003 : Nat := 4983230072969 + 3 ^ 40 * 38003 * 2
def baseEnd_38003 : Nat := 19513805312920046787733

theorem tailTrace_38003 : CollatzResearch.WordTrace tailWord_38003 prefixEnd_38003 19513805312920046787733 := by
  unfold tailWord_38003
  simp only [CollatzResearch.WordTrace]
  refine ⟨1386083281329096240782663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 924055520886064160521775 1386083281329096240782663)
  ·
    refine ⟨2079124921993644361173995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1386083281329096240782663 2079124921993644361173995)
    ·
      refine ⟨3118687382990466541760993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2079124921993644361173995 3118687382990466541760993)
      ·
        refine ⟨2339015537242849906320745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3118687382990466541760993 2339015537242849906320745)
        ·
          refine ⟨1754261652932137429740559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2339015537242849906320745 1754261652932137429740559)
          ·
            refine ⟨2631392479398206144610839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1754261652932137429740559 2631392479398206144610839)
            ·
              refine ⟨3947088719097309216916259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2631392479398206144610839 3947088719097309216916259)
              ·
                refine ⟨5920633078645963825374389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3947088719097309216916259 5920633078645963825374389)
                ·
                  refine ⟨555059351123059108628849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5920633078645963825374389 555059351123059108628849)
                  ·
                    refine ⟨416294513342294331471637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 555059351123059108628849 416294513342294331471637)
                    ·
                      refine ⟨19513805312920046787733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 416294513342294331471637 19513805312920046787733)
                      ·
                        rfl

theorem cell23_38003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 2, 6].length) (baseStart_38003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_38003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_38003 prefixEnd_38003 := by exact prefixLift 38003
  have htrace : WordTrace (prefixWord ++ tailWord_38003) baseStart_38003 baseEnd_38003 := by
    simpa [prefixWord, tailWord_38003, baseEnd_38003] using wordTrace_append hprefix tailTrace_38003
  have hstable : (prefixWord ++ tailWord_38003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38003).length < 2 ^ (prefixWord ++ tailWord_38003).sum := by decide
  have hdescent : baseEnd_38003 < baseStart_38003 := by decide
  rcases family_descends (prefixWord ++ tailWord_38003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38017 : List Nat := [1, 2, 4, 2, 2, 1, 3, 2, 6]
def baseStart_38017 : Nat := 118140960795 + 38017 * 2 ^ 59
def prefixEnd_38017 : Nat := 4983230072969 + 3 ^ 40 * 38017 * 2
def baseEnd_38017 : Nat := 2168999338009221334741

theorem tailTrace_38017 : CollatzResearch.WordTrace tailWord_38017 prefixEnd_38017 2168999338009221334741 := by
  unfold tailWord_38017
  simp only [CollatzResearch.WordTrace]
  refine ⟨1386593903278376631792305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 924395935518917754528203 1386593903278376631792305)
  ·
    refine ⟨1039945427458782473844229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1386593903278376631792305 1039945427458782473844229)
    ·
      refine ⟨194989767648521713845793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1039945427458782473844229 194989767648521713845793)
      ·
        refine ⟨146242325736391285384345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194989767648521713845793 146242325736391285384345)
        ·
          refine ⟨109681744302293464038259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146242325736391285384345 109681744302293464038259)
          ·
            refine ⟨164522616453440196057389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109681744302293464038259 164522616453440196057389)
            ·
              refine ⟨61695981170040073521521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 164522616453440196057389 61695981170040073521521)
              ·
                refine ⟨46271985877530055141141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61695981170040073521521 46271985877530055141141)
                ·
                  refine ⟨2168999338009221334741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 46271985877530055141141 2168999338009221334741)
                  ·
                    rfl

theorem cell23_38017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 2, 6].length) (baseStart_38017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_38017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_38017 prefixEnd_38017 := by exact prefixLift 38017
  have htrace : WordTrace (prefixWord ++ tailWord_38017) baseStart_38017 baseEnd_38017 := by
    simpa [prefixWord, tailWord_38017, baseEnd_38017] using wordTrace_append hprefix tailTrace_38017
  have hstable : (prefixWord ++ tailWord_38017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38017).length < 2 ^ (prefixWord ++ tailWord_38017).sum := by decide
  have hdescent : baseEnd_38017 < baseStart_38017 := by decide
  rcases family_descends (prefixWord ++ tailWord_38017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38020 : List Nat := [2, 3, 2, 1, 2, 2, 1, 1, 1, 2, 6]
def baseStart_38020 : Nat := 118140960795 + 38020 * 2 ^ 59
def prefixEnd_38020 : Nat := 4983230072969 + 3 ^ 40 * 38020 * 2
def baseEnd_38020 : Nat := 19522534484046480275155

theorem tailTrace_38020 : CollatzResearch.WordTrace tailWord_38020 prefixEnd_38020 19522534484046480275155 := by
  unfold tailWord_38020
  simp only [CollatzResearch.WordTrace]
  refine ⟨693351661133754072075757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 924468881511672096101009 693351661133754072075757)
  ·
    refine ⟨260006872925157777028409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 693351661133754072075757 260006872925157777028409)
    ·
      refine ⟨195005154693868332771307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 260006872925157777028409 195005154693868332771307)
      ·
        refine ⟨292507732040802499156961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195005154693868332771307 292507732040802499156961)
        ·
          refine ⟨219380799030601874367721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 292507732040802499156961 219380799030601874367721)
          ·
            refine ⟨164535599272951405775791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 219380799030601874367721 164535599272951405775791)
            ·
              refine ⟨246803398909427108663687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164535599272951405775791 246803398909427108663687)
              ·
                refine ⟨370205098364140662995531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 246803398909427108663687 370205098364140662995531)
                ·
                  refine ⟨555307647546210994493297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 370205098364140662995531 555307647546210994493297)
                  ·
                    refine ⟨416480735659658245869973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 555307647546210994493297 416480735659658245869973)
                    ·
                      refine ⟨19522534484046480275155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 416480735659658245869973 19522534484046480275155)
                      ·
                        rfl

theorem cell23_38020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_38020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_38020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_38020 prefixEnd_38020 := by exact prefixLift 38020
  have htrace : WordTrace (prefixWord ++ tailWord_38020) baseStart_38020 baseEnd_38020 := by
    simpa [prefixWord, tailWord_38020, baseEnd_38020] using wordTrace_append hprefix tailTrace_38020
  have hstable : (prefixWord ++ tailWord_38020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38020).length < 2 ^ (prefixWord ++ tailWord_38020).sum := by decide
  have hdescent : baseEnd_38020 < baseStart_38020 := by decide
  rcases family_descends (prefixWord ++ tailWord_38020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38034 : List Nat := [3, 2, 3, 1, 1, 3, 3, 1, 6]
def baseStart_38034 : Nat := 118140960795 + 38034 * 2 ^ 59
def prefixEnd_38034 : Nat := 4983230072969 + 3 ^ 40 * 38034 * 2
def baseEnd_38034 : Nat := 2169969245912158388899

theorem tailTrace_38034 : CollatzResearch.WordTrace tailWord_38034 prefixEnd_38034 2169969245912158388899 := by
  unfold tailWord_38034
  simp only [CollatzResearch.WordTrace]
  refine ⟨346803486054197133790289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 924809296144525690107437 346803486054197133790289)
  ·
    refine ⟨260102614540647850342717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 346803486054197133790289 260102614540647850342717)
    ·
      refine ⟨97538480452742943878519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 260102614540647850342717 97538480452742943878519)
      ·
        refine ⟨146307720679114415817779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97538480452742943878519 146307720679114415817779)
        ·
          refine ⟨219461581018671623726669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146307720679114415817779 219461581018671623726669)
          ·
            refine ⟨82298092882001858897501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 219461581018671623726669 82298092882001858897501)
            ·
              refine ⟨30861784830750697086563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82298092882001858897501 30861784830750697086563)
              ·
                refine ⟨46292677246126045629845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30861784830750697086563 46292677246126045629845)
                ·
                  refine ⟨2169969245912158388899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 46292677246126045629845 2169969245912158388899)
                  ·
                    rfl

theorem cell23_38034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 3, 1, 6].length) (baseStart_38034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_38034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_38034 prefixEnd_38034 := by exact prefixLift 38034
  have htrace : WordTrace (prefixWord ++ tailWord_38034) baseStart_38034 baseEnd_38034 := by
    simpa [prefixWord, tailWord_38034, baseEnd_38034] using wordTrace_append hprefix tailTrace_38034
  have hstable : (prefixWord ++ tailWord_38034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38034).length < 2 ^ (prefixWord ++ tailWord_38034).sum := by decide
  have hdescent : baseEnd_38034 < baseStart_38034 := by decide
  rcases family_descends (prefixWord ++ tailWord_38034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38037 : List Nat := [1, 3, 2, 1, 1, 1, 2, 1, 6, 3, 2]
def baseStart_38037 : Nat := 118140960795 + 38037 * 2 ^ 59
def prefixEnd_38037 : Nat := 4983230072969 + 3 ^ 40 * 38037 * 2
def baseEnd_38037 : Nat := 19531263655172913762577

theorem tailTrace_38037 : CollatzResearch.WordTrace tailWord_38037 prefixEnd_38037 19531263655172913762577 := by
  unfold tailWord_38037
  simp only [CollatzResearch.WordTrace]
  refine ⟨1387323363205920047520365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 924882242137280031680243 1387323363205920047520365)
  ·
    refine ⟨520246261202220017820137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1387323363205920047520365 520246261202220017820137)
    ·
      refine ⟨390184695901665013365103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 520246261202220017820137 390184695901665013365103)
      ·
        refine ⟨585277043852497520047655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 390184695901665013365103 585277043852497520047655)
        ·
          refine ⟨877915565778746280071483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 585277043852497520047655 877915565778746280071483)
          ·
            refine ⟨1316873348668119420107225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 877915565778746280071483 1316873348668119420107225)
            ·
              refine ⟨987655011501089565080419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1316873348668119420107225 987655011501089565080419)
              ·
                refine ⟨1481482517251634347620629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 987655011501089565080419 1481482517251634347620629)
                ·
                  refine ⟨69444492996170360044717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1481482517251634347620629 69444492996170360044717)
                  ·
                    refine ⟨26041684873563885016769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 69444492996170360044717 26041684873563885016769)
                    ·
                      refine ⟨19531263655172913762577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 26041684873563885016769 19531263655172913762577)
                      ·
                        rfl

theorem cell23_38037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 6, 3, 2].length) (baseStart_38037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_38037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_38037 prefixEnd_38037 := by exact prefixLift 38037
  have htrace : WordTrace (prefixWord ++ tailWord_38037) baseStart_38037 baseEnd_38037 := by
    simpa [prefixWord, tailWord_38037, baseEnd_38037] using wordTrace_append hprefix tailTrace_38037
  have hstable : (prefixWord ++ tailWord_38037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38037).length < 2 ^ (prefixWord ++ tailWord_38037).sum := by decide
  have hdescent : baseEnd_38037 < baseStart_38037 := by decide
  rcases family_descends (prefixWord ++ tailWord_38037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38044 : List Nat := [2, 2, 3, 2, 1, 2, 2, 2, 3, 1, 3]
def baseStart_38044 : Nat := 118140960795 + 38044 * 2 ^ 59
def prefixEnd_38044 : Nat := 4983230072969 + 3 ^ 40 * 38044 * 2
def baseEnd_38044 : Nat := 19534858019754386375045

theorem tailTrace_38044 : CollatzResearch.WordTrace tailWord_38044 prefixEnd_38044 19534858019754386375045 := by
  unfold tailWord_38044
  simp only [CollatzResearch.WordTrace]
  refine ⟨693789337090280121512593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 925052449453706828683457 693789337090280121512593)
  ·
    refine ⟨520342002817710091134445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 693789337090280121512593 520342002817710091134445)
    ·
      refine ⟨195128251056641284175417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 520342002817710091134445 195128251056641284175417)
      ·
        refine ⟨146346188292480963131563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195128251056641284175417 146346188292480963131563)
        ·
          refine ⟨219519282438721444697345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146346188292480963131563 219519282438721444697345)
          ·
            refine ⟨164639461829041083523009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 219519282438721444697345 164639461829041083523009)
            ·
              refine ⟨123479596371780812642257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 164639461829041083523009 123479596371780812642257)
              ·
                refine ⟨92609697278835609481693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 123479596371780812642257 92609697278835609481693)
                ·
                  refine ⟨34728636479563353555635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 92609697278835609481693 34728636479563353555635)
                  ·
                    refine ⟨52092954719345030333453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34728636479563353555635 52092954719345030333453)
                    ·
                      refine ⟨19534858019754386375045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 52092954719345030333453 19534858019754386375045)
                      ·
                        rfl

theorem cell23_38044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_38044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_38044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_38044 prefixEnd_38044 := by exact prefixLift 38044
  have htrace : WordTrace (prefixWord ++ tailWord_38044) baseStart_38044 baseEnd_38044 := by
    simpa [prefixWord, tailWord_38044, baseEnd_38044] using wordTrace_append hprefix tailTrace_38044
  have hstable : (prefixWord ++ tailWord_38044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38044).length < 2 ^ (prefixWord ++ tailWord_38044).sum := by decide
  have hdescent : baseEnd_38044 < baseStart_38044 := by decide
  rcases family_descends (prefixWord ++ tailWord_38044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38067 : List Nat := [1, 1, 1, 2, 3, 2, 4, 3, 1, 1, 4]
def baseStart_38067 : Nat := 118140960795 + 38067 * 2 ^ 59
def prefixEnd_38067 : Nat := 4983230072969 + 3 ^ 40 * 38067 * 2
def baseEnd_38067 : Nat := 19546668074807796387439

theorem tailTrace_38067 : CollatzResearch.WordTrace tailWord_38067 prefixEnd_38067 19546668074807796387439 := by
  unfold tailWord_38067
  simp only [CollatzResearch.WordTrace]
  refine ⟨1388417553097235171112455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 925611702064823447408303 1388417553097235171112455)
  ·
    refine ⟨2082626329645852756668683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1388417553097235171112455 2082626329645852756668683)
    ·
      refine ⟨3123939494468779135003025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2082626329645852756668683 3123939494468779135003025)
      ·
        refine ⟨2342954620851584351252269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3123939494468779135003025 2342954620851584351252269)
        ·
          refine ⟨878607982819344131719601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2342954620851584351252269 878607982819344131719601)
          ·
            refine ⟨658955987114508098789701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 878607982819344131719601 658955987114508098789701)
            ·
              refine ⟨123554247583970268523069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 658955987114508098789701 123554247583970268523069)
              ·
                refine ⟨46332842843988850696151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 123554247583970268523069 46332842843988850696151)
                ·
                  refine ⟨69499264265983276044227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46332842843988850696151 69499264265983276044227)
                  ·
                    refine ⟨104248896398974914066341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 69499264265983276044227 104248896398974914066341)
                    ·
                      refine ⟨19546668074807796387439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 104248896398974914066341 19546668074807796387439)
                      ·
                        rfl

theorem cell23_38067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 3, 1, 1, 4].length) (baseStart_38067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_38067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_38067 prefixEnd_38067 := by exact prefixLift 38067
  have htrace : WordTrace (prefixWord ++ tailWord_38067) baseStart_38067 baseEnd_38067 := by
    simpa [prefixWord, tailWord_38067, baseEnd_38067] using wordTrace_append hprefix tailTrace_38067
  have hstable : (prefixWord ++ tailWord_38067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38067).length < 2 ^ (prefixWord ++ tailWord_38067).sum := by decide
  have hdescent : baseEnd_38067 < baseStart_38067 := by decide
  rcases family_descends (prefixWord ++ tailWord_38067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38077 : List Nat := [1, 4, 1, 2, 1, 1, 4, 1, 4, 4]
def baseStart_38077 : Nat := 118140960795 + 38077 * 2 ^ 59
def prefixEnd_38077 : Nat := 4983230072969 + 3 ^ 40 * 38077 * 2
def baseEnd_38077 : Nat := 6517267627117585754131

theorem tailTrace_38077 : CollatzResearch.WordTrace tailWord_38077 prefixEnd_38077 6517267627117585754131 := by
  unfold tailWord_38077
  simp only [CollatzResearch.WordTrace]
  refine ⟨1388782283061006878976485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 925854855374004585984323 1388782283061006878976485)
  ·
    refine ⟨260396678073938789808091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1388782283061006878976485 260396678073938789808091)
    ·
      refine ⟨390595017110908184712137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 260396678073938789808091 390595017110908184712137)
      ·
        refine ⟨292946262833181138534103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 390595017110908184712137 292946262833181138534103)
        ·
          refine ⟨439419394249771707801155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 292946262833181138534103 439419394249771707801155)
          ·
            refine ⟨659129091374657561701733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 439419394249771707801155 659129091374657561701733)
            ·
              refine ⟨123586704632748292819075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 659129091374657561701733 123586704632748292819075)
              ·
                refine ⟨185380056949122439228613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123586704632748292819075 185380056949122439228613)
                ·
                  refine ⟨34758760677960457355365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 185380056949122439228613 34758760677960457355365)
                  ·
                    refine ⟨6517267627117585754131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34758760677960457355365 6517267627117585754131)
                    ·
                      rfl

theorem cell23_38077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 1, 4, 4].length) (baseStart_38077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_38077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_38077 prefixEnd_38077 := by exact prefixLift 38077
  have htrace : WordTrace (prefixWord ++ tailWord_38077) baseStart_38077 baseEnd_38077 := by
    simpa [prefixWord, tailWord_38077, baseEnd_38077] using wordTrace_append hprefix tailTrace_38077
  have hstable : (prefixWord ++ tailWord_38077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38077).length < 2 ^ (prefixWord ++ tailWord_38077).sum := by decide
  have hdescent : baseEnd_38077 < baseStart_38077 := by decide
  rcases family_descends (prefixWord ++ tailWord_38077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38090 : List Nat := [3, 1, 2, 1, 3, 2, 1, 10]
def baseStart_38090 : Nat := 118140960795 + 38090 * 2 ^ 59
def prefixEnd_38090 : Nat := 4983230072969 + 3 ^ 40 * 38090 * 2
def baseEnd_38090 : Nat := 724388078883748385179

theorem tailTrace_38090 : CollatzResearch.WordTrace tailWord_38090 prefixEnd_38090 724388078883748385179 := by
  unfold tailWord_38090
  simp only [CollatzResearch.WordTrace]
  refine ⟨347314108003477524799931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 926170954675940066133149 347314108003477524799931)
  ·
    refine ⟨520971162005216287199897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 347314108003477524799931 520971162005216287199897)
    ·
      refine ⟨390728371503912215399923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 520971162005216287199897 390728371503912215399923)
      ·
        refine ⟨586092557255868323099885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 390728371503912215399923 586092557255868323099885)
        ·
          refine ⟨219784708970950621162457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 586092557255868323099885 219784708970950621162457)
          ·
            refine ⟨164838531728212965871843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 219784708970950621162457 164838531728212965871843)
            ·
              refine ⟨247257797592319448807765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164838531728212965871843 247257797592319448807765)
              ·
                refine ⟨724388078883748385179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 247257797592319448807765 724388078883748385179)
                ·
                  rfl

theorem cell23_38090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 10].length) (baseStart_38090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_38090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_38090 prefixEnd_38090 := by exact prefixLift 38090
  have htrace : WordTrace (prefixWord ++ tailWord_38090) baseStart_38090 baseEnd_38090 := by
    simpa [prefixWord, tailWord_38090, baseEnd_38090] using wordTrace_append hprefix tailTrace_38090
  have hstable : (prefixWord ++ tailWord_38090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38090).length < 2 ^ (prefixWord ++ tailWord_38090).sum := by decide
  have hdescent : baseEnd_38090 < baseStart_38090 := by decide
  rcases family_descends (prefixWord ++ tailWord_38090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38101 : List Nat := [1, 3, 2, 4, 1, 3, 1, 2, 1, 1, 4]
def baseStart_38101 : Nat := 118140960795 + 38101 * 2 ^ 59
def prefixEnd_38101 : Nat := 4983230072969 + 3 ^ 40 * 38101 * 2
def baseEnd_38101 : Nat := 19564126417060663362283

theorem tailTrace_38101 : CollatzResearch.WordTrace tailWord_38101 prefixEnd_38101 19564126417060663362283 := by
  unfold tailWord_38101
  simp only [CollatzResearch.WordTrace]
  refine ⟨1389657634974058977850157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 926438423316039318566771 1389657634974058977850157)
  ·
    refine ⟨521121613115272116693809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1389657634974058977850157 521121613115272116693809)
    ·
      refine ⟨390841209836454087520357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 521121613115272116693809 390841209836454087520357)
      ·
        refine ⟨73282726844335141410067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 390841209836454087520357 73282726844335141410067)
        ·
          refine ⟨109924090266502712115101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73282726844335141410067 109924090266502712115101)
          ·
            refine ⟨41221533849938517043163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109924090266502712115101 41221533849938517043163)
            ·
              refine ⟨61832300774907775564745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41221533849938517043163 61832300774907775564745)
              ·
                refine ⟨46374225581180831673559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61832300774907775564745 46374225581180831673559)
                ·
                  refine ⟨69561338371771247510339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46374225581180831673559 69561338371771247510339)
                  ·
                    refine ⟨104342007557656871265509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 69561338371771247510339 104342007557656871265509)
                    ·
                      refine ⟨19564126417060663362283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 104342007557656871265509 19564126417060663362283)
                      ·
                        rfl

theorem cell23_38101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_38101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_38101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_38101 prefixEnd_38101 := by exact prefixLift 38101
  have htrace : WordTrace (prefixWord ++ tailWord_38101) baseStart_38101 baseEnd_38101 := by
    simpa [prefixWord, tailWord_38101, baseEnd_38101] using wordTrace_append hprefix tailTrace_38101
  have hstable : (prefixWord ++ tailWord_38101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38101).length < 2 ^ (prefixWord ++ tailWord_38101).sum := by decide
  have hdescent : baseEnd_38101 < baseStart_38101 := by decide
  rcases family_descends (prefixWord ++ tailWord_38101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38104 : List Nat := [2, 1, 2, 2, 5, 1, 1, 1, 3, 2, 3]
def baseStart_38104 : Nat := 118140960795 + 38104 * 2 ^ 59
def prefixEnd_38104 : Nat := 4983230072969 + 3 ^ 40 * 38104 * 2
def baseEnd_38104 : Nat := 19565666859024151624769

theorem tailTrace_38104 : CollatzResearch.WordTrace tailWord_38104 prefixEnd_38104 19565666859024151624769 := by
  unfold tailWord_38104
  simp only [CollatzResearch.WordTrace]
  refine ⟨694883526981595245104683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 926511369308793660139577 694883526981595245104683)
  ·
    refine ⟨1042325290472392867657025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 694883526981595245104683 1042325290472392867657025)
    ·
      refine ⟨781743967854294650742769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1042325290472392867657025 781743967854294650742769)
      ·
        refine ⟨586307975890720988057077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 781743967854294650742769 586307975890720988057077)
        ·
          refine ⟨54966372739755092630351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 586307975890720988057077 54966372739755092630351)
          ·
            refine ⟨82449559109632638945527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54966372739755092630351 82449559109632638945527)
            ·
              refine ⟨123674338664448958418291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82449559109632638945527 123674338664448958418291)
              ·
                refine ⟨185511507996673437627437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 123674338664448958418291 185511507996673437627437)
                ·
                  refine ⟨69566815498752539110289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 185511507996673437627437 69566815498752539110289)
                  ·
                    refine ⟨52175111624064404332717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 69566815498752539110289 52175111624064404332717)
                    ·
                      refine ⟨19565666859024151624769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 52175111624064404332717 19565666859024151624769)
                      ·
                        rfl

theorem cell23_38104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 1, 3, 2, 3].length) (baseStart_38104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_38104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_38104 prefixEnd_38104 := by exact prefixLift 38104
  have htrace : WordTrace (prefixWord ++ tailWord_38104) baseStart_38104 baseEnd_38104 := by
    simpa [prefixWord, tailWord_38104, baseEnd_38104] using wordTrace_append hprefix tailTrace_38104
  have hstable : (prefixWord ++ tailWord_38104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38104).length < 2 ^ (prefixWord ++ tailWord_38104).sum := by decide
  have hdescent : baseEnd_38104 < baseStart_38104 := by decide
  rcases family_descends (prefixWord ++ tailWord_38104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38178 : List Nat := [3, 3, 1, 1, 4, 1, 1, 3, 1, 3, 2]
def baseStart_38178 : Nat := 118140960795 + 38178 * 2 ^ 59
def prefixEnd_38178 : Nat := 4983230072969 + 3 ^ 40 * 38178 * 2
def baseEnd_38178 : Nat := 19603664427456862099429

theorem tailTrace_38178 : CollatzResearch.WordTrace tailWord_38178 prefixEnd_38178 19603664427456862099429 := by
  unfold tailWord_38178
  simp only [CollatzResearch.WordTrace]
  refine ⟨348116513923775282100797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 928310703796734085602125 348116513923775282100797)
  ·
    refine ⟨130543692721415730787799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 348116513923775282100797 130543692721415730787799)
    ·
      refine ⟨195815539082123596181699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130543692721415730787799 195815539082123596181699)
      ·
        refine ⟨293723308623185394272549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195815539082123596181699 293723308623185394272549)
        ·
          refine ⟨55073120366847261426103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 293723308623185394272549 55073120366847261426103)
          ·
            refine ⟨82609680550270892139155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55073120366847261426103 82609680550270892139155)
            ·
              refine ⟨123914520825406338208733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82609680550270892139155 123914520825406338208733)
              ·
                refine ⟨46467945309527376828275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 123914520825406338208733 46467945309527376828275)
                ·
                  refine ⟨69701917964291065242413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46467945309527376828275 69701917964291065242413)
                  ·
                    refine ⟨26138219236609149465905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 69701917964291065242413 26138219236609149465905)
                    ·
                      refine ⟨19603664427456862099429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 26138219236609149465905 19603664427456862099429)
                      ·
                        rfl

theorem cell23_38178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 3, 1, 3, 2].length) (baseStart_38178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_38178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_38178 prefixEnd_38178 := by exact prefixLift 38178
  have htrace : WordTrace (prefixWord ++ tailWord_38178) baseStart_38178 baseEnd_38178 := by
    simpa [prefixWord, tailWord_38178, baseEnd_38178] using wordTrace_append hprefix tailTrace_38178
  have hstable : (prefixWord ++ tailWord_38178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38178).length < 2 ^ (prefixWord ++ tailWord_38178).sum := by decide
  have hdescent : baseEnd_38178 < baseStart_38178 := by decide
  rcases family_descends (prefixWord ++ tailWord_38178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38197 : List Nat := [1, 3, 3, 1, 2, 2, 1, 3, 7]
def baseStart_38197 : Nat := 118140960795 + 38197 * 2 ^ 59
def prefixEnd_38197 : Nat := 4983230072969 + 3 ^ 40 * 38197 * 2
def baseEnd_38197 : Nat := 2179268951099143084649

theorem tailTrace_38197 : CollatzResearch.WordTrace tailWord_38197 prefixEnd_38197 2179268951099143084649 := by
  unfold tailWord_38197
  simp only [CollatzResearch.WordTrace]
  refine ⟨1393159042626267373344845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 928772695084178248896563 1393159042626267373344845)
  ·
    refine ⟨522434640984850265004317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1393159042626267373344845 522434640984850265004317)
    ·
      refine ⟨195912990369318849376619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 522434640984850265004317 195912990369318849376619)
      ·
        refine ⟨293869485553978274064929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195912990369318849376619 293869485553978274064929)
        ·
          refine ⟨220402114165483705548697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 293869485553978274064929 220402114165483705548697)
          ·
            refine ⟨165301585624112779161523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 220402114165483705548697 165301585624112779161523)
            ·
              refine ⟨247952378436169168742285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 165301585624112779161523 247952378436169168742285)
              ·
                refine ⟨92982141913563438278357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 247952378436169168742285 92982141913563438278357)
                ·
                  refine ⟨2179268951099143084649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 92982141913563438278357 2179268951099143084649)
                  ·
                    rfl

theorem cell23_38197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 3, 7].length) (baseStart_38197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_38197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_38197 prefixEnd_38197 := by exact prefixLift 38197
  have htrace : WordTrace (prefixWord ++ tailWord_38197) baseStart_38197 baseEnd_38197 := by
    simpa [prefixWord, tailWord_38197, baseEnd_38197] using wordTrace_append hprefix tailTrace_38197
  have hstable : (prefixWord ++ tailWord_38197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38197).length < 2 ^ (prefixWord ++ tailWord_38197).sum := by decide
  have hdescent : baseEnd_38197 < baseStart_38197 := by decide
  rcases family_descends (prefixWord ++ tailWord_38197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38208 : List Nat := [2, 1, 1, 2, 2, 1, 7, 1, 2, 2, 2]
def baseStart_38208 : Nat := 118140960795 + 38208 * 2 ^ 59
def prefixEnd_38208 : Nat := 4983230072969 + 3 ^ 40 * 38208 * 2
def baseEnd_38208 : Nat := 19619068847091744724291

theorem tailTrace_38208 : CollatzResearch.WordTrace tailWord_38208 prefixEnd_38208 19619068847091744724291 := by
  unfold tailWord_38208
  simp only [CollatzResearch.WordTrace]
  refine ⟨696780122793208125997639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 929040163724277501330185 696780122793208125997639)
  ·
    refine ⟨1045170184189812188996459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 696780122793208125997639 1045170184189812188996459)
    ·
      refine ⟨1567755276284718283494689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1045170184189812188996459 1567755276284718283494689)
      ·
        refine ⟨1175816457213538712621017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1567755276284718283494689 1175816457213538712621017)
        ·
          refine ⟨881862342910154034465763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1175816457213538712621017 881862342910154034465763)
          ·
            refine ⟨1322793514365231051698645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 881862342910154034465763 1322793514365231051698645)
            ·
              refine ⟨31002972992935102774187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1322793514365231051698645 31002972992935102774187)
              ·
                refine ⟨46504459489402654161281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31002972992935102774187 46504459489402654161281)
                ·
                  refine ⟨34878344617051990620961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46504459489402654161281 34878344617051990620961)
                  ·
                    refine ⟨26158758462788992965721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34878344617051990620961 26158758462788992965721)
                    ·
                      refine ⟨19619068847091744724291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 26158758462788992965721 19619068847091744724291)
                      ·
                        rfl

theorem cell23_38208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 7, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 7, 1, 2, 2, 2].length) (baseStart_38208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_38208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_38208 prefixEnd_38208 := by exact prefixLift 38208
  have htrace : WordTrace (prefixWord ++ tailWord_38208) baseStart_38208 baseEnd_38208 := by
    simpa [prefixWord, tailWord_38208, baseEnd_38208] using wordTrace_append hprefix tailTrace_38208
  have hstable : (prefixWord ++ tailWord_38208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38208).length < 2 ^ (prefixWord ++ tailWord_38208).sum := by decide
  have hdescent : baseEnd_38208 < baseStart_38208 := by decide
  rcases family_descends (prefixWord ++ tailWord_38208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38227 : List Nat := [1, 1, 1, 2, 1, 1, 6, 3, 2, 5]
def baseStart_38227 : Nat := 118140960795 + 38227 * 2 ^ 59
def prefixEnd_38227 : Nat := 4983230072969 + 3 ^ 40 * 38227 * 2
def baseEnd_38227 : Nat := 6542941659842390128901

theorem tailTrace_38227 : CollatzResearch.WordTrace tailWord_38227 prefixEnd_38227 6542941659842390128901 := by
  unfold tailWord_38227
  simp only [CollatzResearch.WordTrace]
  refine ⟨1394253232517582496936935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 929502155011721664624623 1394253232517582496936935)
  ·
    refine ⟨2091379848776373745405403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1394253232517582496936935 2091379848776373745405403)
    ·
      refine ⟨3137069773164560618108105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2091379848776373745405403 3137069773164560618108105)
      ·
        refine ⟨2352802329873420463581079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3137069773164560618108105 2352802329873420463581079)
        ·
          refine ⟨3529203494810130695371619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2352802329873420463581079 3529203494810130695371619)
          ·
            refine ⟨5293805242215196043057429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3529203494810130695371619 5293805242215196043057429)
            ·
              refine ⟨248147120728837314518317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5293805242215196043057429 248147120728837314518317)
              ·
                refine ⟨93055170273313992944369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 248147120728837314518317 93055170273313992944369)
                ·
                  refine ⟨69791377704985494708277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 93055170273313992944369 69791377704985494708277)
                  ·
                    refine ⟨6542941659842390128901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 69791377704985494708277 6542941659842390128901)
                    ·
                      rfl

theorem cell23_38227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 3, 2, 5].length) (baseStart_38227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_38227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_38227 prefixEnd_38227 := by exact prefixLift 38227
  have htrace : WordTrace (prefixWord ++ tailWord_38227) baseStart_38227 baseEnd_38227 := by
    simpa [prefixWord, tailWord_38227, baseEnd_38227] using wordTrace_append hprefix tailTrace_38227
  have hstable : (prefixWord ++ tailWord_38227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38227).length < 2 ^ (prefixWord ++ tailWord_38227).sum := by decide
  have hdescent : baseEnd_38227 < baseStart_38227 := by decide
  rcases family_descends (prefixWord ++ tailWord_38227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38231 : List Nat := [1, 1, 3, 2, 3, 4, 1, 3, 5]
def baseStart_38231 : Nat := 118140960795 + 38231 * 2 ^ 59
def prefixEnd_38231 : Nat := 4983230072969 + 3 ^ 40 * 38231 * 2
def baseEnd_38231 : Nat := 2181208766905017192965

theorem tailTrace_38231 : CollatzResearch.WordTrace tailWord_38231 prefixEnd_38231 2181208766905017192965 := by
  unfold tailWord_38231
  simp only [CollatzResearch.WordTrace]
  refine ⟨1394399124503091180082547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 929599416335394120055031 1394399124503091180082547)
  ·
    refine ⟨2091598686754636770123821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1394399124503091180082547 2091598686754636770123821)
    ·
      refine ⟨784349507532988788796433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2091598686754636770123821 784349507532988788796433)
      ·
        refine ⟨588262130649741591597325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 784349507532988788796433 588262130649741591597325)
        ·
          refine ⟨220598298993653096848997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 588262130649741591597325 220598298993653096848997)
          ·
            refine ⟨41362181061309955659187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 220598298993653096848997 41362181061309955659187)
            ·
              refine ⟨62043271591964933488781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41362181061309955659187 62043271591964933488781)
              ·
                refine ⟨23266226846986850058293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62043271591964933488781 23266226846986850058293)
                ·
                  refine ⟨2181208766905017192965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23266226846986850058293 2181208766905017192965)
                  ·
                    rfl

theorem cell23_38231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 3, 5].length) (baseStart_38231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_38231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_38231 prefixEnd_38231 := by exact prefixLift 38231
  have htrace : WordTrace (prefixWord ++ tailWord_38231) baseStart_38231 baseEnd_38231 := by
    simpa [prefixWord, tailWord_38231, baseEnd_38231] using wordTrace_append hprefix tailTrace_38231
  have hstable : (prefixWord ++ tailWord_38231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38231).length < 2 ^ (prefixWord ++ tailWord_38231).sum := by decide
  have hdescent : baseEnd_38231 < baseStart_38231 := by decide
  rcases family_descends (prefixWord ++ tailWord_38231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38244 : List Nat := [2, 3, 1, 1, 3, 3, 1, 2, 2, 5]
def baseStart_38244 : Nat := 118140960795 + 38244 * 2 ^ 59
def prefixEnd_38244 : Nat := 4983230072969 + 3 ^ 40 * 38244 * 2
def baseEnd_38244 : Nat := 6545851383551201291375

theorem tailTrace_38244 : CollatzResearch.WordTrace tailWord_38244 prefixEnd_38244 6545851383551201291375 := by
  unfold tailWord_38244
  simp only [CollatzResearch.WordTrace]
  refine ⟨697436636727997200152893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 929915515637329600203857 697436636727997200152893)
  ·
    refine ⟨261538738772998950057335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 697436636727997200152893 261538738772998950057335)
    ·
      refine ⟨392308108159498425086003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 261538738772998950057335 392308108159498425086003)
      ·
        refine ⟨588462162239247637629005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 392308108159498425086003 588462162239247637629005)
        ·
          refine ⟨220673310839717864110877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 588462162239247637629005 220673310839717864110877)
          ·
            refine ⟨82752491564894199041579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 220673310839717864110877 82752491564894199041579)
            ·
              refine ⟨124128737347341298562369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82752491564894199041579 124128737347341298562369)
              ·
                refine ⟨93096553010505973921777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 124128737347341298562369 93096553010505973921777)
                ·
                  refine ⟨69822414757879480441333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 93096553010505973921777 69822414757879480441333)
                  ·
                    refine ⟨6545851383551201291375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 69822414757879480441333 6545851383551201291375)
                    ·
                      rfl

theorem cell23_38244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 2, 2, 5].length) (baseStart_38244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_38244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_38244 prefixEnd_38244 := by exact prefixLift 38244
  have htrace : WordTrace (prefixWord ++ tailWord_38244) baseStart_38244 baseEnd_38244 := by
    simpa [prefixWord, tailWord_38244, baseEnd_38244] using wordTrace_append hprefix tailTrace_38244
  have hstable : (prefixWord ++ tailWord_38244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38244).length < 2 ^ (prefixWord ++ tailWord_38244).sum := by decide
  have hdescent : baseEnd_38244 < baseStart_38244 := by decide
  rcases family_descends (prefixWord ++ tailWord_38244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38248 : List Nat := [2, 1, 4, 2, 3, 1, 3, 2, 5]
def baseStart_38248 : Nat := 118140960795 + 38248 * 2 ^ 59
def prefixEnd_38248 : Nat := 4983230072969 + 3 ^ 40 * 38248 * 2
def baseEnd_38248 : Nat := 2182178674807954247123

theorem tailTrace_38248 : CollatzResearch.WordTrace tailWord_38248 prefixEnd_38248 2182178674807954247123 := by
  unfold tailWord_38248
  simp only [CollatzResearch.WordTrace]
  refine ⟨697509582720751541725699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 930012776961002055634265 697509582720751541725699)
  ·
    refine ⟨1046264374081127312588549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 697509582720751541725699 1046264374081127312588549)
    ·
      refine ⟨196174570140211371110353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1046264374081127312588549 196174570140211371110353)
      ·
        refine ⟨147130927605158528332765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196174570140211371110353 147130927605158528332765)
        ·
          refine ⟨55174097851934448124787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 147130927605158528332765 55174097851934448124787)
          ·
            refine ⟨82761146777901672187181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55174097851934448124787 82761146777901672187181)
            ·
              refine ⟨31035430041713127070193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82761146777901672187181 31035430041713127070193)
              ·
                refine ⟨23276572531284845302645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31035430041713127070193 23276572531284845302645)
                ·
                  refine ⟨2182178674807954247123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23276572531284845302645 2182178674807954247123)
                  ·
                    rfl

theorem cell23_38248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 3, 2, 5].length) (baseStart_38248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_38248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_38248 prefixEnd_38248 := by exact prefixLift 38248
  have htrace : WordTrace (prefixWord ++ tailWord_38248) baseStart_38248 baseEnd_38248 := by
    simpa [prefixWord, tailWord_38248, baseEnd_38248] using wordTrace_append hprefix tailTrace_38248
  have hstable : (prefixWord ++ tailWord_38248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38248).length < 2 ^ (prefixWord ++ tailWord_38248).sum := by decide
  have hdescent : baseEnd_38248 < baseStart_38248 := by decide
  rcases family_descends (prefixWord ++ tailWord_38248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38277 : List Nat := [1, 3, 1, 1, 3, 1, 2, 1, 2, 4, 4]
def baseStart_38277 : Nat := 118140960795 + 38277 * 2 ^ 59
def prefixEnd_38277 : Nat := 4983230072969 + 3 ^ 40 * 38277 * 2
def baseEnd_38277 : Nat := 19654499012251974761473

theorem tailTrace_38277 : CollatzResearch.WordTrace tailWord_38277 prefixEnd_38277 19654499012251974761473 := by
  unfold tailWord_38277
  simp only [CollatzResearch.WordTrace]
  refine ⟨1396076882336441036257085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 930717921557627357504723 1396076882336441036257085)
  ·
    refine ⟨523528830876165388596407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1396076882336441036257085 523528830876165388596407)
    ·
      refine ⟨785293246314248082894611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 523528830876165388596407 785293246314248082894611)
      ·
        refine ⟨1177939869471372124341917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 785293246314248082894611 1177939869471372124341917)
        ·
          refine ⟨441727451051764546628219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1177939869471372124341917 441727451051764546628219)
          ·
            refine ⟨662591176577646819942329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 441727451051764546628219 662591176577646819942329)
            ·
              refine ⟨496943382433235114956747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 662591176577646819942329 496943382433235114956747)
              ·
                refine ⟨745415073649852672435121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 496943382433235114956747 745415073649852672435121)
                ·
                  refine ⟨559061305237389504326341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 745415073649852672435121 559061305237389504326341)
                  ·
                    refine ⟨104823994732010532061189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 559061305237389504326341 104823994732010532061189)
                    ·
                      refine ⟨19654499012251974761473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 104823994732010532061189 19654499012251974761473)
                      ·
                        rfl

theorem cell23_38277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 4, 4].length) (baseStart_38277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_38277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_38277 prefixEnd_38277 := by exact prefixLift 38277
  have htrace : WordTrace (prefixWord ++ tailWord_38277) baseStart_38277 baseEnd_38277 := by
    simpa [prefixWord, tailWord_38277, baseEnd_38277] using wordTrace_append hprefix tailTrace_38277
  have hstable : (prefixWord ++ tailWord_38277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38277).length < 2 ^ (prefixWord ++ tailWord_38277).sum := by decide
  have hdescent : baseEnd_38277 < baseStart_38277 := by decide
  rcases family_descends (prefixWord ++ tailWord_38277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38281 : List Nat := [1, 2, 1, 1, 7, 1, 2, 1, 2, 1, 4]
def baseStart_38281 : Nat := 118140960795 + 38281 * 2 ^ 59
def prefixEnd_38281 : Nat := 4983230072969 + 3 ^ 40 * 38281 * 2
def baseEnd_38281 : Nat := 19656552934869959111455

theorem tailTrace_38281 : CollatzResearch.WordTrace tailWord_38281 prefixEnd_38281 19656552934869959111455 := by
  unfold tailWord_38281
  simp only [CollatzResearch.WordTrace]
  refine ⟨1396222774321949719402697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 930815182881299812935131 1396222774321949719402697)
  ·
    refine ⟨1047167080741462289552023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1396222774321949719402697 1047167080741462289552023)
    ·
      refine ⟨1570750621112193434328035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1047167080741462289552023 1570750621112193434328035)
      ·
        refine ⟨2356125931668290151492053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1570750621112193434328035 2356125931668290151492053)
        ·
          refine ⟨55221701523475550425595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 2356125931668290151492053 55221701523475550425595)
          ·
            refine ⟨82832552285213325638393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55221701523475550425595 82832552285213325638393)
            ·
              refine ⟨62124414213909994228795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82832552285213325638393 62124414213909994228795)
              ·
                refine ⟨93186621320864991343193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62124414213909994228795 93186621320864991343193)
                ·
                  refine ⟨69889965990648743507395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 93186621320864991343193 69889965990648743507395)
                  ·
                    refine ⟨104834948985973115261093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 69889965990648743507395 104834948985973115261093)
                    ·
                      refine ⟨19656552934869959111455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 104834948985973115261093 19656552934869959111455)
                      ·
                        rfl

theorem cell23_38281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 1, 2, 1, 4].length) (baseStart_38281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_38281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_38281 prefixEnd_38281 := by exact prefixLift 38281
  have htrace : WordTrace (prefixWord ++ tailWord_38281) baseStart_38281 baseEnd_38281 := by
    simpa [prefixWord, tailWord_38281, baseEnd_38281] using wordTrace_append hprefix tailTrace_38281
  have hstable : (prefixWord ++ tailWord_38281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38281).length < 2 ^ (prefixWord ++ tailWord_38281).sum := by decide
  have hdescent : baseEnd_38281 < baseStart_38281 := by decide
  rcases family_descends (prefixWord ++ tailWord_38281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38301 : List Nat := [1, 4, 2, 1, 3, 1, 2, 2, 2, 2, 3]
def baseStart_38301 : Nat := 118140960795 + 38301 * 2 ^ 59
def prefixEnd_38301 : Nat := 4983230072969 + 3 ^ 40 * 38301 * 2
def baseEnd_38301 : Nat := 19666822547959880861363

theorem tailTrace_38301 : CollatzResearch.WordTrace tailWord_38301 prefixEnd_38301 19666822547959880861363 := by
  unfold tailWord_38301
  simp only [CollatzResearch.WordTrace]
  refine ⟨1396952234249493135130757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 931301489499662090087171 1396952234249493135130757)
  ·
    refine ⟨261928543921779962837017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1396952234249493135130757 261928543921779962837017)
    ·
      refine ⟨196446407941334972127763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 261928543921779962837017 196446407941334972127763)
      ·
        refine ⟨294669611912002458191645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196446407941334972127763 294669611912002458191645)
        ·
          refine ⟨110501104467000921821867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 294669611912002458191645 110501104467000921821867)
          ·
            refine ⟨165751656700501382732801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110501104467000921821867 165751656700501382732801)
            ·
              refine ⟨124313742525376037049601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 165751656700501382732801 124313742525376037049601)
              ·
                refine ⟨93235306894032027787201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 124313742525376037049601 93235306894032027787201)
                ·
                  refine ⟨69926480170524020840401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 93235306894032027787201 69926480170524020840401)
                  ·
                    refine ⟨52444860127893015630301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 69926480170524020840401 52444860127893015630301)
                    ·
                      refine ⟨19666822547959880861363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 52444860127893015630301 19666822547959880861363)
                      ·
                        rfl

theorem cell23_38301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 2, 2, 2, 3].length) (baseStart_38301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_38301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_38301 prefixEnd_38301 := by exact prefixLift 38301
  have htrace : WordTrace (prefixWord ++ tailWord_38301) baseStart_38301 baseEnd_38301 := by
    simpa [prefixWord, tailWord_38301, baseEnd_38301] using wordTrace_append hprefix tailTrace_38301
  have hstable : (prefixWord ++ tailWord_38301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38301).length < 2 ^ (prefixWord ++ tailWord_38301).sum := by decide
  have hdescent : baseEnd_38301 < baseStart_38301 := by decide
  rcases family_descends (prefixWord ++ tailWord_38301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38304 : List Nat := [2, 1, 1, 4, 1, 2, 4, 2, 6]
def baseStart_38304 : Nat := 118140960795 + 38304 * 2 ^ 59
def prefixEnd_38304 : Nat := 4983230072969 + 3 ^ 40 * 38304 * 2
def baseEnd_38304 : Nat := 2185373665547041013761

theorem tailTrace_38304 : CollatzResearch.WordTrace tailWord_38304 prefixEnd_38304 2185373665547041013761 := by
  unfold tailWord_38304
  simp only [CollatzResearch.WordTrace]
  refine ⟨698530826619312323744983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 931374435492416431659977 698530826619312323744983)
  ·
    refine ⟨1047796239928968485617475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 698530826619312323744983 1047796239928968485617475)
    ·
      refine ⟨1571694359893452728426213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1047796239928968485617475 1571694359893452728426213)
      ·
        refine ⟨294692692480022386579915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1571694359893452728426213 294692692480022386579915)
        ·
          refine ⟨442039038720033579869873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 294692692480022386579915 442039038720033579869873)
          ·
            refine ⟨331529279040025184902405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 442039038720033579869873 331529279040025184902405)
            ·
              refine ⟨62161739820004722169201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 331529279040025184902405 62161739820004722169201)
              ·
                refine ⟨46621304865003541626901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62161739820004722169201 46621304865003541626901)
                ·
                  refine ⟨2185373665547041013761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 46621304865003541626901 2185373665547041013761)
                  ·
                    rfl

theorem cell23_38304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 2, 6].length) (baseStart_38304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_38304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_38304 prefixEnd_38304 := by exact prefixLift 38304
  have htrace : WordTrace (prefixWord ++ tailWord_38304) baseStart_38304 baseEnd_38304 := by
    simpa [prefixWord, tailWord_38304, baseEnd_38304] using wordTrace_append hprefix tailTrace_38304
  have hstable : (prefixWord ++ tailWord_38304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38304).length < 2 ^ (prefixWord ++ tailWord_38304).sum := by decide
  have hdescent : baseEnd_38304 < baseStart_38304 := by decide
  rcases family_descends (prefixWord ++ tailWord_38304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38307 : List Nat := [1, 1, 1, 4, 1, 3, 2, 1, 1, 2, 6]
def baseStart_38307 : Nat := 118140960795 + 38307 * 2 ^ 59
def prefixEnd_38307 : Nat := 4983230072969 + 3 ^ 40 * 38307 * 2
def baseEnd_38307 : Nat := 19669903431886857386335

theorem tailTrace_38307 : CollatzResearch.WordTrace tailWord_38307 prefixEnd_38307 19669903431886857386335 := by
  unfold tailWord_38307
  simp only [CollatzResearch.WordTrace]
  refine ⟨1397171072227756159849175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 931447381485170773232783 1397171072227756159849175)
  ·
    refine ⟨2095756608341634239773763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1397171072227756159849175 2095756608341634239773763)
    ·
      refine ⟨3143634912512451359660645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2095756608341634239773763 3143634912512451359660645)
      ·
        refine ⟨589431546096084629936371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3143634912512451359660645 589431546096084629936371)
        ·
          refine ⟨884147319144126944904557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 589431546096084629936371 884147319144126944904557)
          ·
            refine ⟨331555244679047604339209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 884147319144126944904557 331555244679047604339209)
            ·
              refine ⟨248666433509285703254407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 331555244679047604339209 248666433509285703254407)
              ·
                refine ⟨372999650263928554881611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 248666433509285703254407 372999650263928554881611)
                ·
                  refine ⟨559499475395892832322417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 372999650263928554881611 559499475395892832322417)
                  ·
                    refine ⟨419624606546919624241813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 559499475395892832322417 419624606546919624241813)
                    ·
                      refine ⟨19669903431886857386335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 419624606546919624241813 19669903431886857386335)
                      ·
                        rfl

theorem cell23_38307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 2, 6].length) (baseStart_38307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_38307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_38307 prefixEnd_38307 := by exact prefixLift 38307
  have htrace : WordTrace (prefixWord ++ tailWord_38307) baseStart_38307 baseEnd_38307 := by
    simpa [prefixWord, tailWord_38307, baseEnd_38307] using wordTrace_append hprefix tailTrace_38307
  have hstable : (prefixWord ++ tailWord_38307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38307).length < 2 ^ (prefixWord ++ tailWord_38307).sum := by decide
  have hdescent : baseEnd_38307 < baseStart_38307 := by decide
  rcases family_descends (prefixWord ++ tailWord_38307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38327 : List Nat := [1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 7]
def baseStart_38327 : Nat := 118140960795 + 38327 * 2 ^ 59
def prefixEnd_38327 : Nat := 4983230072969 + 3 ^ 40 * 38327 * 2
def baseEnd_38327 : Nat := 19680173044976779136243

theorem tailTrace_38327 : CollatzResearch.WordTrace tailWord_38327 prefixEnd_38327 19680173044976779136243 := by
  unfold tailWord_38327
  simp only [CollatzResearch.WordTrace]
  refine ⟨1397900532155299575577235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 931933688103533050384823 1397900532155299575577235)
  ·
    refine ⟨2096850798232949363365853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1397900532155299575577235 2096850798232949363365853)
    ·
      refine ⟨786319049337356011262195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2096850798232949363365853 786319049337356011262195)
      ·
        refine ⟨1179478574006034016893293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 786319049337356011262195 1179478574006034016893293)
        ·
          refine ⟨442304465252262756334985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1179478574006034016893293 442304465252262756334985)
          ·
            refine ⟨331728348939197067251239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 442304465252262756334985 331728348939197067251239)
            ·
              refine ⟨497592523408795600876859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 331728348939197067251239 497592523408795600876859)
              ·
                refine ⟨746388785113193401315289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 497592523408795600876859 746388785113193401315289)
                ·
                  refine ⟨559791588834895050986467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 746388785113193401315289 559791588834895050986467)
                  ·
                    refine ⟨839687383252342576479701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 559791588834895050986467 839687383252342576479701)
                    ·
                      refine ⟨19680173044976779136243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 839687383252342576479701 19680173044976779136243)
                      ·
                        rfl

theorem cell23_38327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 7].length) (baseStart_38327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_38327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_38327 prefixEnd_38327 := by exact prefixLift 38327
  have htrace : WordTrace (prefixWord ++ tailWord_38327) baseStart_38327 baseEnd_38327 := by
    simpa [prefixWord, tailWord_38327, baseEnd_38327] using wordTrace_append hprefix tailTrace_38327
  have hstable : (prefixWord ++ tailWord_38327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38327).length < 2 ^ (prefixWord ++ tailWord_38327).sum := by decide
  have hdescent : baseEnd_38327 < baseStart_38327 := by decide
  rcases family_descends (prefixWord ++ tailWord_38327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38351 : List Nat := [1, 1, 2, 1, 1, 4, 6, 1, 1, 5]
def baseStart_38351 : Nat := 118140960795 + 38351 * 2 ^ 59
def prefixEnd_38351 : Nat := 4983230072969 + 3 ^ 40 * 38351 * 2
def baseEnd_38351 : Nat := 6564165526894895078711

theorem tailTrace_38351 : CollatzResearch.WordTrace tailWord_38351 prefixEnd_38351 6564165526894895078711 := by
  unfold tailWord_38351
  simp only [CollatzResearch.WordTrace]
  refine ⟨1398775884068351674450907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 932517256045567782967271 1398775884068351674450907)
  ·
    refine ⟨2098163826102527511676361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1398775884068351674450907 2098163826102527511676361)
    ·
      refine ⟨1573622869576895633757271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2098163826102527511676361 1573622869576895633757271)
      ·
        refine ⟨2360434304365343450635907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1573622869576895633757271 2360434304365343450635907)
        ·
          refine ⟨3540651456548015175953861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2360434304365343450635907 3540651456548015175953861)
          ·
            refine ⟨663872148102752845491349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3540651456548015175953861 663872148102752845491349)
            ·
              refine ⟨31119006942316539632407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 663872148102752845491349 31119006942316539632407)
              ·
                refine ⟨46678510413474809448611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31119006942316539632407 46678510413474809448611)
                ·
                  refine ⟨70017765620212214172917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46678510413474809448611 70017765620212214172917)
                  ·
                    refine ⟨6564165526894895078711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 70017765620212214172917 6564165526894895078711)
                    ·
                      rfl

theorem cell23_38351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 6, 1, 1, 5].length) (baseStart_38351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_38351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_38351 prefixEnd_38351 := by exact prefixLift 38351
  have htrace : WordTrace (prefixWord ++ tailWord_38351) baseStart_38351 baseEnd_38351 := by
    simpa [prefixWord, tailWord_38351, baseEnd_38351] using wordTrace_append hprefix tailTrace_38351
  have hstable : (prefixWord ++ tailWord_38351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38351).length < 2 ^ (prefixWord ++ tailWord_38351).sum := by decide
  have hdescent : baseEnd_38351 < baseStart_38351 := by decide
  rcases family_descends (prefixWord ++ tailWord_38351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38365 : List Nat := [1, 4, 3, 1, 1, 2, 2, 4, 1, 1, 3]
def baseStart_38365 : Nat := 118140960795 + 38365 * 2 ^ 59
def prefixEnd_38365 : Nat := 4983230072969 + 3 ^ 40 * 38365 * 2
def baseEnd_38365 : Nat := 19699685309847630461069

theorem tailTrace_38365 : CollatzResearch.WordTrace tailWord_38365 prefixEnd_38365 19699685309847630461069 := by
  unfold tailWord_38365
  simp only [CollatzResearch.WordTrace]
  refine ⟨1399286506017632065460549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 932857670678421376973699 1399286506017632065460549)
  ·
    refine ⟨262366219878306012273853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1399286506017632065460549 262366219878306012273853)
    ·
      refine ⟨98387332454364754602695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 262366219878306012273853 98387332454364754602695)
      ·
        refine ⟨147580998681547131904043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98387332454364754602695 147580998681547131904043)
        ·
          refine ⟨221371498022320697856065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147580998681547131904043 221371498022320697856065)
          ·
            refine ⟨166028623516740523392049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 221371498022320697856065 166028623516740523392049)
            ·
              refine ⟨124521467637555392544037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 166028623516740523392049 124521467637555392544037)
              ·
                refine ⟨23347775182041636102007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 124521467637555392544037 23347775182041636102007)
                ·
                  refine ⟨35021662773062454153011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23347775182041636102007 35021662773062454153011)
                  ·
                    refine ⟨52532494159593681229517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35021662773062454153011 52532494159593681229517)
                    ·
                      refine ⟨19699685309847630461069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 52532494159593681229517 19699685309847630461069)
                      ·
                        rfl

theorem cell23_38365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 4, 1, 1, 3].length) (baseStart_38365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_38365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_38365 prefixEnd_38365 := by exact prefixLift 38365
  have htrace : WordTrace (prefixWord ++ tailWord_38365) baseStart_38365 baseEnd_38365 := by
    simpa [prefixWord, tailWord_38365, baseEnd_38365] using wordTrace_append hprefix tailTrace_38365
  have hstable : (prefixWord ++ tailWord_38365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38365).length < 2 ^ (prefixWord ++ tailWord_38365).sum := by decide
  have hdescent : baseEnd_38365 < baseStart_38365 := by decide
  rcases family_descends (prefixWord ++ tailWord_38365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38384 : List Nat := [2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 6]
def baseStart_38384 : Nat := 118140960795 + 38384 * 2 ^ 59
def prefixEnd_38384 : Nat := 4983230072969 + 3 ^ 40 * 38384 * 2
def baseEnd_38384 : Nat := 19709441442283056123481

theorem tailTrace_38384 : CollatzResearch.WordTrace tailWord_38384 prefixEnd_38384 19709441442283056123481 := by
  unfold tailWord_38384
  simp only [CollatzResearch.WordTrace]
  refine ⟨699989746474399155201103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 933319661965865540268137 699989746474399155201103)
  ·
    refine ⟨1049984619711598732801655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 699989746474399155201103 1049984619711598732801655)
    ·
      refine ⟨1574976929567398099202483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1049984619711598732801655 1574976929567398099202483)
      ·
        refine ⟨2362465394351097148803725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1574976929567398099202483 2362465394351097148803725)
        ·
          refine ⟨885924522881661430801397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2362465394351097148803725 885924522881661430801397)
          ·
            refine ⟨83055424020155759137631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 885924522881661430801397 83055424020155759137631)
            ·
              refine ⟨124583136030233638706447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83055424020155759137631 124583136030233638706447)
              ·
                refine ⟨186874704045350458059671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 124583136030233638706447 186874704045350458059671)
                ·
                  refine ⟨280312056068025687089507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 186874704045350458059671 280312056068025687089507)
                  ·
                    refine ⟨420468084102038530634261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 280312056068025687089507 420468084102038530634261)
                    ·
                      refine ⟨19709441442283056123481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 420468084102038530634261 19709441442283056123481)
                      ·
                        rfl

theorem cell23_38384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 6].length) (baseStart_38384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_38384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_38384 prefixEnd_38384 := by exact prefixLift 38384
  have htrace : WordTrace (prefixWord ++ tailWord_38384) baseStart_38384 baseEnd_38384 := by
    simpa [prefixWord, tailWord_38384, baseEnd_38384] using wordTrace_append hprefix tailTrace_38384
  have hstable : (prefixWord ++ tailWord_38384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38384).length < 2 ^ (prefixWord ++ tailWord_38384).sum := by decide
  have hdescent : baseEnd_38384 < baseStart_38384 := by decide
  rcases family_descends (prefixWord ++ tailWord_38384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38411 : List Nat := [1, 1, 1, 1, 9, 1, 9]
def baseStart_38411 : Nat := 118140960795 + 38411 * 2 ^ 59
def prefixEnd_38411 : Nat := 4983230072969 + 3 ^ 40 * 38411 * 2
def baseEnd_38411 : Nat := 243497597777215438097

theorem tailTrace_38411 : CollatzResearch.WordTrace tailWord_38411 prefixEnd_38411 243497597777215438097 := by
  unfold tailWord_38411
  simp only [CollatzResearch.WordTrace]
  refine ⟨1400964263850981921635087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 933976175900654614423391 1400964263850981921635087)
  ·
    refine ⟨2101446395776472882452631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1400964263850981921635087 2101446395776472882452631)
    ·
      refine ⟨3152169593664709323678947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2101446395776472882452631 3152169593664709323678947)
      ·
        refine ⟨4728254390497063985518421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3152169593664709323678947 4728254390497063985518421)
        ·
          refine ⟨27704615569318734290147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 4728254390497063985518421 27704615569318734290147)
          ·
            refine ⟨41556923353978101435221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27704615569318734290147 41556923353978101435221)
            ·
              refine ⟨243497597777215438097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 41556923353978101435221 243497597777215438097)
              ·
                rfl

theorem cell23_38411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 9].length) (baseStart_38411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_38411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_38411 prefixEnd_38411 := by exact prefixLift 38411
  have htrace : WordTrace (prefixWord ++ tailWord_38411) baseStart_38411 baseEnd_38411 := by
    simpa [prefixWord, tailWord_38411, baseEnd_38411] using wordTrace_append hprefix tailTrace_38411
  have hstable : (prefixWord ++ tailWord_38411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38411).length < 2 ^ (prefixWord ++ tailWord_38411).sum := by decide
  have hdescent : baseEnd_38411 < baseStart_38411 := by decide
  rcases family_descends (prefixWord ++ tailWord_38411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38501 : List Nat := [1, 3, 1, 3, 3, 2, 1, 2, 7]
def baseStart_38501 : Nat := 118140960795 + 38501 * 2 ^ 59
def prefixEnd_38501 : Nat := 4983230072969 + 3 ^ 40 * 38501 * 2
def baseEnd_38501 : Nat := 2196613186539899817827

theorem tailTrace_38501 : CollatzResearch.WordTrace tailWord_38501 prefixEnd_38501 2196613186539899817827 := by
  unfold tailWord_38501
  simp only [CollatzResearch.WordTrace]
  refine ⟨1404246833524927292411357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 936164555683284861607571 1404246833524927292411357)
  ·
    refine ⟨526592562571847734654259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1404246833524927292411357 526592562571847734654259)
    ·
      refine ⟨789888843857771601981389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 526592562571847734654259 789888843857771601981389)
      ·
        refine ⟨296208316446664350743021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 789888843857771601981389 296208316446664350743021)
        ·
          refine ⟨111078118667499131528633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 296208316446664350743021 111078118667499131528633)
          ·
            refine ⟨83308589000624348646475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111078118667499131528633 83308589000624348646475)
            ·
              refine ⟨124962883500936522969713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83308589000624348646475 124962883500936522969713)
              ·
                refine ⟨93722162625702392227285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 124962883500936522969713 93722162625702392227285)
                ·
                  refine ⟨2196613186539899817827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 93722162625702392227285 2196613186539899817827)
                  ·
                    rfl

theorem cell23_38501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 2, 7].length) (baseStart_38501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_38501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_38501 prefixEnd_38501 := by exact prefixLift 38501
  have htrace : WordTrace (prefixWord ++ tailWord_38501) baseStart_38501 baseEnd_38501 := by
    simpa [prefixWord, tailWord_38501, baseEnd_38501] using wordTrace_append hprefix tailTrace_38501
  have hstable : (prefixWord ++ tailWord_38501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38501).length < 2 ^ (prefixWord ++ tailWord_38501).sum := by decide
  have hdescent : baseEnd_38501 < baseStart_38501 := by decide
  rcases family_descends (prefixWord ++ tailWord_38501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38551 : List Nat := [1, 1, 3, 3, 2, 2, 1, 2, 1, 3, 4]
def baseStart_38551 : Nat := 118140960795 + 38551 * 2 ^ 59
def prefixEnd_38551 : Nat := 4983230072969 + 3 ^ 40 * 38551 * 2
def baseEnd_38551 : Nat := 19795192711583902735213

theorem tailTrace_38551 : CollatzResearch.WordTrace tailWord_38551 prefixEnd_38551 19795192711583902735213 := by
  unfold tailWord_38551
  simp only [CollatzResearch.WordTrace]
  refine ⟨1406070483343785831731507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 937380322229190554487671 1406070483343785831731507)
  ·
    refine ⟨2109105725015678747597261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1406070483343785831731507 2109105725015678747597261)
    ·
      refine ⟨790914646880879530348973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2109105725015678747597261 790914646880879530348973)
      ·
        refine ⟨296592992580329823880865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 790914646880879530348973 296592992580329823880865)
        ·
          refine ⟨222444744435247367910649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 296592992580329823880865 222444744435247367910649)
          ·
            refine ⟨166833558326435525932987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 222444744435247367910649 166833558326435525932987)
            ·
              refine ⟨250250337489653288899481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166833558326435525932987 250250337489653288899481)
              ·
                refine ⟨187687753117239966674611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 250250337489653288899481 187687753117239966674611)
                ·
                  refine ⟨281531629675859950011917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 187687753117239966674611 281531629675859950011917)
                  ·
                    refine ⟨105574361128447481254469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 281531629675859950011917 105574361128447481254469)
                    ·
                      refine ⟨19795192711583902735213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 105574361128447481254469 19795192711583902735213)
                      ·
                        rfl

theorem cell23_38551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_38551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_38551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_38551 prefixEnd_38551 := by exact prefixLift 38551
  have htrace : WordTrace (prefixWord ++ tailWord_38551) baseStart_38551 baseEnd_38551 := by
    simpa [prefixWord, tailWord_38551, baseEnd_38551] using wordTrace_append hprefix tailTrace_38551
  have hstable : (prefixWord ++ tailWord_38551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38551).length < 2 ^ (prefixWord ++ tailWord_38551).sum := by decide
  have hdescent : baseEnd_38551 < baseStart_38551 := by decide
  rcases family_descends (prefixWord ++ tailWord_38551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38588 : List Nat := [2, 2, 2, 3, 1, 2, 1, 1, 4, 2, 3]
def baseStart_38588 : Nat := 118140960795 + 38588 * 2 ^ 59
def prefixEnd_38588 : Nat := 4983230072969 + 3 ^ 40 * 38588 * 2
def baseEnd_38588 : Nat := 19814191495800257972543

theorem tailTrace_38588 : CollatzResearch.WordTrace tailWord_38588 prefixEnd_38588 19814191495800257972543 := by
  unfold tailWord_38588
  simp only [CollatzResearch.WordTrace]
  refine ⟨703709992104870575414209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 938279989473160767218945 703709992104870575414209)
  ·
    refine ⟨527782494078652931560657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 703709992104870575414209 527782494078652931560657)
    ·
      refine ⟨395836870558989698670493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 527782494078652931560657 395836870558989698670493)
      ·
        refine ⟨148438826459621137001435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 395836870558989698670493 148438826459621137001435)
        ·
          refine ⟨222658239689431705502153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148438826459621137001435 222658239689431705502153)
          ·
            refine ⟨166993679767073779126615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 222658239689431705502153 166993679767073779126615)
            ·
              refine ⟨250490519650610668689923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166993679767073779126615 250490519650610668689923)
              ·
                refine ⟨375735779475916003034885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 250490519650610668689923 375735779475916003034885)
                ·
                  refine ⟨70450458651734250569041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 375735779475916003034885 70450458651734250569041)
                  ·
                    refine ⟨52837843988800687926781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 70450458651734250569041 52837843988800687926781)
                    ·
                      refine ⟨19814191495800257972543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 52837843988800687926781 19814191495800257972543)
                      ·
                        rfl

theorem cell23_38588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_38588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_38588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_38588 prefixEnd_38588 := by exact prefixLift 38588
  have htrace : WordTrace (prefixWord ++ tailWord_38588) baseStart_38588 baseEnd_38588 := by
    simpa [prefixWord, tailWord_38588, baseEnd_38588] using wordTrace_append hprefix tailTrace_38588
  have hstable : (prefixWord ++ tailWord_38588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38588).length < 2 ^ (prefixWord ++ tailWord_38588).sum := by decide
  have hdescent : baseEnd_38588 < baseStart_38588 := by decide
  rcases family_descends (prefixWord ++ tailWord_38588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38591 : List Nat := [1, 1, 2, 2, 2, 3, 2, 4, 6]
def baseStart_38591 : Nat := 118140960795 + 38591 * 2 ^ 59
def prefixEnd_38591 : Nat := 4983230072969 + 3 ^ 40 * 38591 * 2
def baseEnd_38591 : Nat := 2201747993084860692781

theorem tailTrace_38591 : CollatzResearch.WordTrace tailWord_38591 prefixEnd_38591 2201747993084860692781 := by
  unfold tailWord_38591
  simp only [CollatzResearch.WordTrace]
  refine ⟨1407529403198872663187627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 938352935465915108791751 1407529403198872663187627)
  ·
    refine ⟨2111294104798308994781441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1407529403198872663187627 2111294104798308994781441)
    ·
      refine ⟨1583470578598731746086081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2111294104798308994781441 1583470578598731746086081)
      ·
        refine ⟨1187602933949048809564561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1583470578598731746086081 1187602933949048809564561)
        ·
          refine ⟨890702200461786607173421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1187602933949048809564561 890702200461786607173421)
          ·
            refine ⟨334013325173169977690033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 890702200461786607173421 334013325173169977690033)
            ·
              refine ⟨250509993879877483267525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 334013325173169977690033 250509993879877483267525)
              ·
                refine ⟨46970623852477028112661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 250509993879877483267525 46970623852477028112661)
                ·
                  refine ⟨2201747993084860692781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 46970623852477028112661 2201747993084860692781)
                  ·
                    rfl

theorem cell23_38591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 4, 6].length) (baseStart_38591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_38591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_38591 prefixEnd_38591 := by exact prefixLift 38591
  have htrace : WordTrace (prefixWord ++ tailWord_38591) baseStart_38591 baseEnd_38591 := by
    simpa [prefixWord, tailWord_38591, baseEnd_38591] using wordTrace_append hprefix tailTrace_38591
  have hstable : (prefixWord ++ tailWord_38591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38591).length < 2 ^ (prefixWord ++ tailWord_38591).sum := by decide
  have hdescent : baseEnd_38591 < baseStart_38591 := by decide
  rcases family_descends (prefixWord ++ tailWord_38591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38652 : List Nat := [2, 2, 2, 1, 3, 1, 3, 4, 1, 1, 3]
def baseStart_38652 : Nat := 118140960795 + 38652 * 2 ^ 59
def prefixEnd_38652 : Nat := 4983230072969 + 3 ^ 40 * 38652 * 2
def baseEnd_38652 : Nat := 19847054257688007572249

theorem tailTrace_38652 : CollatzResearch.WordTrace tailWord_38652 prefixEnd_38652 19847054257688007572249 := by
  unfold tailWord_38652
  simp only [CollatzResearch.WordTrace]
  refine ⟨704877127988940040579105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 939836170651920054105473 704877127988940040579105)
  ·
    refine ⟨528657845991705030434329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 704877127988940040579105 528657845991705030434329)
    ·
      refine ⟨396493384493778772825747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 528657845991705030434329 396493384493778772825747)
      ·
        refine ⟨594740076740668159238621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 396493384493778772825747 594740076740668159238621)
        ·
          refine ⟨223027528777750559714483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 594740076740668159238621 223027528777750559714483)
          ·
            refine ⟨334541293166625839571725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 223027528777750559714483 334541293166625839571725)
            ·
              refine ⟨125452984937484689839397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 334541293166625839571725 125452984937484689839397)
              ·
                refine ⟨23522434675778379344887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 125452984937484689839397 23522434675778379344887)
                ·
                  refine ⟨35283652013667569017331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23522434675778379344887 35283652013667569017331)
                  ·
                    refine ⟨52925478020501353525997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35283652013667569017331 52925478020501353525997)
                    ·
                      refine ⟨19847054257688007572249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 52925478020501353525997 19847054257688007572249)
                      ·
                        rfl

theorem cell23_38652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 4, 1, 1, 3].length) (baseStart_38652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_38652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_38652 prefixEnd_38652 := by exact prefixLift 38652
  have htrace : WordTrace (prefixWord ++ tailWord_38652) baseStart_38652 baseEnd_38652 := by
    simpa [prefixWord, tailWord_38652, baseEnd_38652] using wordTrace_append hprefix tailTrace_38652
  have hstable : (prefixWord ++ tailWord_38652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38652).length < 2 ^ (prefixWord ++ tailWord_38652).sum := by decide
  have hdescent : baseEnd_38652 < baseStart_38652 := by decide
  rcases family_descends (prefixWord ++ tailWord_38652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38688 : List Nat := [2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 4]
def baseStart_38688 : Nat := 118140960795 + 38688 * 2 ^ 59
def prefixEnd_38688 : Nat := 4983230072969 + 3 ^ 40 * 38688 * 2
def baseEnd_38688 : Nat := 19865539561249866722083

theorem tailTrace_38688 : CollatzResearch.WordTrace tailWord_38688 prefixEnd_38688 19865539561249866722083 := by
  unfold tailWord_38688
  simp only [CollatzResearch.WordTrace]
  refine ⟨705533641923729114734359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 940711522564972152979145 705533641923729114734359)
  ·
    refine ⟨1058300462885593672101539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 705533641923729114734359 1058300462885593672101539)
    ·
      refine ⟨1587450694328390508152309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1058300462885593672101539 1587450694328390508152309)
      ·
        refine ⟨148823502593286610139279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1587450694328390508152309 148823502593286610139279)
        ·
          refine ⟨223235253889929915208919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148823502593286610139279 223235253889929915208919)
          ·
            refine ⟨334852880834894872813379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 223235253889929915208919 334852880834894872813379)
            ·
              refine ⟨502279321252342309220069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 334852880834894872813379 502279321252342309220069)
              ·
                refine ⟨94177372734814182978763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 502279321252342309220069 94177372734814182978763)
                ·
                  refine ⟨141266059102221274468145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 94177372734814182978763 141266059102221274468145)
                  ·
                    refine ⟨105949544326665955851109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 141266059102221274468145 105949544326665955851109)
                    ·
                      refine ⟨19865539561249866722083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 105949544326665955851109 19865539561249866722083)
                      ·
                        rfl

theorem cell23_38688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_38688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_38688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_38688 prefixEnd_38688 := by exact prefixLift 38688
  have htrace : WordTrace (prefixWord ++ tailWord_38688) baseStart_38688 baseEnd_38688 := by
    simpa [prefixWord, tailWord_38688, baseEnd_38688] using wordTrace_append hprefix tailTrace_38688
  have hstable : (prefixWord ++ tailWord_38688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38688).length < 2 ^ (prefixWord ++ tailWord_38688).sum := by decide
  have hdescent : baseEnd_38688 < baseStart_38688 := by decide
  rcases family_descends (prefixWord ++ tailWord_38688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38692 : List Nat := [2, 3, 1, 3, 2, 1, 4, 1, 1, 1, 4]
def baseStart_38692 : Nat := 118140960795 + 38692 * 2 ^ 59
def prefixEnd_38692 : Nat := 4983230072969 + 3 ^ 40 * 38692 * 2
def baseEnd_38692 : Nat := 19867593483867851072065

theorem tailTrace_38692 : CollatzResearch.WordTrace tailWord_38692 prefixEnd_38692 19867593483867851072065 := by
  unfold tailWord_38692
  simp only [CollatzResearch.WordTrace]
  refine ⟨705606587916483456307165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 940808783888644608409553 705606587916483456307165)
  ·
    refine ⟨264602470468681296115187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 705606587916483456307165 264602470468681296115187)
    ·
      refine ⟨396903705703021944172781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264602470468681296115187 396903705703021944172781)
      ·
        refine ⟨148838889638633229064793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 396903705703021944172781 148838889638633229064793)
        ·
          refine ⟨111629167228974921798595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148838889638633229064793 111629167228974921798595)
          ·
            refine ⟨167443750843462382697893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111629167228974921798595 167443750843462382697893)
            ·
              refine ⟨31395703283149196755855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 167443750843462382697893 31395703283149196755855)
              ·
                refine ⟨47093554924723795133783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31395703283149196755855 47093554924723795133783)
                ·
                  refine ⟨70640332387085692700675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47093554924723795133783 70640332387085692700675)
                  ·
                    refine ⟨105960498580628539051013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 70640332387085692700675 105960498580628539051013)
                    ·
                      refine ⟨19867593483867851072065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 105960498580628539051013 19867593483867851072065)
                      ·
                        rfl

theorem cell23_38692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 4, 1, 1, 1, 4].length) (baseStart_38692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_38692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_38692 prefixEnd_38692 := by exact prefixLift 38692
  have htrace : WordTrace (prefixWord ++ tailWord_38692) baseStart_38692 baseEnd_38692 := by
    simpa [prefixWord, tailWord_38692, baseEnd_38692] using wordTrace_append hprefix tailTrace_38692
  have hstable : (prefixWord ++ tailWord_38692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38692).length < 2 ^ (prefixWord ++ tailWord_38692).sum := by decide
  have hdescent : baseEnd_38692 < baseStart_38692 := by decide
  rcases family_descends (prefixWord ++ tailWord_38692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38702 : List Nat := [4, 1, 3, 2, 2, 1, 1, 1, 4, 4]
def baseStart_38702 : Nat := 118140960795 + 38702 * 2 ^ 59
def prefixEnd_38702 : Nat := 4983230072969 + 3 ^ 40 * 38702 * 2
def baseEnd_38702 : Nat := 6624242763470937315673

theorem tailTrace_38702 : CollatzResearch.WordTrace tailWord_38702 prefixEnd_38702 6624242763470937315673 := by
  unfold tailWord_38702
  simp only [CollatzResearch.WordTrace]
  refine ⟨176447238224592327559795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 941051937197825746985573 176447238224592327559795)
  ·
    refine ⟨264670857336888491339693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 176447238224592327559795 264670857336888491339693)
    ·
      refine ⟨99251571501333184252385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 264670857336888491339693 99251571501333184252385)
      ·
        refine ⟨74438678625999888189289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99251571501333184252385 74438678625999888189289)
        ·
          refine ⟨55829008969499916141967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74438678625999888189289 55829008969499916141967)
          ·
            refine ⟨83743513454249874212951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55829008969499916141967 83743513454249874212951)
            ·
              refine ⟨125615270181374811319427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83743513454249874212951 125615270181374811319427)
              ·
                refine ⟨188422905272062216979141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125615270181374811319427 188422905272062216979141)
                ·
                  refine ⟨35329294738511665683589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 188422905272062216979141 35329294738511665683589)
                  ·
                    refine ⟨6624242763470937315673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35329294738511665683589 6624242763470937315673)
                    ·
                      rfl

theorem cell23_38702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_38702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_38702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_38702 prefixEnd_38702 := by exact prefixLift 38702
  have htrace : WordTrace (prefixWord ++ tailWord_38702) baseStart_38702 baseEnd_38702 := by
    simpa [prefixWord, tailWord_38702, baseEnd_38702] using wordTrace_append hprefix tailTrace_38702
  have hstable : (prefixWord ++ tailWord_38702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38702).length < 2 ^ (prefixWord ++ tailWord_38702).sum := by decide
  have hdescent : baseEnd_38702 < baseStart_38702 := by decide
  rcases family_descends (prefixWord ++ tailWord_38702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38709 : List Nat := [1, 3, 3, 1, 4, 1, 2, 1, 3, 2, 2]
def baseStart_38709 : Nat := 118140960795 + 38709 * 2 ^ 59
def prefixEnd_38709 : Nat := 4983230072969 + 3 ^ 40 * 38709 * 2
def baseEnd_38709 : Nat := 19876322654994284559487

theorem tailTrace_38709 : CollatzResearch.WordTrace tailWord_38709 prefixEnd_38709 19876322654994284559487 := by
  unfold tailWord_38709
  simp only [CollatzResearch.WordTrace]
  refine ⟨1411833216771378815983181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 941222144514252543988787 1411833216771378815983181)
  ·
    refine ⟨529437456289267055993693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1411833216771378815983181 529437456289267055993693)
    ·
      refine ⟨198539046108475145997635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 529437456289267055993693 198539046108475145997635)
      ·
        refine ⟨297808569162712718996453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198539046108475145997635 297808569162712718996453)
        ·
          refine ⟨55839106718008634811835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 297808569162712718996453 55839106718008634811835)
          ·
            refine ⟨83758660077012952217753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55839106718008634811835 83758660077012952217753)
            ·
              refine ⟨62818995057759714163315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83758660077012952217753 62818995057759714163315)
              ·
                refine ⟨94228492586639571244973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62818995057759714163315 94228492586639571244973)
                ·
                  refine ⟨35335684719989839216865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 94228492586639571244973 35335684719989839216865)
                  ·
                    refine ⟨26501763539992379412649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35335684719989839216865 26501763539992379412649)
                    ·
                      refine ⟨19876322654994284559487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 26501763539992379412649 19876322654994284559487)
                      ·
                        rfl

theorem cell23_38709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 1, 3, 2, 2].length) (baseStart_38709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_38709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_38709 prefixEnd_38709 := by exact prefixLift 38709
  have htrace : WordTrace (prefixWord ++ tailWord_38709) baseStart_38709 baseEnd_38709 := by
    simpa [prefixWord, tailWord_38709, baseEnd_38709] using wordTrace_append hprefix tailTrace_38709
  have hstable : (prefixWord ++ tailWord_38709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38709).length < 2 ^ (prefixWord ++ tailWord_38709).sum := by decide
  have hdescent : baseEnd_38709 < baseStart_38709 := by decide
  rcases family_descends (prefixWord ++ tailWord_38709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38711 : List Nat := [1, 1, 3, 1, 2, 1, 2, 3, 2, 7]
def baseStart_38711 : Nat := 118140960795 + 38711 * 2 ^ 59
def prefixEnd_38711 : Nat := 4983230072969 + 3 ^ 40 * 38711 * 2
def baseEnd_38711 : Nat := 6625783205434425578159

theorem tailTrace_38711 : CollatzResearch.WordTrace tailWord_38711 prefixEnd_38711 6625783205434425578159 := by
  unfold tailWord_38711
  simp only [CollatzResearch.WordTrace]
  refine ⟨1411906162764133157555987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 941270775176088771703991 1411906162764133157555987)
  ·
    refine ⟨2117859244146199736333981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1411906162764133157555987 2117859244146199736333981)
    ·
      refine ⟨794197216554824901125243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2117859244146199736333981 794197216554824901125243)
      ·
        refine ⟨1191295824832237351687865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 794197216554824901125243 1191295824832237351687865)
        ·
          refine ⟨893471868624178013765899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1191295824832237351687865 893471868624178013765899)
          ·
            refine ⟨1340207802936267020648849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 893471868624178013765899 1340207802936267020648849)
            ·
              refine ⟨1005155852202200265486637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1340207802936267020648849 1005155852202200265486637)
              ·
                refine ⟨376933444575825099557489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1005155852202200265486637 376933444575825099557489)
                ·
                  refine ⟨282700083431868824668117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 376933444575825099557489 282700083431868824668117)
                  ·
                    refine ⟨6625783205434425578159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 282700083431868824668117 6625783205434425578159)
                    ·
                      rfl

theorem cell23_38711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 2, 7].length) (baseStart_38711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_38711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_38711 prefixEnd_38711 := by exact prefixLift 38711
  have htrace : WordTrace (prefixWord ++ tailWord_38711) baseStart_38711 baseEnd_38711 := by
    simpa [prefixWord, tailWord_38711, baseEnd_38711] using wordTrace_append hprefix tailTrace_38711
  have hstable : (prefixWord ++ tailWord_38711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38711).length < 2 ^ (prefixWord ++ tailWord_38711).sum := by decide
  have hdescent : baseEnd_38711 < baseStart_38711 := by decide
  rcases family_descends (prefixWord ++ tailWord_38711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38726 : List Nat := [6, 1, 1, 2, 1, 1, 2, 2, 3, 2, 2]
def baseStart_38726 : Nat := 118140960795 + 38726 * 2 ^ 59
def prefixEnd_38726 : Nat := 4983230072969 + 3 ^ 40 * 38726 * 2
def baseEnd_38726 : Nat := 19885051826120718046909

theorem tailTrace_38726 : CollatzResearch.WordTrace tailWord_38726 prefixEnd_38726 19885051826120718046909 := by
  unfold tailWord_38726
  simp only [CollatzResearch.WordTrace]
  refine ⟨44139164303430959979751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 941635505139860479568021 44139164303430959979751)
  ·
    refine ⟨66208746455146439969627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44139164303430959979751 66208746455146439969627)
    ·
      refine ⟨99313119682719659954441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66208746455146439969627 99313119682719659954441)
      ·
        refine ⟨74484839762039744965831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99313119682719659954441 74484839762039744965831)
        ·
          refine ⟨111727259643059617448747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74484839762039744965831 111727259643059617448747)
          ·
            refine ⟨167590889464589426173121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111727259643059617448747 167590889464589426173121)
            ·
              refine ⟨125693167098442069629841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 167590889464589426173121 125693167098442069629841)
              ·
                refine ⟨94269875323831552222381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 125693167098442069629841 94269875323831552222381)
                ·
                  refine ⟨35351203246436832083393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 94269875323831552222381 35351203246436832083393)
                  ·
                    refine ⟨26513402434827624062545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35351203246436832083393 26513402434827624062545)
                    ·
                      refine ⟨19885051826120718046909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 26513402434827624062545 19885051826120718046909)
                      ·
                        rfl

theorem cell23_38726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_38726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_38726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_38726 prefixEnd_38726 := by exact prefixLift 38726
  have htrace : WordTrace (prefixWord ++ tailWord_38726) baseStart_38726 baseEnd_38726 := by
    simpa [prefixWord, tailWord_38726, baseEnd_38726] using wordTrace_append hprefix tailTrace_38726
  have hstable : (prefixWord ++ tailWord_38726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38726).length < 2 ^ (prefixWord ++ tailWord_38726).sum := by decide
  have hdescent : baseEnd_38726 < baseStart_38726 := by decide
  rcases family_descends (prefixWord ++ tailWord_38726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38732 : List Nat := [2, 2, 1, 3, 5, 1, 2, 7]
def baseStart_38732 : Nat := 118140960795 + 38732 * 2 ^ 59
def prefixEnd_38732 : Nat := 4983230072969 + 3 ^ 40 * 38732 * 2
def baseEnd_38732 : Nat := 736597507779544243403

theorem tailTrace_38732 : CollatzResearch.WordTrace tailWord_38732 prefixEnd_38732 736597507779544243403 := by
  unfold tailWord_38732
  simp only [CollatzResearch.WordTrace]
  refine ⟨706336047844026872035225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 941781397125369162713633 706336047844026872035225)
  ·
    refine ⟨529752035883020154026419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 706336047844026872035225 529752035883020154026419)
    ·
      refine ⟨794628053824530231039629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 529752035883020154026419 794628053824530231039629)
      ·
        refine ⟨297985520184198836639861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 794628053824530231039629 297985520184198836639861)
        ·
          refine ⟨27936142517268640934987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 297985520184198836639861 27936142517268640934987)
          ·
            refine ⟨41904213775902961402481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27936142517268640934987 41904213775902961402481)
            ·
              refine ⟨31428160331927221051861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41904213775902961402481 31428160331927221051861)
              ·
                refine ⟨736597507779544243403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 31428160331927221051861 736597507779544243403)
                ·
                  rfl

theorem cell23_38732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 2, 7].length) (baseStart_38732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_38732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_38732 prefixEnd_38732 := by exact prefixLift 38732
  have htrace : WordTrace (prefixWord ++ tailWord_38732) baseStart_38732 baseEnd_38732 := by
    simpa [prefixWord, tailWord_38732, baseEnd_38732] using wordTrace_append hprefix tailTrace_38732
  have hstable : (prefixWord ++ tailWord_38732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38732).length < 2 ^ (prefixWord ++ tailWord_38732).sum := by decide
  have hdescent : baseEnd_38732 < baseStart_38732 := by decide
  rcases family_descends (prefixWord ++ tailWord_38732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38738 : List Nat := [3, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5]
def baseStart_38738 : Nat := 118140960795 + 38738 * 2 ^ 59
def prefixEnd_38738 : Nat := 4983230072969 + 3 ^ 40 * 38738 * 2
def baseEnd_38738 : Nat := 19891213593974671096853

theorem tailTrace_38738 : CollatzResearch.WordTrace tailWord_38738 prefixEnd_38738 19891213593974671096853 := by
  unfold tailWord_38738
  simp only [CollatzResearch.WordTrace]
  refine ⟨353222733416579192197217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 941927289110877845859245 353222733416579192197217)
  ·
    refine ⟨264917050062434394147913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 353222733416579192197217 264917050062434394147913)
    ·
      refine ⟨198687787546825795610935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 264917050062434394147913 198687787546825795610935)
      ·
        refine ⟨298031681320238693416403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198687787546825795610935 298031681320238693416403)
        ·
          refine ⟨447047521980358040124605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 298031681320238693416403 447047521980358040124605)
          ·
            refine ⟨167642820742634265046727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 447047521980358040124605 167642820742634265046727)
            ·
              refine ⟨251464231113951397570091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 167642820742634265046727 251464231113951397570091)
              ·
                refine ⟨377196346670927096355137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 251464231113951397570091 377196346670927096355137)
                ·
                  refine ⟨282897260003195322266353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 377196346670927096355137 282897260003195322266353)
                  ·
                    refine ⟨212172945002396491699765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 282897260003195322266353 212172945002396491699765)
                    ·
                      refine ⟨19891213593974671096853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 212172945002396491699765 19891213593974671096853)
                      ·
                        rfl

theorem cell23_38738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_38738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_38738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_38738 prefixEnd_38738 := by exact prefixLift 38738
  have htrace : WordTrace (prefixWord ++ tailWord_38738) baseStart_38738 baseEnd_38738 := by
    simpa [prefixWord, tailWord_38738, baseEnd_38738] using wordTrace_append hprefix tailTrace_38738
  have hstable : (prefixWord ++ tailWord_38738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38738).length < 2 ^ (prefixWord ++ tailWord_38738).sum := by decide
  have hdescent : baseEnd_38738 < baseStart_38738 := by decide
  rcases family_descends (prefixWord ++ tailWord_38738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38743 : List Nat := [1, 1, 3, 2, 6, 1, 1, 3, 1, 2, 2]
def baseStart_38743 : Nat := 118140960795 + 38743 * 2 ^ 59
def prefixEnd_38743 : Nat := 4983230072969 + 3 ^ 40 * 38743 * 2
def baseEnd_38743 : Nat := 19893780997247151534331

theorem tailTrace_38743 : CollatzResearch.WordTrace tailWord_38743 prefixEnd_38743 19893780997247151534331 := by
  unfold tailWord_38743
  simp only [CollatzResearch.WordTrace]
  refine ⟨1413073298648202622720883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 942048865765468415147255 1413073298648202622720883)
  ·
    refine ⟨2119609947972303934081325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1413073298648202622720883 2119609947972303934081325)
    ·
      refine ⟨794853730489613975280497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2119609947972303934081325 794853730489613975280497)
      ·
        refine ⟨596140297867210481460373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 794853730489613975280497 596140297867210481460373)
        ·
          refine ⟨27944076462525491318455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 596140297867210481460373 27944076462525491318455)
          ·
            refine ⟨41916114693788236977683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27944076462525491318455 41916114693788236977683)
            ·
              refine ⟨62874172040682355466525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41916114693788236977683 62874172040682355466525)
              ·
                refine ⟨23577814515255883299947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62874172040682355466525 23577814515255883299947)
                ·
                  refine ⟨35366721772883824949921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23577814515255883299947 35366721772883824949921)
                  ·
                    refine ⟨26525041329662868712441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35366721772883824949921 26525041329662868712441)
                    ·
                      refine ⟨19893780997247151534331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 26525041329662868712441 19893780997247151534331)
                      ·
                        rfl

theorem cell23_38743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 3, 1, 2, 2].length) (baseStart_38743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_38743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_38743 prefixEnd_38743 := by exact prefixLift 38743
  have htrace : WordTrace (prefixWord ++ tailWord_38743) baseStart_38743 baseEnd_38743 := by
    simpa [prefixWord, tailWord_38743, baseEnd_38743] using wordTrace_append hprefix tailTrace_38743
  have hstable : (prefixWord ++ tailWord_38743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38743).length < 2 ^ (prefixWord ++ tailWord_38743).sum := by decide
  have hdescent : baseEnd_38743 < baseStart_38743 := by decide
  rcases family_descends (prefixWord ++ tailWord_38743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38752 : List Nat := [2, 1, 1, 3, 3, 2, 2, 3, 1, 3, 2]
def baseStart_38752 : Nat := 118140960795 + 38752 * 2 ^ 59
def prefixEnd_38752 : Nat := 4983230072969 + 3 ^ 40 * 38752 * 2
def baseEnd_38752 : Nat := 19898402323137616321789

theorem tailTrace_38752 : CollatzResearch.WordTrace tailWord_38752 prefixEnd_38752 19898402323137616321789 := by
  unfold tailWord_38752
  simp only [CollatzResearch.WordTrace]
  refine ⟨706700777807798579899255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 942267703743731439865673 706700777807798579899255)
  ·
    refine ⟨1060051166711697869848883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 706700777807798579899255 1060051166711697869848883)
    ·
      refine ⟨1590076750067546804773325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1060051166711697869848883 1590076750067546804773325)
      ·
        refine ⟨596278781275330051789997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1590076750067546804773325 596278781275330051789997)
        ·
          refine ⟨223604542978248769421249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 596278781275330051789997 223604542978248769421249)
          ·
            refine ⟨167703407233686577065937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 223604542978248769421249 167703407233686577065937)
            ·
              refine ⟨125777555425264932799453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 167703407233686577065937 125777555425264932799453)
              ·
                refine ⟨47166583284474349799795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 125777555425264932799453 47166583284474349799795)
                ·
                  refine ⟨70749874926711524699693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47166583284474349799795 70749874926711524699693)
                  ·
                    refine ⟨26531203097516821762385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 70749874926711524699693 26531203097516821762385)
                    ·
                      refine ⟨19898402323137616321789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 26531203097516821762385 19898402323137616321789)
                      ·
                        rfl

theorem cell23_38752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 3, 1, 3, 2].length) (baseStart_38752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_38752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_38752 prefixEnd_38752 := by exact prefixLift 38752
  have htrace : WordTrace (prefixWord ++ tailWord_38752) baseStart_38752 baseEnd_38752 := by
    simpa [prefixWord, tailWord_38752, baseEnd_38752] using wordTrace_append hprefix tailTrace_38752
  have hstable : (prefixWord ++ tailWord_38752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38752).length < 2 ^ (prefixWord ++ tailWord_38752).sum := by decide
  have hdescent : baseEnd_38752 < baseStart_38752 := by decide
  rcases family_descends (prefixWord ++ tailWord_38752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38768 : List Nat := [2, 1, 1, 1, 4, 1, 1, 3, 2, 4, 3]
def baseStart_38768 : Nat := 118140960795 + 38768 * 2 ^ 59
def prefixEnd_38768 : Nat := 4983230072969 + 3 ^ 40 * 38768 * 2
def baseEnd_38768 : Nat := 19906618013609553721715

theorem tailTrace_38768 : CollatzResearch.WordTrace tailWord_38768 prefixEnd_38768 19906618013609553721715 := by
  unfold tailWord_38768
  simp only [CollatzResearch.WordTrace]
  refine ⟨706992561778815946190479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 942656749038421261587305 706992561778815946190479)
  ·
    refine ⟨1060488842668223919285719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 706992561778815946190479 1060488842668223919285719)
    ·
      refine ⟨1590733264002335878928579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1060488842668223919285719 1590733264002335878928579)
      ·
        refine ⟨2386099896003503818392869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1590733264002335878928579 2386099896003503818392869)
        ·
          refine ⟨447393730500656965948663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2386099896003503818392869 447393730500656965948663)
          ·
            refine ⟨671090595750985448922995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 447393730500656965948663 671090595750985448922995)
            ·
              refine ⟨1006635893626478173384493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 671090595750985448922995 1006635893626478173384493)
              ·
                refine ⟨377488460109929315019185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1006635893626478173384493 377488460109929315019185)
                ·
                  refine ⟨283116345082446986264389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 377488460109929315019185 283116345082446986264389)
                  ·
                    refine ⟨53084314702958809924573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 283116345082446986264389 53084314702958809924573)
                    ·
                      refine ⟨19906618013609553721715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 53084314702958809924573 19906618013609553721715)
                      ·
                        rfl

theorem cell23_38768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 2, 4, 3].length) (baseStart_38768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_38768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_38768 prefixEnd_38768 := by exact prefixLift 38768
  have htrace : WordTrace (prefixWord ++ tailWord_38768) baseStart_38768 baseEnd_38768 := by
    simpa [prefixWord, tailWord_38768, baseEnd_38768] using wordTrace_append hprefix tailTrace_38768
  have hstable : (prefixWord ++ tailWord_38768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38768).length < 2 ^ (prefixWord ++ tailWord_38768).sum := by decide
  have hdescent : baseEnd_38768 < baseStart_38768 := by decide
  rcases family_descends (prefixWord ++ tailWord_38768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38778 : List Nat := [3, 1, 1, 1, 1, 1, 4, 3, 2, 2, 4]
def baseStart_38778 : Nat := 118140960795 + 38778 * 2 ^ 59
def prefixEnd_38778 : Nat := 4983230072969 + 3 ^ 40 * 38778 * 2
def baseEnd_38778 : Nat := 19911752820154514596669

theorem tailTrace_38778 : CollatzResearch.WordTrace tailWord_38778 prefixEnd_38778 19911752820154514596669 := by
  unfold tailWord_38778
  simp only [CollatzResearch.WordTrace]
  refine ⟨353587463380350900061247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 942899902347602400163325 353587463380350900061247)
  ·
    refine ⟨530381195070526350091871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 353587463380350900061247 530381195070526350091871)
    ·
      refine ⟨795571792605789525137807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 530381195070526350091871 795571792605789525137807)
      ·
        refine ⟨1193357688908684287706711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 795571792605789525137807 1193357688908684287706711)
        ·
          refine ⟨1790036533363026431560067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1193357688908684287706711 1790036533363026431560067)
          ·
            refine ⟨2685054800044539647340101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1790036533363026431560067 2685054800044539647340101)
            ·
              refine ⟨503447775008351183876269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2685054800044539647340101 503447775008351183876269)
              ·
                refine ⟨188792915628131693953601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 503447775008351183876269 188792915628131693953601)
                ·
                  refine ⟨141594686721098770465201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 188792915628131693953601 141594686721098770465201)
                  ·
                    refine ⟨106196015040824077848901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 141594686721098770465201 106196015040824077848901)
                    ·
                      refine ⟨19911752820154514596669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 106196015040824077848901 19911752820154514596669)
                      ·
                        rfl

theorem cell23_38778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3, 2, 2, 4].length) (baseStart_38778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_38778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_38778 prefixEnd_38778 := by exact prefixLift 38778
  have htrace : WordTrace (prefixWord ++ tailWord_38778) baseStart_38778 baseEnd_38778 := by
    simpa [prefixWord, tailWord_38778, baseEnd_38778] using wordTrace_append hprefix tailTrace_38778
  have hstable : (prefixWord ++ tailWord_38778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38778).length < 2 ^ (prefixWord ++ tailWord_38778).sum := by decide
  have hdescent : baseEnd_38778 < baseStart_38778 := by decide
  rcases family_descends (prefixWord ++ tailWord_38778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38788 : List Nat := [2, 3, 2, 1, 1, 1, 2, 4, 7]
def baseStart_38788 : Nat := 118140960795 + 38788 * 2 ^ 59
def prefixEnd_38788 : Nat := 4983230072969 + 3 ^ 40 * 38788 * 2
def baseEnd_38788 : Nat := 2212987514077719496847

theorem tailTrace_38788 : CollatzResearch.WordTrace tailWord_38788 prefixEnd_38788 2212987514077719496847 := by
  unfold tailWord_38788
  simp only [CollatzResearch.WordTrace]
  refine ⟨707357291742587654054509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 943143055656783538739345 707357291742587654054509)
  ·
    refine ⟨265258984403470370270441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 707357291742587654054509 265258984403470370270441)
    ·
      refine ⟨198944238302602777702831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 265258984403470370270441 198944238302602777702831)
      ·
        refine ⟨298416357453904166554247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198944238302602777702831 298416357453904166554247)
        ·
          refine ⟨447624536180856249831371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 298416357453904166554247 447624536180856249831371)
          ·
            refine ⟨671436804271284374747057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 447624536180856249831371 671436804271284374747057)
            ·
              refine ⟨503577603203463281060293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 671436804271284374747057 503577603203463281060293)
              ·
                refine ⟨94420800600649365198805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 503577603203463281060293 94420800600649365198805)
                ·
                  refine ⟨2212987514077719496847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 94420800600649365198805 2212987514077719496847)
                  ·
                    rfl

theorem cell23_38788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 4, 7].length) (baseStart_38788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_38788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_38788 prefixEnd_38788 := by exact prefixLift 38788
  have htrace : WordTrace (prefixWord ++ tailWord_38788) baseStart_38788 baseEnd_38788 := by
    simpa [prefixWord, tailWord_38788, baseEnd_38788] using wordTrace_append hprefix tailTrace_38788
  have hstable : (prefixWord ++ tailWord_38788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38788).length < 2 ^ (prefixWord ++ tailWord_38788).sum := by decide
  have hdescent : baseEnd_38788 < baseStart_38788 := by decide
  rcases family_descends (prefixWord ++ tailWord_38788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38805 : List Nat := [1, 3, 2, 1, 1, 3, 2, 5, 5]
def baseStart_38805 : Nat := 118140960795 + 38805 * 2 ^ 59
def prefixEnd_38805 : Nat := 4983230072969 + 3 ^ 40 * 38805 * 2
def baseEnd_38805 : Nat := 2213957421980656551005

theorem tailTrace_38805 : CollatzResearch.WordTrace tailWord_38805 prefixEnd_38805 2213957421980656551005 := by
  unfold tailWord_38805
  simp only [CollatzResearch.WordTrace]
  refine ⟨1415334624423587211477869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 943556416282391474318579 1415334624423587211477869)
  ·
    refine ⟨530750484158845204304201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1415334624423587211477869 530750484158845204304201)
    ·
      refine ⟨398062863119133903228151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 530750484158845204304201 398062863119133903228151)
      ·
        refine ⟨597094294678700854842227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 398062863119133903228151 597094294678700854842227)
        ·
          refine ⟨895641442018051282263341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 597094294678700854842227 895641442018051282263341)
          ·
            refine ⟨335865540756769230848753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 895641442018051282263341 335865540756769230848753)
            ·
              refine ⟨251899155567576923136565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 335865540756769230848753 251899155567576923136565)
              ·
                refine ⟨23615545834460336544053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 251899155567576923136565 23615545834460336544053)
                ·
                  refine ⟨2213957421980656551005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23615545834460336544053 2213957421980656551005)
                  ·
                    rfl

theorem cell23_38805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 5, 5].length) (baseStart_38805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_38805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_38805 prefixEnd_38805 := by exact prefixLift 38805
  have htrace : WordTrace (prefixWord ++ tailWord_38805) baseStart_38805 baseEnd_38805 := by
    simpa [prefixWord, tailWord_38805, baseEnd_38805] using wordTrace_append hprefix tailTrace_38805
  have hstable : (prefixWord ++ tailWord_38805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38805).length < 2 ^ (prefixWord ++ tailWord_38805).sum := by decide
  have hdescent : baseEnd_38805 < baseStart_38805 := by decide
  rcases family_descends (prefixWord ++ tailWord_38805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38855 : List Nat := [1, 1, 4, 1, 1, 2, 1, 1, 3, 6, 2]
def baseStart_38855 : Nat := 118140960795 + 38855 * 2 ^ 59
def prefixEnd_38855 : Nat := 4983230072969 + 3 ^ 40 * 38855 * 2
def baseEnd_38855 : Nat := 19951290830550713333815

theorem tailTrace_38855 : CollatzResearch.WordTrace tailWord_38855 prefixEnd_38855 19951290830550713333815 := by
  unfold tailWord_38855
  simp only [CollatzResearch.WordTrace]
  refine ⟨1417158274242445750798019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 944772182828297167198679 1417158274242445750798019)
  ·
    refine ⟨2125737411363668626197029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1417158274242445750798019 2125737411363668626197029)
    ·
      refine ⟨398575764630687867411943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2125737411363668626197029 398575764630687867411943)
      ·
        refine ⟨597863646946031801117915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 398575764630687867411943 597863646946031801117915)
        ·
          refine ⟨896795470419047701676873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 597863646946031801117915 896795470419047701676873)
          ·
            refine ⟨672596602814285776257655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 896795470419047701676873 672596602814285776257655)
            ·
              refine ⟨1008894904221428664386483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 672596602814285776257655 1008894904221428664386483)
              ·
                refine ⟨1513342356332142996579725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1008894904221428664386483 1513342356332142996579725)
                ·
                  refine ⟨567503383624553623717397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1513342356332142996579725 567503383624553623717397)
                  ·
                    refine ⟨26601721107400951111753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 567503383624553623717397 26601721107400951111753)
                    ·
                      refine ⟨19951290830550713333815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 26601721107400951111753 19951290830550713333815)
                      ·
                        rfl

theorem cell23_38855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 6, 2].length) (baseStart_38855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_38855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_38855 prefixEnd_38855 := by exact prefixLift 38855
  have htrace : WordTrace (prefixWord ++ tailWord_38855) baseStart_38855 baseEnd_38855 := by
    simpa [prefixWord, tailWord_38855, baseEnd_38855] using wordTrace_append hprefix tailTrace_38855
  have hstable : (prefixWord ++ tailWord_38855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38855).length < 2 ^ (prefixWord ++ tailWord_38855).sum := by decide
  have hdescent : baseEnd_38855 < baseStart_38855 := by decide
  rcases family_descends (prefixWord ++ tailWord_38855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38955 : List Nat := [1, 1, 1, 1, 2, 1, 4, 2, 6, 4]
def baseStart_38955 : Nat := 118140960795 + 38955 * 2 ^ 59
def prefixEnd_38955 : Nat := 4983230072969 + 3 ^ 40 * 38955 * 2
def baseEnd_38955 : Nat := 6667546298666774027785

theorem tailTrace_38955 : CollatzResearch.WordTrace tailWord_38955 prefixEnd_38955 6667546298666774027785 := by
  unfold tailWord_38955
  simp only [CollatzResearch.WordTrace]
  refine ⟨1420805573880162829438319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 947203715920108552958879 1420805573880162829438319)
  ·
    refine ⟨2131208360820244244157479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1420805573880162829438319 2131208360820244244157479)
    ·
      refine ⟨3196812541230366366236219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2131208360820244244157479 3196812541230366366236219)
      ·
        refine ⟨4795218811845549549354329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3196812541230366366236219 4795218811845549549354329)
        ·
          refine ⟨3596414108884162162015747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4795218811845549549354329 3596414108884162162015747)
          ·
            refine ⟨5394621163326243243023621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3596414108884162162015747 5394621163326243243023621)
            ·
              refine ⟨1011491468123670608066929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5394621163326243243023621 1011491468123670608066929)
              ·
                refine ⟨758618601092752956050197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1011491468123670608066929 758618601092752956050197)
                ·
                  refine ⟨35560246926222794814853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 758618601092752956050197 35560246926222794814853)
                  ·
                    refine ⟨6667546298666774027785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35560246926222794814853 6667546298666774027785)
                    ·
                      rfl

theorem cell23_38955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 6, 4].length) (baseStart_38955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_38955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_38955 prefixEnd_38955 := by exact prefixLift 38955
  have htrace : WordTrace (prefixWord ++ tailWord_38955) baseStart_38955 baseEnd_38955 := by
    simpa [prefixWord, tailWord_38955, baseEnd_38955] using wordTrace_append hprefix tailTrace_38955
  have hstable : (prefixWord ++ tailWord_38955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38955).length < 2 ^ (prefixWord ++ tailWord_38955).sum := by decide
  have hdescent : baseEnd_38955 < baseStart_38955 := by decide
  rcases family_descends (prefixWord ++ tailWord_38955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38962 : List Nat := [3, 2, 1, 1, 2, 4, 1, 1, 3, 1, 4]
def baseStart_38962 : Nat := 118140960795 + 38962 * 2 ^ 59
def prefixEnd_38962 : Nat := 4983230072969 + 3 ^ 40 * 38962 * 2
def baseEnd_38962 : Nat := 20006233260581794695823

theorem tailTrace_38962 : CollatzResearch.WordTrace tailWord_38962 prefixEnd_38962 20006233260581794695823 := by
  unfold tailWord_38962
  simp only [CollatzResearch.WordTrace]
  refine ⟨355265221213700756235785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 947373923236535349962093 355265221213700756235785)
  ·
    refine ⟨266448915910275567176839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 355265221213700756235785 266448915910275567176839)
    ·
      refine ⟨399673373865413350765259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266448915910275567176839 399673373865413350765259)
      ·
        refine ⟨599510060798120026147889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 399673373865413350765259 599510060798120026147889)
        ·
          refine ⟨449632545598590019610917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 599510060798120026147889 449632545598590019610917)
          ·
            refine ⟨84306102299735628677047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 449632545598590019610917 84306102299735628677047)
            ·
              refine ⟨126459153449603443015571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84306102299735628677047 126459153449603443015571)
              ·
                refine ⟨189688730174405164523357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126459153449603443015571 189688730174405164523357)
                ·
                  refine ⟨71133273815401936696259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 189688730174405164523357 71133273815401936696259)
                  ·
                    refine ⟨106699910723102905044389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 71133273815401936696259 106699910723102905044389)
                    ·
                      refine ⟨20006233260581794695823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 106699910723102905044389 20006233260581794695823)
                      ·
                        rfl

theorem cell23_38962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 1, 3, 1, 4].length) (baseStart_38962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_38962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_38962 prefixEnd_38962 := by exact prefixLift 38962
  have htrace : WordTrace (prefixWord ++ tailWord_38962) baseStart_38962 baseEnd_38962 := by
    simpa [prefixWord, tailWord_38962, baseEnd_38962] using wordTrace_append hprefix tailTrace_38962
  have hstable : (prefixWord ++ tailWord_38962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38962).length < 2 ^ (prefixWord ++ tailWord_38962).sum := by decide
  have hdescent : baseEnd_38962 < baseStart_38962 := by decide
  rcases family_descends (prefixWord ++ tailWord_38962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38965 : List Nat := [1, 3, 3, 1, 1, 1, 2, 2, 3, 1, 5]
def baseStart_38965 : Nat := 118140960795 + 38965 * 2 ^ 59
def prefixEnd_38965 : Nat := 4983230072969 + 3 ^ 40 * 38965 * 2
def baseEnd_38965 : Nat := 20007773702545282958309

theorem tailTrace_38965 : CollatzResearch.WordTrace tailWord_38965 prefixEnd_38965 20007773702545282958309 := by
  unfold tailWord_38965
  simp only [CollatzResearch.WordTrace]
  refine ⟨1421170303843934537302349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 947446869229289691534899 1421170303843934537302349)
  ·
    refine ⟨532938863941475451488381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1421170303843934537302349 532938863941475451488381)
    ·
      refine ⟨199852073978053294308143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 532938863941475451488381 199852073978053294308143)
      ·
        refine ⟨299778110967079941462215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199852073978053294308143 299778110967079941462215)
        ·
          refine ⟨449667166450619912193323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 299778110967079941462215 449667166450619912193323)
          ·
            refine ⟨674500749675929868289985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 449667166450619912193323 674500749675929868289985)
            ·
              refine ⟨505875562256947401217489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 674500749675929868289985 505875562256947401217489)
              ·
                refine ⟨379406671692710550913117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 505875562256947401217489 379406671692710550913117)
                ·
                  refine ⟨142277501884766456592419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 379406671692710550913117 142277501884766456592419)
                  ·
                    refine ⟨213416252827149684888629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 142277501884766456592419 213416252827149684888629)
                    ·
                      refine ⟨20007773702545282958309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 213416252827149684888629 20007773702545282958309)
                      ·
                        rfl

theorem cell23_38965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_38965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_38965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_38965 prefixEnd_38965 := by exact prefixLift 38965
  have htrace : WordTrace (prefixWord ++ tailWord_38965) baseStart_38965 baseEnd_38965 := by
    simpa [prefixWord, tailWord_38965, baseEnd_38965] using wordTrace_append hprefix tailTrace_38965
  have hstable : (prefixWord ++ tailWord_38965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38965).length < 2 ^ (prefixWord ++ tailWord_38965).sum := by decide
  have hdescent : baseEnd_38965 < baseStart_38965 := by decide
  rcases family_descends (prefixWord ++ tailWord_38965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38966 : List Nat := [5, 1, 2, 1, 1, 1, 4, 1, 2, 3, 2]
def baseStart_38966 : Nat := 118140960795 + 38966 * 2 ^ 59
def prefixEnd_38966 : Nat := 4983230072969 + 3 ^ 40 * 38966 * 2
def baseEnd_38966 : Nat := 20008287183199779045805

theorem tailTrace_38966 : CollatzResearch.WordTrace tailWord_38966 prefixEnd_38966 20008287183199779045805 := by
  unfold tailWord_38966
  simp only [CollatzResearch.WordTrace]
  refine ⟨88825423552519481755547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 947471184560207805392501 88825423552519481755547)
  ·
    refine ⟨133238135328779222633321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88825423552519481755547 133238135328779222633321)
    ·
      refine ⟨99928601496584416974991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133238135328779222633321 99928601496584416974991)
      ·
        refine ⟨149892902244876625462487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99928601496584416974991 149892902244876625462487)
        ·
          refine ⟨224839353367314938193731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149892902244876625462487 224839353367314938193731)
          ·
            refine ⟨337259030050972407290597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224839353367314938193731 337259030050972407290597)
            ·
              refine ⟨63236068134557326366987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 337259030050972407290597 63236068134557326366987)
              ·
                refine ⟨94854102201835989550481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63236068134557326366987 94854102201835989550481)
                ·
                  refine ⟨71140576651376992162861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 94854102201835989550481 71140576651376992162861)
                  ·
                    refine ⟨26677716244266372061073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 71140576651376992162861 26677716244266372061073)
                    ·
                      refine ⟨20008287183199779045805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 26677716244266372061073 20008287183199779045805)
                      ·
                        rfl

theorem cell23_38966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 1, 2, 3, 2].length) (baseStart_38966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_38966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_38966 prefixEnd_38966 := by exact prefixLift 38966
  have htrace : WordTrace (prefixWord ++ tailWord_38966) baseStart_38966 baseEnd_38966 := by
    simpa [prefixWord, tailWord_38966, baseEnd_38966] using wordTrace_append hprefix tailTrace_38966
  have hstable : (prefixWord ++ tailWord_38966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38966).length < 2 ^ (prefixWord ++ tailWord_38966).sum := by decide
  have hdescent : baseEnd_38966 < baseStart_38966 := by decide
  rcases family_descends (prefixWord ++ tailWord_38966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_38975 : List Nat := [1, 1, 2, 2, 3, 1, 3, 1, 3, 2, 4]
def baseStart_38975 : Nat := 118140960795 + 38975 * 2 ^ 59
def prefixEnd_38975 : Nat := 4983230072969 + 3 ^ 40 * 38975 * 2
def baseEnd_38975 : Nat := 20012908509090243833263

theorem tailTrace_38975 : CollatzResearch.WordTrace tailWord_38975 prefixEnd_38975 20012908509090243833263 := by
  unfold tailWord_38975
  simp only [CollatzResearch.WordTrace]
  refine ⟨1421535033807706245166379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 947690022538470830110919 1421535033807706245166379)
  ·
    refine ⟨2132302550711559367749569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1421535033807706245166379 2132302550711559367749569)
    ·
      refine ⟨1599226913033669525812177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2132302550711559367749569 1599226913033669525812177)
      ·
        refine ⟨1199420184775252144359133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1599226913033669525812177 1199420184775252144359133)
        ·
          refine ⟨449782569290719554134675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1199420184775252144359133 449782569290719554134675)
          ·
            refine ⟨674673853936079331202013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 449782569290719554134675 674673853936079331202013)
            ·
              refine ⟨253002695226029749200755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 674673853936079331202013 253002695226029749200755)
              ·
                refine ⟨379504042839044623801133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 253002695226029749200755 379504042839044623801133)
                ·
                  refine ⟨142314016064641733925425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 379504042839044623801133 142314016064641733925425)
                  ·
                    refine ⟨106735512048481300444069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 142314016064641733925425 106735512048481300444069)
                    ·
                      refine ⟨20012908509090243833263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 106735512048481300444069 20012908509090243833263)
                      ·
                        rfl

theorem cell23_38975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 3, 2, 4].length) (baseStart_38975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_38975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_38975 prefixEnd_38975 := by exact prefixLift 38975
  have htrace : WordTrace (prefixWord ++ tailWord_38975) baseStart_38975 baseEnd_38975 := by
    simpa [prefixWord, tailWord_38975, baseEnd_38975] using wordTrace_append hprefix tailTrace_38975
  have hstable : (prefixWord ++ tailWord_38975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_38975).length < 2 ^ (prefixWord ++ tailWord_38975).sum := by decide
  have hdescent : baseEnd_38975 < baseStart_38975 := by decide
  rcases family_descends (prefixWord ++ tailWord_38975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39012 : List Nat := [2, 3, 1, 1, 2, 1, 3, 3, 1, 3, 3]
def baseStart_39012 : Nat := 118140960795 + 39012 * 2 ^ 59
def prefixEnd_39012 : Nat := 4983230072969 + 3 ^ 40 * 39012 * 2
def baseEnd_39012 : Nat := 20031907293306599070593

theorem tailTrace_39012 : CollatzResearch.WordTrace tailWord_39012 prefixEnd_39012 20031907293306599070593 := by
  unfold tailWord_39012
  simp only [CollatzResearch.WordTrace]
  refine ⟨711442267336830782131645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 948589689782441042842193 711442267336830782131645)
  ·
    refine ⟨266790850251311543299367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 711442267336830782131645 266790850251311543299367)
    ·
      refine ⟨400186275376967314949051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266790850251311543299367 400186275376967314949051)
      ·
        refine ⟨600279413065450972423577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 400186275376967314949051 600279413065450972423577)
        ·
          refine ⟨450209559799088229317683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 600279413065450972423577 450209559799088229317683)
          ·
            refine ⟨675314339698632343976525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 450209559799088229317683 675314339698632343976525)
            ·
              refine ⟨253242877386987128991197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 675314339698632343976525 253242877386987128991197)
              ·
                refine ⟨94966079020120173371699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 253242877386987128991197 94966079020120173371699)
                ·
                  refine ⟨142449118530180260057549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 94966079020120173371699 142449118530180260057549)
                  ·
                    refine ⟨53418419448817597521581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 142449118530180260057549 53418419448817597521581)
                    ·
                      refine ⟨20031907293306599070593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 53418419448817597521581 20031907293306599070593)
                      ·
                        rfl

theorem cell23_39012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 3, 1, 3, 3].length) (baseStart_39012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_39012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_39012 prefixEnd_39012 := by exact prefixLift 39012
  have htrace : WordTrace (prefixWord ++ tailWord_39012) baseStart_39012 baseEnd_39012 := by
    simpa [prefixWord, tailWord_39012, baseEnd_39012] using wordTrace_append hprefix tailTrace_39012
  have hstable : (prefixWord ++ tailWord_39012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39012).length < 2 ^ (prefixWord ++ tailWord_39012).sum := by decide
  have hdescent : baseEnd_39012 < baseStart_39012 := by decide
  rcases family_descends (prefixWord ++ tailWord_39012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39015 : List Nat := [1, 1, 5, 1, 1, 2, 1, 2, 2, 7]
def baseStart_39015 : Nat := 118140960795 + 39015 * 2 ^ 59
def prefixEnd_39015 : Nat := 4983230072969 + 3 ^ 40 * 39015 * 2
def baseEnd_39015 : Nat := 6677815911756695777693

theorem tailTrace_39015 : CollatzResearch.WordTrace tailWord_39015 prefixEnd_39015 6677815911756695777693 := by
  unfold tailWord_39015
  simp only [CollatzResearch.WordTrace]
  refine ⟨1422993953662793076622499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 948662635775195384414999 1422993953662793076622499)
  ·
    refine ⟨2134490930494189614933749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1422993953662793076622499 2134490930494189614933749)
    ·
      refine ⟨200108524733830276400039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2134490930494189614933749 200108524733830276400039)
      ·
        refine ⟨300162787100745414600059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200108524733830276400039 300162787100745414600059)
        ·
          refine ⟨450244180651118121900089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 300162787100745414600059 450244180651118121900089)
          ·
            refine ⟨337683135488338591425067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 450244180651118121900089 337683135488338591425067)
            ·
              refine ⟨506524703232507887137601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 337683135488338591425067 506524703232507887137601)
              ·
                refine ⟨379893527424380915353201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 506524703232507887137601 379893527424380915353201)
                ·
                  refine ⟨284920145568285686514901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 379893527424380915353201 284920145568285686514901)
                  ·
                    refine ⟨6677815911756695777693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 284920145568285686514901 6677815911756695777693)
                    ·
                      rfl

theorem cell23_39015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 2, 7].length) (baseStart_39015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_39015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_39015 prefixEnd_39015 := by exact prefixLift 39015
  have htrace : WordTrace (prefixWord ++ tailWord_39015) baseStart_39015 baseEnd_39015 := by
    simpa [prefixWord, tailWord_39015, baseEnd_39015] using wordTrace_append hprefix tailTrace_39015
  have hstable : (prefixWord ++ tailWord_39015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39015).length < 2 ^ (prefixWord ++ tailWord_39015).sum := by decide
  have hdescent : baseEnd_39015 < baseStart_39015 := by decide
  rcases family_descends (prefixWord ++ tailWord_39015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39025 : List Nat := [1, 2, 2, 2, 1, 1, 4, 1, 2, 2, 5]
def baseStart_39025 : Nat := 118140960795 + 39025 * 2 ^ 59
def prefixEnd_39025 : Nat := 4983230072969 + 3 ^ 40 * 39025 * 2
def baseEnd_39025 : Nat := 20038582541815048208033

theorem tailTrace_39025 : CollatzResearch.WordTrace tailWord_39025 prefixEnd_39025 20038582541815048208033 := by
  unfold tailWord_39025
  simp only [CollatzResearch.WordTrace]
  refine ⟨1423358683626564784486529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 948905789084376522991019 1423358683626564784486529)
  ·
    refine ⟨1067519012719923588364897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1423358683626564784486529 1067519012719923588364897)
    ·
      refine ⟨800639259539942691273673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1067519012719923588364897 800639259539942691273673)
      ·
        refine ⟨600479444654957018455255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 800639259539942691273673 600479444654957018455255)
        ·
          refine ⟨900719166982435527682883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 600479444654957018455255 900719166982435527682883)
          ·
            refine ⟨1351078750473653291524325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 900719166982435527682883 1351078750473653291524325)
            ·
              refine ⟨253327265713809992160811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1351078750473653291524325 253327265713809992160811)
              ·
                refine ⟨379990898570714988241217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 253327265713809992160811 379990898570714988241217)
                ·
                  refine ⟨284993173928036241180913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 379990898570714988241217 284993173928036241180913)
                  ·
                    refine ⟨213744880446027180885685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 284993173928036241180913 213744880446027180885685)
                    ·
                      refine ⟨20038582541815048208033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 213744880446027180885685 20038582541815048208033)
                      ·
                        rfl

theorem cell23_39025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 2, 2, 5].length) (baseStart_39025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_39025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_39025 prefixEnd_39025 := by exact prefixLift 39025
  have htrace : WordTrace (prefixWord ++ tailWord_39025) baseStart_39025 baseEnd_39025 := by
    simpa [prefixWord, tailWord_39025, baseEnd_39025] using wordTrace_append hprefix tailTrace_39025
  have hstable : (prefixWord ++ tailWord_39025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39025).length < 2 ^ (prefixWord ++ tailWord_39025).sum := by decide
  have hdescent : baseEnd_39025 < baseStart_39025 := by decide
  rcases family_descends (prefixWord ++ tailWord_39025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39030 : List Nat := [5, 1, 1, 2, 1, 3, 2, 3, 1, 2, 2]
def baseStart_39030 : Nat := 118140960795 + 39030 * 2 ^ 59
def prefixEnd_39030 : Nat := 4983230072969 + 3 ^ 40 * 39030 * 2
def baseEnd_39030 : Nat := 20041149945087528645511

theorem tailTrace_39030 : CollatzResearch.WordTrace tailWord_39030 prefixEnd_39030 20041149945087528645511 := by
  unfold tailWord_39030
  simp only [CollatzResearch.WordTrace]
  refine ⟨88971315538028164901159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 949027365738967092279029 88971315538028164901159)
  ·
    refine ⟨133456973307042247351739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88971315538028164901159 133456973307042247351739)
    ·
      refine ⟨200185459960563371027609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133456973307042247351739 200185459960563371027609)
      ·
        refine ⟨150139094970422528270707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200185459960563371027609 150139094970422528270707)
        ·
          refine ⟨225208642455633792406061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150139094970422528270707 225208642455633792406061)
          ·
            refine ⟨84453240920862672152273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 225208642455633792406061 84453240920862672152273)
            ·
              refine ⟨63339930690647004114205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84453240920862672152273 63339930690647004114205)
              ·
                refine ⟨23752474008992626542827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63339930690647004114205 23752474008992626542827)
                ·
                  refine ⟨35628711013488939814241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23752474008992626542827 35628711013488939814241)
                  ·
                    refine ⟨26721533260116704860681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35628711013488939814241 26721533260116704860681)
                    ·
                      refine ⟨20041149945087528645511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 26721533260116704860681 20041149945087528645511)
                      ·
                        rfl

theorem cell23_39030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 3, 1, 2, 2].length) (baseStart_39030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_39030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_39030 prefixEnd_39030 := by exact prefixLift 39030
  have htrace : WordTrace (prefixWord ++ tailWord_39030) baseStart_39030 baseEnd_39030 := by
    simpa [prefixWord, tailWord_39030, baseEnd_39030] using wordTrace_append hprefix tailTrace_39030
  have hstable : (prefixWord ++ tailWord_39030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39030).length < 2 ^ (prefixWord ++ tailWord_39030).sum := by decide
  have hdescent : baseEnd_39030 < baseStart_39030 := by decide
  rcases family_descends (prefixWord ++ tailWord_39030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39052 : List Nat := [2, 2, 1, 2, 1, 1, 1, 1, 2, 8, 2]
def baseStart_39052 : Nat := 118140960795 + 39052 * 2 ^ 59
def prefixEnd_39052 : Nat := 4983230072969 + 3 ^ 40 * 39052 * 2
def baseEnd_39052 : Nat := 20052446519486442570409

theorem tailTrace_39052 : CollatzResearch.WordTrace tailWord_39052 prefixEnd_39052 20052446519486442570409 := by
  unfold tailWord_39052
  simp only [CollatzResearch.WordTrace]
  refine ⟨712171727264374197859705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 949562303019165597146273 712171727264374197859705)
  ·
    refine ⟨534128795448280648394779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 712171727264374197859705 534128795448280648394779)
    ·
      refine ⟨801193193172420972592169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 534128795448280648394779 801193193172420972592169)
      ·
        refine ⟨600894894879315729444127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 801193193172420972592169 600894894879315729444127)
        ·
          refine ⟨901342342318973594166191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 600894894879315729444127 901342342318973594166191)
          ·
            refine ⟨1352013513478460391249287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 901342342318973594166191 1352013513478460391249287)
            ·
              refine ⟨2028020270217690586873931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1352013513478460391249287 2028020270217690586873931)
              ·
                refine ⟨3042030405326535880310897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2028020270217690586873931 3042030405326535880310897)
                ·
                  refine ⟨2281522803994901910233173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3042030405326535880310897 2281522803994901910233173)
                  ·
                    refine ⟨26736595359315256760545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 2281522803994901910233173 26736595359315256760545)
                    ·
                      refine ⟨20052446519486442570409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 26736595359315256760545 20052446519486442570409)
                      ·
                        rfl

theorem cell23_39052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 2, 8, 2].length) (baseStart_39052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_39052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_39052 prefixEnd_39052 := by exact prefixLift 39052
  have htrace : WordTrace (prefixWord ++ tailWord_39052) baseStart_39052 baseEnd_39052 := by
    simpa [prefixWord, tailWord_39052, baseEnd_39052] using wordTrace_append hprefix tailTrace_39052
  have hstable : (prefixWord ++ tailWord_39052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39052).length < 2 ^ (prefixWord ++ tailWord_39052).sum := by decide
  have hdescent : baseEnd_39052 < baseStart_39052 := by decide
  rcases family_descends (prefixWord ++ tailWord_39052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39063 : List Nat := [1, 1, 3, 3, 4, 1, 3, 1, 2, 1, 3]
def baseStart_39063 : Nat := 118140960795 + 39063 * 2 ^ 59
def prefixEnd_39063 : Nat := 4983230072969 + 3 ^ 40 * 39063 * 2
def baseEnd_39063 : Nat := 20058094806685899532859

theorem tailTrace_39063 : CollatzResearch.WordTrace tailWord_39063 prefixEnd_39063 20058094806685899532859 := by
  unfold tailWord_39063
  simp only [CollatzResearch.WordTrace]
  refine ⟨1424744657488897274369843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 949829771659264849579895 1424744657488897274369843)
  ·
    refine ⟨2137116986233345911554765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1424744657488897274369843 2137116986233345911554765)
    ·
      refine ⟨801418869837504716833037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2137116986233345911554765 801418869837504716833037)
      ·
        refine ⟨300532076189064268812389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 801418869837504716833037 300532076189064268812389)
        ·
          refine ⟨56349764285449550402323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 300532076189064268812389 56349764285449550402323)
          ·
            refine ⟨84524646428174325603485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56349764285449550402323 84524646428174325603485)
            ·
              refine ⟨31696742410565372101307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84524646428174325603485 31696742410565372101307)
              ·
                refine ⟨47545113615848058151961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31696742410565372101307 47545113615848058151961)
                ·
                  refine ⟨35658835211886043613971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47545113615848058151961 35658835211886043613971)
                  ·
                    refine ⟨53488252817829065420957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35658835211886043613971 53488252817829065420957)
                    ·
                      refine ⟨20058094806685899532859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 53488252817829065420957 20058094806685899532859)
                      ·
                        rfl

theorem cell23_39063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 3, 1, 2, 1, 3].length) (baseStart_39063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_39063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_39063 prefixEnd_39063 := by exact prefixLift 39063
  have htrace : WordTrace (prefixWord ++ tailWord_39063) baseStart_39063 baseEnd_39063 := by
    simpa [prefixWord, tailWord_39063, baseEnd_39063] using wordTrace_append hprefix tailTrace_39063
  have hstable : (prefixWord ++ tailWord_39063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39063).length < 2 ^ (prefixWord ++ tailWord_39063).sum := by decide
  have hdescent : baseEnd_39063 < baseStart_39063 := by decide
  rcases family_descends (prefixWord ++ tailWord_39063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39089 : List Nat := [1, 2, 2, 5, 2, 1, 1, 1, 2, 1, 5]
def baseStart_39089 : Nat := 118140960795 + 39089 * 2 ^ 59
def prefixEnd_39089 : Nat := 4983230072969 + 3 ^ 40 * 39089 * 2
def baseEnd_39089 : Nat := 20071445303702797807739

theorem tailTrace_39089 : CollatzResearch.WordTrace tailWord_39089 prefixEnd_39089 20071445303702797807739 := by
  unfold tailWord_39089
  simp only [CollatzResearch.WordTrace]
  refine ⟨1425692955394703714816321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 950461970263135809877547 1425692955394703714816321)
  ·
    refine ⟨1069269716546027786112241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1425692955394703714816321 1069269716546027786112241)
    ·
      refine ⟨801952287409520839584181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1069269716546027786112241 801952287409520839584181)
      ·
        refine ⟨75183026944642578711017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 801952287409520839584181 75183026944642578711017)
        ·
          refine ⟨56387270208481934033263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75183026944642578711017 56387270208481934033263)
          ·
            refine ⟨84580905312722901049895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56387270208481934033263 84580905312722901049895)
            ·
              refine ⟨126871357969084351574843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84580905312722901049895 126871357969084351574843)
              ·
                refine ⟨190307036953626527362265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126871357969084351574843 190307036953626527362265)
                ·
                  refine ⟨142730277715219895521699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 190307036953626527362265 142730277715219895521699)
                  ·
                    refine ⟨214095416572829843282549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 142730277715219895521699 214095416572829843282549)
                    ·
                      refine ⟨20071445303702797807739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 214095416572829843282549 20071445303702797807739)
                      ·
                        rfl

theorem cell23_39089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_39089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_39089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_39089 prefixEnd_39089 := by exact prefixLift 39089
  have htrace : WordTrace (prefixWord ++ tailWord_39089) baseStart_39089 baseEnd_39089 := by
    simpa [prefixWord, tailWord_39089, baseEnd_39089] using wordTrace_append hprefix tailTrace_39089
  have hstable : (prefixWord ++ tailWord_39089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39089).length < 2 ^ (prefixWord ++ tailWord_39089).sum := by decide
  have hdescent : baseEnd_39089 < baseStart_39089 := by decide
  rcases family_descends (prefixWord ++ tailWord_39089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39169 : List Nat := [1, 2, 4, 1, 1, 2, 2, 3, 3, 4]
def baseStart_39169 : Nat := 118140960795 + 39169 * 2 ^ 59
def prefixEnd_39169 : Nat := 4983230072969 + 3 ^ 40 * 39169 * 2
def baseEnd_39169 : Nat := 6704174585354161602457

theorem tailTrace_39169 : CollatzResearch.WordTrace tailWord_39169 prefixEnd_39169 6704174585354161602457 := by
  unfold tailWord_39169
  simp only [CollatzResearch.WordTrace]
  refine ⟨1428610795104877377728561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 952407196736584918485707 1428610795104877377728561)
  ·
    refine ⟨1071458096328658033296421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1428610795104877377728561 1071458096328658033296421)
    ·
      refine ⟨200898393061623381243079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1071458096328658033296421 200898393061623381243079)
      ·
        refine ⟨301347589592435071864619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200898393061623381243079 301347589592435071864619)
        ·
          refine ⟨452021384388652607796929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 301347589592435071864619 452021384388652607796929)
          ·
            refine ⟨339016038291489455847697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 452021384388652607796929 339016038291489455847697)
            ·
              refine ⟨254262028718617091885773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 339016038291489455847697 254262028718617091885773)
              ·
                refine ⟨95348260769481409457165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 254262028718617091885773 95348260769481409457165)
                ·
                  refine ⟨35755597788555528546437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 95348260769481409457165 35755597788555528546437)
                  ·
                    refine ⟨6704174585354161602457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35755597788555528546437 6704174585354161602457)
                    ·
                      rfl

theorem cell23_39169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 3, 3, 4].length) (baseStart_39169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_39169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_39169 prefixEnd_39169 := by exact prefixLift 39169
  have htrace : WordTrace (prefixWord ++ tailWord_39169) baseStart_39169 baseEnd_39169 := by
    simpa [prefixWord, tailWord_39169, baseEnd_39169] using wordTrace_append hprefix tailTrace_39169
  have hstable : (prefixWord ++ tailWord_39169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39169).length < 2 ^ (prefixWord ++ tailWord_39169).sum := by decide
  have hdescent : baseEnd_39169 < baseStart_39169 := by decide
  rcases family_descends (prefixWord ++ tailWord_39169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39176 : List Nat := [2, 1, 3, 2, 3, 2, 1, 1, 2, 4, 2]
def baseStart_39176 : Nat := 118140960795 + 39176 * 2 ^ 59
def prefixEnd_39176 : Nat := 4983230072969 + 3 ^ 40 * 39176 * 2
def baseEnd_39176 : Nat := 20116118120643957419839

theorem tailTrace_39176 : CollatzResearch.WordTrace tailWord_39176 prefixEnd_39176 20116118120643957419839 := by
  unfold tailWord_39176
  simp only [CollatzResearch.WordTrace]
  refine ⟨714433053039758786616691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 952577404053011715488921 714433053039758786616691)
  ·
    refine ⟨1071649579559638179925037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 714433053039758786616691 1071649579559638179925037)
    ·
      refine ⟨401868592334864317471889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1071649579559638179925037 401868592334864317471889)
      ·
        refine ⟨301401444251148238103917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 401868592334864317471889 301401444251148238103917)
        ·
          refine ⟨113025541594180589288969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 301401444251148238103917 113025541594180589288969)
          ·
            refine ⟨84769156195635441966727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113025541594180589288969 84769156195635441966727)
            ·
              refine ⟨127153734293453162950091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84769156195635441966727 127153734293453162950091)
              ·
                refine ⟨190730601440179744425137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 127153734293453162950091 190730601440179744425137)
                ·
                  refine ⟨143047951080134808318853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 190730601440179744425137 143047951080134808318853)
                  ·
                    refine ⟨26821490827525276559785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 143047951080134808318853 26821490827525276559785)
                    ·
                      refine ⟨20116118120643957419839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 26821490827525276559785 20116118120643957419839)
                      ·
                        rfl

theorem cell23_39176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 1, 2, 4, 2].length) (baseStart_39176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_39176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_39176 prefixEnd_39176 := by exact prefixLift 39176
  have htrace : WordTrace (prefixWord ++ tailWord_39176) baseStart_39176 baseEnd_39176 := by
    simpa [prefixWord, tailWord_39176, baseEnd_39176] using wordTrace_append hprefix tailTrace_39176
  have hstable : (prefixWord ++ tailWord_39176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39176).length < 2 ^ (prefixWord ++ tailWord_39176).sum := by decide
  have hdescent : baseEnd_39176 < baseStart_39176 := by decide
  rcases family_descends (prefixWord ++ tailWord_39176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39226 : List Nat := [3, 1, 1, 1, 4, 2, 1, 3, 3, 1, 3]
def baseStart_39226 : Nat := 118140960795 + 39226 * 2 ^ 59
def prefixEnd_39226 : Nat := 4983230072969 + 3 ^ 40 * 39226 * 2
def baseEnd_39226 : Nat := 20141792153368761794609

theorem tailTrace_39226 : CollatzResearch.WordTrace tailWord_39226 prefixEnd_39226 20141792153368761794609 := by
  unfold tailWord_39226
  simp only [CollatzResearch.WordTrace]
  refine ⟨357672438974594028138383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 953793170598917408369021 357672438974594028138383)
  ·
    refine ⟨536508658461891042207575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 357672438974594028138383 536508658461891042207575)
    ·
      refine ⟨804762987692836563311363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 536508658461891042207575 804762987692836563311363)
      ·
        refine ⟨1207144481539254844967045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 804762987692836563311363 1207144481539254844967045)
        ·
          refine ⟨226339590288610283431321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1207144481539254844967045 226339590288610283431321)
          ·
            refine ⟨169754692716457712573491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 226339590288610283431321 169754692716457712573491)
            ·
              refine ⟨254632039074686568860237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 169754692716457712573491 254632039074686568860237)
              ·
                refine ⟨95487014653007463322589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 254632039074686568860237 95487014653007463322589)
                ·
                  refine ⟨35807630494877798745971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 95487014653007463322589 35807630494877798745971)
                  ·
                    refine ⟨53711445742316698118957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35807630494877798745971 53711445742316698118957)
                    ·
                      refine ⟨20141792153368761794609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 53711445742316698118957 20141792153368761794609)
                      ·
                        rfl

theorem cell23_39226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 3, 3, 1, 3].length) (baseStart_39226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_39226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_39226 prefixEnd_39226 := by exact prefixLift 39226
  have htrace : WordTrace (prefixWord ++ tailWord_39226) baseStart_39226 baseEnd_39226 := by
    simpa [prefixWord, tailWord_39226, baseEnd_39226] using wordTrace_append hprefix tailTrace_39226
  have hstable : (prefixWord ++ tailWord_39226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39226).length < 2 ^ (prefixWord ++ tailWord_39226).sum := by decide
  have hdescent : baseEnd_39226 < baseStart_39226 := by decide
  rcases family_descends (prefixWord ++ tailWord_39226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39232 : List Nat := [2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 4]
def baseStart_39232 : Nat := 118140960795 + 39232 * 2 ^ 59
def prefixEnd_39232 : Nat := 4983230072969 + 3 ^ 40 * 39232 * 2
def baseEnd_39232 : Nat := 20144873037295738319581

theorem tailTrace_39232 : CollatzResearch.WordTrace tailWord_39232 prefixEnd_39232 20144873037295738319581 := by
  unfold tailWord_39232
  simp only [CollatzResearch.WordTrace]
  refine ⟨715454296938319568635975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 953939062584426091514633 715454296938319568635975)
  ·
    refine ⟨1073181445407479352953963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 715454296938319568635975 1073181445407479352953963)
    ·
      refine ⟨1609772168111219029430945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1073181445407479352953963 1609772168111219029430945)
      ·
        refine ⟨1207329126083414272073209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1609772168111219029430945 1207329126083414272073209)
        ·
          refine ⟨905496844562560704054907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1207329126083414272073209 905496844562560704054907)
          ·
            refine ⟨1358245266843841056082361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 905496844562560704054907 1358245266843841056082361)
            ·
              refine ⟨1018683950132880792061771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1358245266843841056082361 1018683950132880792061771)
              ·
                refine ⟨1528025925199321188092657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1018683950132880792061771 1528025925199321188092657)
                ·
                  refine ⟨1146019443899490891069493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1528025925199321188092657 1146019443899490891069493)
                  ·
                    refine ⟨107439322865577271037765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1146019443899490891069493 107439322865577271037765)
                    ·
                      refine ⟨20144873037295738319581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 107439322865577271037765 20144873037295738319581)
                      ·
                        rfl

theorem cell23_39232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 4].length) (baseStart_39232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_39232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_39232 prefixEnd_39232 := by exact prefixLift 39232
  have htrace : WordTrace (prefixWord ++ tailWord_39232) baseStart_39232 baseEnd_39232 := by
    simpa [prefixWord, tailWord_39232, baseEnd_39232] using wordTrace_append hprefix tailTrace_39232
  have hstable : (prefixWord ++ tailWord_39232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39232).length < 2 ^ (prefixWord ++ tailWord_39232).sum := by decide
  have hdescent : baseEnd_39232 < baseStart_39232 := by decide
  rcases family_descends (prefixWord ++ tailWord_39232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39233 : List Nat := [1, 2, 5, 2, 2, 1, 3, 1, 6]
def baseStart_39233 : Nat := 118140960795 + 39233 * 2 ^ 59
def prefixEnd_39233 : Nat := 4983230072969 + 3 ^ 40 * 39233 * 2
def baseEnd_39233 : Nat := 2238376279772248267453

theorem tailTrace_39233 : CollatzResearch.WordTrace tailWord_39233 prefixEnd_39233 2238376279772248267453 := by
  unfold tailWord_39233
  simp only [CollatzResearch.WordTrace]
  refine ⟨1430945066873016308058353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 953963377915344205372235 1430945066873016308058353)
  ·
    refine ⟨1073208800154762231043765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1430945066873016308058353 1073208800154762231043765)
    ·
      refine ⟨100613325014508959160353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1073208800154762231043765 100613325014508959160353)
      ·
        refine ⟨75459993760881719370265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100613325014508959160353 75459993760881719370265)
        ·
          refine ⟨56594995320661289527699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75459993760881719370265 56594995320661289527699)
          ·
            refine ⟨84892492980991934291549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56594995320661289527699 84892492980991934291549)
            ·
              refine ⟨31834684867871975359331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84892492980991934291549 31834684867871975359331)
              ·
                refine ⟨47752027301807963038997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31834684867871975359331 47752027301807963038997)
                ·
                  refine ⟨2238376279772248267453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 47752027301807963038997 2238376279772248267453)
                  ·
                    rfl

theorem cell23_39233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 3, 1, 6].length) (baseStart_39233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_39233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_39233 prefixEnd_39233 := by exact prefixLift 39233
  have htrace : WordTrace (prefixWord ++ tailWord_39233) baseStart_39233 baseEnd_39233 := by
    simpa [prefixWord, tailWord_39233, baseEnd_39233] using wordTrace_append hprefix tailTrace_39233
  have hstable : (prefixWord ++ tailWord_39233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39233).length < 2 ^ (prefixWord ++ tailWord_39233).sum := by decide
  have hdescent : baseEnd_39233 < baseStart_39233 := by decide
  rcases family_descends (prefixWord ++ tailWord_39233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39269 : List Nat := [1, 3, 1, 3, 1, 3, 1, 3, 1, 1, 5]
def baseStart_39269 : Nat := 118140960795 + 39269 * 2 ^ 59
def prefixEnd_39269 : Nat := 4983230072969 + 3 ^ 40 * 39269 * 2
def baseEnd_39269 : Nat := 20163871821512093556911

theorem tailTrace_39269 : CollatzResearch.WordTrace tailWord_39269 prefixEnd_39269 20163871821512093556911 := by
  unfold tailWord_39269
  simp only [CollatzResearch.WordTrace]
  refine ⟨1432258094742594456368861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 954838729828396304245907 1432258094742594456368861)
  ·
    refine ⟨537096785528472921138323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1432258094742594456368861 537096785528472921138323)
    ·
      refine ⟨805645178292709381707485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 537096785528472921138323 805645178292709381707485)
      ·
        refine ⟨302116941859766018140307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 805645178292709381707485 302116941859766018140307)
        ·
          refine ⟨453175412789649027210461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 302116941859766018140307 453175412789649027210461)
          ·
            refine ⟨169940779796118385203923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 453175412789649027210461 169940779796118385203923)
            ·
              refine ⟨254911169694177577805885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 169940779796118385203923 254911169694177577805885)
              ·
                refine ⟨95591688635316591677207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 254911169694177577805885 95591688635316591677207)
                ·
                  refine ⟨143387532952974887515811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95591688635316591677207 143387532952974887515811)
                  ·
                    refine ⟨215081299429462331273717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 143387532952974887515811 215081299429462331273717)
                    ·
                      refine ⟨20163871821512093556911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 215081299429462331273717 20163871821512093556911)
                      ·
                        rfl

theorem cell23_39269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_39269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_39269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_39269 prefixEnd_39269 := by exact prefixLift 39269
  have htrace : WordTrace (prefixWord ++ tailWord_39269) baseStart_39269 baseEnd_39269 := by
    simpa [prefixWord, tailWord_39269, baseEnd_39269] using wordTrace_append hprefix tailTrace_39269
  have hstable : (prefixWord ++ tailWord_39269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39269).length < 2 ^ (prefixWord ++ tailWord_39269).sum := by decide
  have hdescent : baseEnd_39269 < baseStart_39269 := by decide
  rcases family_descends (prefixWord ++ tailWord_39269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39293 : List Nat := [1, 4, 1, 1, 2, 3, 4, 1, 2, 4]
def baseStart_39293 : Nat := 118140960795 + 39293 * 2 ^ 59
def prefixEnd_39293 : Nat := 4983230072969 + 3 ^ 40 * 39293 * 2
def baseEnd_39293 : Nat := 6725398452406666552267

theorem tailTrace_39293 : CollatzResearch.WordTrace tailWord_39293 prefixEnd_39293 6725398452406666552267 := by
  unfold tailWord_39293
  simp only [CollatzResearch.WordTrace]
  refine ⟨1433133446655646555242533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 955422297770431036828355 1433133446655646555242533)
  ·
    refine ⟨268712521247933729107975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1433133446655646555242533 268712521247933729107975)
    ·
      refine ⟨403068781871900593661963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268712521247933729107975 403068781871900593661963)
      ·
        refine ⟨604603172807850890492945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 403068781871900593661963 604603172807850890492945)
        ·
          refine ⟨453452379605888167869709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 604603172807850890492945 453452379605888167869709)
          ·
            refine ⟨170044642352208062951141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 453452379605888167869709 170044642352208062951141)
            ·
              refine ⟨31883370441039011803339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 170044642352208062951141 31883370441039011803339)
              ·
                refine ⟨47825055661558517705009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31883370441039011803339 47825055661558517705009)
                ·
                  refine ⟨35868791746168888278757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47825055661558517705009 35868791746168888278757)
                  ·
                    refine ⟨6725398452406666552267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35868791746168888278757 6725398452406666552267)
                    ·
                      rfl

theorem cell23_39293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 4, 1, 2, 4].length) (baseStart_39293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_39293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_39293 prefixEnd_39293 := by exact prefixLift 39293
  have htrace : WordTrace (prefixWord ++ tailWord_39293) baseStart_39293 baseEnd_39293 := by
    simpa [prefixWord, tailWord_39293, baseEnd_39293] using wordTrace_append hprefix tailTrace_39293
  have hstable : (prefixWord ++ tailWord_39293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39293).length < 2 ^ (prefixWord ++ tailWord_39293).sum := by decide
  have hdescent : baseEnd_39293 < baseStart_39293 := by decide
  rcases family_descends (prefixWord ++ tailWord_39293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39320 : List Nat := [2, 1, 2, 5, 1, 2, 3, 1, 1, 2, 3]
def baseStart_39320 : Nat := 118140960795 + 39320 * 2 ^ 59
def prefixEnd_39320 : Nat := 4983230072969 + 3 ^ 40 * 39320 * 2
def baseEnd_39320 : Nat := 20190059334891394019177

theorem tailTrace_39320 : CollatzResearch.WordTrace tailWord_39320 prefixEnd_39320 20190059334891394019177 := by
  unfold tailWord_39320
  simp only [CollatzResearch.WordTrace]
  refine ⟨717059108778915083237707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 956078811705220110983609 717059108778915083237707)
  ·
    refine ⟨1075588663168372624856561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 717059108778915083237707 1075588663168372624856561)
    ·
      refine ⟨806691497376279468642421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1075588663168372624856561 806691497376279468642421)
      ·
        refine ⟨75627327879026200185227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 806691497376279468642421 75627327879026200185227)
        ·
          refine ⟨113440991818539300277841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75627327879026200185227 113440991818539300277841)
          ·
            refine ⟨85080743863904475208381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113440991818539300277841 85080743863904475208381)
            ·
              refine ⟨31905278948964178203143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85080743863904475208381 31905278948964178203143)
              ·
                refine ⟨47857918423446267304715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31905278948964178203143 47857918423446267304715)
                ·
                  refine ⟨71786877635169400957073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47857918423446267304715 71786877635169400957073)
                  ·
                    refine ⟨53840158226377050717805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 71786877635169400957073 53840158226377050717805)
                    ·
                      refine ⟨20190059334891394019177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 53840158226377050717805 20190059334891394019177)
                      ·
                        rfl

theorem cell23_39320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_39320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_39320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_39320 prefixEnd_39320 := by exact prefixLift 39320
  have htrace : WordTrace (prefixWord ++ tailWord_39320) baseStart_39320 baseEnd_39320 := by
    simpa [prefixWord, tailWord_39320, baseEnd_39320] using wordTrace_append hprefix tailTrace_39320
  have hstable : (prefixWord ++ tailWord_39320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39320).length < 2 ^ (prefixWord ++ tailWord_39320).sum := by decide
  have hdescent : baseEnd_39320 < baseStart_39320 := by decide
  rcases family_descends (prefixWord ++ tailWord_39320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39333 : List Nat := [1, 3, 1, 2, 1, 1, 6, 2, 2, 1, 3]
def baseStart_39333 : Nat := 118140960795 + 39333 * 2 ^ 59
def prefixEnd_39333 : Nat := 4983230072969 + 3 ^ 40 * 39333 * 2
def baseEnd_39333 : Nat := 20196734583399843156617

theorem tailTrace_39333 : CollatzResearch.WordTrace tailWord_39333 prefixEnd_39333 20196734583399843156617 := by
  unfold tailWord_39333
  simp only [CollatzResearch.WordTrace]
  refine ⟨1434592366510733386698653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 956394911007155591132435 1434592366510733386698653)
  ·
    refine ⟨537972137441525020011995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1434592366510733386698653 537972137441525020011995)
    ·
      refine ⟨806958206162287530017993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 537972137441525020011995 806958206162287530017993)
      ·
        refine ⟨605218654621715647513495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 806958206162287530017993 605218654621715647513495)
        ·
          refine ⟨907827981932573471270243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 605218654621715647513495 907827981932573471270243)
          ·
            refine ⟨1361741972898860206905365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 907827981932573471270243 1361741972898860206905365)
            ·
              refine ⟨63831654979634072198689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1361741972898860206905365 63831654979634072198689)
              ·
                refine ⟨47873741234725554149017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63831654979634072198689 47873741234725554149017)
                ·
                  refine ⟨35905305926044165611763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47873741234725554149017 35905305926044165611763)
                  ·
                    refine ⟨53857958889066248417645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35905305926044165611763 53857958889066248417645)
                    ·
                      refine ⟨20196734583399843156617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 53857958889066248417645 20196734583399843156617)
                      ·
                        rfl

theorem cell23_39333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 2, 2, 1, 3].length) (baseStart_39333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_39333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_39333 prefixEnd_39333 := by exact prefixLift 39333
  have htrace : WordTrace (prefixWord ++ tailWord_39333) baseStart_39333 baseEnd_39333 := by
    simpa [prefixWord, tailWord_39333, baseEnd_39333] using wordTrace_append hprefix tailTrace_39333
  have hstable : (prefixWord ++ tailWord_39333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39333).length < 2 ^ (prefixWord ++ tailWord_39333).sum := by decide
  have hdescent : baseEnd_39333 < baseStart_39333 := by decide
  rcases family_descends (prefixWord ++ tailWord_39333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39336 : List Nat := [2, 1, 6, 1, 1, 1, 1, 1, 2, 7]
def baseStart_39336 : Nat := 118140960795 + 39336 * 2 ^ 59
def prefixEnd_39336 : Nat := 4983230072969 + 3 ^ 40 * 39336 * 2
def baseEnd_39336 : Nat := 6732758341787777139701

theorem tailTrace_39336 : CollatzResearch.WordTrace tailWord_39336 prefixEnd_39336 6732758341787777139701 := by
  unfold tailWord_39336
  simp only [CollatzResearch.WordTrace]
  refine ⟨717350892749932449528931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 956467856999909932705241 717350892749932449528931)
  ·
    refine ⟨1076026339124898674293397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 717350892749932449528931 1076026339124898674293397)
    ·
      refine ⟨50438734646479625357503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1076026339124898674293397 50438734646479625357503)
      ·
        refine ⟨75658101969719438036255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50438734646479625357503 75658101969719438036255)
        ·
          refine ⟨113487152954579157054383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75658101969719438036255 113487152954579157054383)
          ·
            refine ⟨170230729431868735581575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113487152954579157054383 170230729431868735581575)
            ·
              refine ⟨255346094147803103372363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170230729431868735581575 255346094147803103372363)
              ·
                refine ⟨383019141221704655058545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 255346094147803103372363 383019141221704655058545)
                ·
                  refine ⟨287264355916278491293909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 383019141221704655058545 287264355916278491293909)
                  ·
                    refine ⟨6732758341787777139701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 287264355916278491293909 6732758341787777139701)
                    ·
                      rfl

theorem cell23_39336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_39336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_39336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_39336 prefixEnd_39336 := by exact prefixLift 39336
  have htrace : WordTrace (prefixWord ++ tailWord_39336) baseStart_39336 baseEnd_39336 := by
    simpa [prefixWord, tailWord_39336, baseEnd_39336] using wordTrace_append hprefix tailTrace_39336
  have hstable : (prefixWord ++ tailWord_39336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39336).length < 2 ^ (prefixWord ++ tailWord_39336).sum := by decide
  have hdescent : baseEnd_39336 < baseStart_39336 := by decide
  rcases family_descends (prefixWord ++ tailWord_39336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39409 : List Nat := [1, 2, 2, 2, 3, 1, 1, 1, 3, 7]
def baseStart_39409 : Nat := 118140960795 + 39409 * 2 ^ 59
def prefixEnd_39409 : Nat := 4983230072969 + 3 ^ 40 * 39409 * 2
def baseEnd_39409 : Nat := 6745253037713848602089

theorem tailTrace_39409 : CollatzResearch.WordTrace tailWord_39409 prefixEnd_39409 6745253037713848602089 := by
  unfold tailWord_39409
  simp only [CollatzResearch.WordTrace]
  refine ⟨1437364314235398366465281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 958242876156932244310187 1437364314235398366465281)
  ·
    refine ⟨1078023235676548774848961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1437364314235398366465281 1078023235676548774848961)
    ·
      refine ⟨808517426757411581136721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1078023235676548774848961 808517426757411581136721)
      ·
        refine ⟨606388070068058685852541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 808517426757411581136721 606388070068058685852541)
        ·
          refine ⟨227395526275522007194703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 606388070068058685852541 227395526275522007194703)
          ·
            refine ⟨341093289413283010792055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227395526275522007194703 341093289413283010792055)
            ·
              refine ⟨511639934119924516188083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 341093289413283010792055 511639934119924516188083)
              ·
                refine ⟨767459901179886774282125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 511639934119924516188083 767459901179886774282125)
                ·
                  refine ⟨287797462942457540355797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 767459901179886774282125 287797462942457540355797)
                  ·
                    refine ⟨6745253037713848602089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 287797462942457540355797 6745253037713848602089)
                    ·
                      rfl

theorem cell23_39409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 3, 7].length) (baseStart_39409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_39409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_39409 prefixEnd_39409 := by exact prefixLift 39409
  have htrace : WordTrace (prefixWord ++ tailWord_39409) baseStart_39409 baseEnd_39409 := by
    simpa [prefixWord, tailWord_39409, baseEnd_39409] using wordTrace_append hprefix tailTrace_39409
  have hstable : (prefixWord ++ tailWord_39409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39409).length < 2 ^ (prefixWord ++ tailWord_39409).sum := by decide
  have hdescent : baseEnd_39409 < baseStart_39409 := by decide
  rcases family_descends (prefixWord ++ tailWord_39409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39447 : List Nat := [1, 1, 3, 6, 1, 1, 3, 2, 5]
def baseStart_39447 : Nat := 118140960795 + 39447 * 2 ^ 59
def prefixEnd_39447 : Nat := 4983230072969 + 3 ^ 40 * 39447 * 2
def baseEnd_39447 : Nat := 2250585708668044125677

theorem tailTrace_39447 : CollatzResearch.WordTrace tailWord_39447 prefixEnd_39447 2250585708668044125677 := by
  unfold tailWord_39447
  simp only [CollatzResearch.WordTrace]
  refine ⟨1438750288097730856348595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 959166858731820570899063 1438750288097730856348595)
  ·
    refine ⟨2158125432146596284522893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1438750288097730856348595 2158125432146596284522893)
    ·
      refine ⟨809297037054973606696085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2158125432146596284522893 809297037054973606696085)
      ·
        refine ⟨37935798611951887813879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 809297037054973606696085 37935798611951887813879)
        ·
          refine ⟨56903697917927831720819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37935798611951887813879 56903697917927831720819)
          ·
            refine ⟨85355546876891747581229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56903697917927831720819 85355546876891747581229)
            ·
              refine ⟨32008330078834405342961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85355546876891747581229 32008330078834405342961)
              ·
                refine ⟨24006247559125804007221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32008330078834405342961 24006247559125804007221)
                ·
                  refine ⟨2250585708668044125677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24006247559125804007221 2250585708668044125677)
                  ·
                    rfl

theorem cell23_39447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 3, 2, 5].length) (baseStart_39447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_39447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_39447 prefixEnd_39447 := by exact prefixLift 39447
  have htrace : WordTrace (prefixWord ++ tailWord_39447) baseStart_39447 baseEnd_39447 := by
    simpa [prefixWord, tailWord_39447, baseEnd_39447] using wordTrace_append hprefix tailTrace_39447
  have hstable : (prefixWord ++ tailWord_39447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39447).length < 2 ^ (prefixWord ++ tailWord_39447).sum := by decide
  have hdescent : baseEnd_39447 < baseStart_39447 := by decide
  rcases family_descends (prefixWord ++ tailWord_39447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39449 : List Nat := [1, 2, 1, 2, 1, 1, 2, 3, 2, 3, 5]
def baseStart_39449 : Nat := 118140960795 + 39449 * 2 ^ 59
def prefixEnd_39449 : Nat := 4983230072969 + 3 ^ 40 * 39449 * 2
def baseEnd_39449 : Nat := 20256298339321389306083

theorem tailTrace_39449 : CollatzResearch.WordTrace tailWord_39449 prefixEnd_39449 20256298339321389306083 := by
  unfold tailWord_39449
  simp only [CollatzResearch.WordTrace]
  refine ⟨1438823234090485197921401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 959215489393656798614267 1438823234090485197921401)
  ·
    refine ⟨1079117425567863898441051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1438823234090485197921401 1079117425567863898441051)
    ·
      refine ⟨1618676138351795847661577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1079117425567863898441051 1618676138351795847661577)
      ·
        refine ⟨1214007103763846885746183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1618676138351795847661577 1214007103763846885746183)
        ·
          refine ⟨1821010655645770328619275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1214007103763846885746183 1821010655645770328619275)
          ·
            refine ⟨2731515983468655492928913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1821010655645770328619275 2731515983468655492928913)
            ·
              refine ⟨2048636987601491619696685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2731515983468655492928913 2048636987601491619696685)
              ·
                refine ⟨768238870350559357386257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2048636987601491619696685 768238870350559357386257)
                ·
                  refine ⟨576179152762919518039693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 768238870350559357386257 576179152762919518039693)
                  ·
                    refine ⟨216067182286094819264885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 576179152762919518039693 216067182286094819264885)
                    ·
                      refine ⟨20256298339321389306083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 216067182286094819264885 20256298339321389306083)
                      ·
                        rfl

theorem cell23_39449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 3, 5].length) (baseStart_39449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_39449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_39449 prefixEnd_39449 := by exact prefixLift 39449
  have htrace : WordTrace (prefixWord ++ tailWord_39449) baseStart_39449 baseEnd_39449 := by
    simpa [prefixWord, tailWord_39449, baseEnd_39449] using wordTrace_append hprefix tailTrace_39449
  have hstable : (prefixWord ++ tailWord_39449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39449).length < 2 ^ (prefixWord ++ tailWord_39449).sum := by decide
  have hdescent : baseEnd_39449 < baseStart_39449 := by decide
  rcases family_descends (prefixWord ++ tailWord_39449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39506 : List Nat := [3, 2, 2, 1, 2, 1, 2, 1, 1, 2, 6]
def baseStart_39506 : Nat := 118140960795 + 39506 * 2 ^ 59
def prefixEnd_39506 : Nat := 4983230072969 + 3 ^ 40 * 39506 * 2
def baseEnd_39506 : Nat := 20285566736627666293321

theorem tailTrace_39506 : CollatzResearch.WordTrace tailWord_39506 prefixEnd_39506 20285566736627666293321 := by
  unfold tailWord_39506
  simp only [CollatzResearch.WordTrace]
  refine ⟨360225548720995983186593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 960601463255989288497581 360225548720995983186593)
  ·
    refine ⟨270169161540746987389945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 360225548720995983186593 270169161540746987389945)
    ·
      refine ⟨202626871155560240542459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 270169161540746987389945 202626871155560240542459)
      ·
        refine ⟨303940306733340360813689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202626871155560240542459 303940306733340360813689)
        ·
          refine ⟨227955230050005270610267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 303940306733340360813689 227955230050005270610267)
          ·
            refine ⟨341932845075007905915401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227955230050005270610267 341932845075007905915401)
            ·
              refine ⟨256449633806255929436551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 341932845075007905915401 256449633806255929436551)
              ·
                refine ⟨384674450709383894154827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 256449633806255929436551 384674450709383894154827)
                ·
                  refine ⟨577011676064075841232241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 384674450709383894154827 577011676064075841232241)
                  ·
                    refine ⟨432758757048056880924181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 577011676064075841232241 432758757048056880924181)
                    ·
                      refine ⟨20285566736627666293321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 432758757048056880924181 20285566736627666293321)
                      ·
                        rfl

theorem cell23_39506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_39506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_39506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_39506 prefixEnd_39506 := by exact prefixLift 39506
  have htrace : WordTrace (prefixWord ++ tailWord_39506) baseStart_39506 baseEnd_39506 := by
    simpa [prefixWord, tailWord_39506, baseEnd_39506] using wordTrace_append hprefix tailTrace_39506
  have hstable : (prefixWord ++ tailWord_39506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39506).length < 2 ^ (prefixWord ++ tailWord_39506).sum := by decide
  have hdescent : baseEnd_39506 < baseStart_39506 := by decide
  rcases family_descends (prefixWord ++ tailWord_39506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39523 : List Nat := [1, 1, 1, 5, 1, 2, 2, 2, 1, 5, 2]
def baseStart_39523 : Nat := 118140960795 + 39523 * 2 ^ 59
def prefixEnd_39523 : Nat := 4983230072969 + 3 ^ 40 * 39523 * 2
def baseEnd_39523 : Nat := 20294295907754099780743

theorem tailTrace_39523 : CollatzResearch.WordTrace tailWord_39523 prefixEnd_39523 20294295907754099780743 := by
  unfold tailWord_39523
  simp only [CollatzResearch.WordTrace]
  refine ⟨1441522235822395836115223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 961014823881597224076815 1441522235822395836115223)
  ·
    refine ⟨2162283353733593754172835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1441522235822395836115223 2162283353733593754172835)
    ·
      refine ⟨3243425030600390631259253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2162283353733593754172835 3243425030600390631259253)
      ·
        refine ⟨304071096618786621680555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3243425030600390631259253 304071096618786621680555)
        ·
          refine ⟨456106644928179932520833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 304071096618786621680555 456106644928179932520833)
          ·
            refine ⟨342079983696134949390625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 456106644928179932520833 342079983696134949390625)
            ·
              refine ⟨256559987772101212042969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 342079983696134949390625 256559987772101212042969)
              ·
                refine ⟨192419990829075909032227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 256559987772101212042969 192419990829075909032227)
                ·
                  refine ⟨288629986243613863548341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 192419990829075909032227 288629986243613863548341)
                  ·
                    refine ⟨27059061210338799707657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 288629986243613863548341 27059061210338799707657)
                    ·
                      refine ⟨20294295907754099780743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 27059061210338799707657 20294295907754099780743)
                      ·
                        rfl

theorem cell23_39523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 2, 1, 5, 2].length) (baseStart_39523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_39523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_39523 prefixEnd_39523 := by exact prefixLift 39523
  have htrace : WordTrace (prefixWord ++ tailWord_39523) baseStart_39523 baseEnd_39523 := by
    simpa [prefixWord, tailWord_39523, baseEnd_39523] using wordTrace_append hprefix tailTrace_39523
  have hstable : (prefixWord ++ tailWord_39523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39523).length < 2 ^ (prefixWord ++ tailWord_39523).sum := by decide
  have hdescent : baseEnd_39523 < baseStart_39523 := by decide
  rcases family_descends (prefixWord ++ tailWord_39523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39530 : List Nat := [3, 1, 3, 2, 1, 1, 3, 2, 3, 1, 3]
def baseStart_39530 : Nat := 118140960795 + 39530 * 2 ^ 59
def prefixEnd_39530 : Nat := 4983230072969 + 3 ^ 40 * 39530 * 2
def baseEnd_39530 : Nat := 20297890272335572393211

theorem tailTrace_39530 : CollatzResearch.WordTrace tailWord_39530 prefixEnd_39530 20297890272335572393211 := by
  unfold tailWord_39530
  simp only [CollatzResearch.WordTrace]
  refine ⟨360444386699259007905011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 961185031198024021080029 360444386699259007905011)
  ·
    refine ⟨540666580048888511857517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 360444386699259007905011 540666580048888511857517)
    ·
      refine ⟨202749967518333191946569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 540666580048888511857517 202749967518333191946569)
      ·
        refine ⟨152062475638749893959927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 202749967518333191946569 152062475638749893959927)
        ·
          refine ⟨228093713458124840939891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152062475638749893959927 228093713458124840939891)
          ·
            refine ⟨342140570187187261409837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228093713458124840939891 342140570187187261409837)
            ·
              refine ⟨128302713820195223028689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 342140570187187261409837 128302713820195223028689)
              ·
                refine ⟨96227035365146417271517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 128302713820195223028689 96227035365146417271517)
                ·
                  refine ⟨36085138261929906476819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 96227035365146417271517 36085138261929906476819)
                  ·
                    refine ⟨54127707392894859715229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36085138261929906476819 54127707392894859715229)
                    ·
                      refine ⟨20297890272335572393211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 54127707392894859715229 20297890272335572393211)
                      ·
                        rfl

theorem cell23_39530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_39530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_39530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_39530 prefixEnd_39530 := by exact prefixLift 39530
  have htrace : WordTrace (prefixWord ++ tailWord_39530) baseStart_39530 baseEnd_39530 := by
    simpa [prefixWord, tailWord_39530, baseEnd_39530] using wordTrace_append hprefix tailTrace_39530
  have hstable : (prefixWord ++ tailWord_39530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39530).length < 2 ^ (prefixWord ++ tailWord_39530).sum := by decide
  have hdescent : baseEnd_39530 < baseStart_39530 := by decide
  rcases family_descends (prefixWord ++ tailWord_39530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39533 : List Nat := [1, 5, 1, 1, 3, 1, 2, 1, 3, 5]
def baseStart_39533 : Nat := 118140960795 + 39533 * 2 ^ 59
def prefixEnd_39533 : Nat := 4983230072969 + 3 ^ 40 * 39533 * 2
def baseEnd_39533 : Nat := 6766476904766353551899

theorem tailTrace_39533 : CollatzResearch.WordTrace tailWord_39533 prefixEnd_39533 6766476904766353551899 := by
  unfold tailWord_39533
  simp only [CollatzResearch.WordTrace]
  refine ⟨1441886965786167543979253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 961257977190778362652835 1441886965786167543979253)
  ·
    refine ⟨135176903042453207248055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1441886965786167543979253 135176903042453207248055)
    ·
      refine ⟨202765354563679810872083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135176903042453207248055 202765354563679810872083)
      ·
        refine ⟨304148031845519716308125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202765354563679810872083 304148031845519716308125)
        ·
          refine ⟨114055511942069893615547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 304148031845519716308125 114055511942069893615547)
          ·
            refine ⟨171083267913104840423321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114055511942069893615547 171083267913104840423321)
            ·
              refine ⟨128312450934828630317491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 171083267913104840423321 128312450934828630317491)
              ·
                refine ⟨192468676402242945476237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128312450934828630317491 192468676402242945476237)
                ·
                  refine ⟨72175753650841104553589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 192468676402242945476237 72175753650841104553589)
                  ·
                    refine ⟨6766476904766353551899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 72175753650841104553589 6766476904766353551899)
                    ·
                      rfl

theorem cell23_39533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 1, 3, 5].length) (baseStart_39533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_39533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_39533 prefixEnd_39533 := by exact prefixLift 39533
  have htrace : WordTrace (prefixWord ++ tailWord_39533) baseStart_39533 baseEnd_39533 := by
    simpa [prefixWord, tailWord_39533, baseEnd_39533] using wordTrace_append hprefix tailTrace_39533
  have hstable : (prefixWord ++ tailWord_39533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39533).length < 2 ^ (prefixWord ++ tailWord_39533).sum := by decide
  have hdescent : baseEnd_39533 < baseStart_39533 := by decide
  rcases family_descends (prefixWord ++ tailWord_39533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39563 : List Nat := [1, 1, 1, 1, 4, 1, 2, 6, 2, 4]
def baseStart_39563 : Nat := 118140960795 + 39563 * 2 ^ 59
def prefixEnd_39563 : Nat := 4983230072969 + 3 ^ 40 * 39563 * 2
def baseEnd_39563 : Nat := 6771611711311314426853

theorem tailTrace_39563 : CollatzResearch.WordTrace tailWord_39563 prefixEnd_39563 6771611711311314426853 := by
  unfold tailWord_39563
  simp only [CollatzResearch.WordTrace]
  refine ⟨1442981155677482667571343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 961987437118321778380895 1442981155677482667571343)
  ·
    refine ⟨2164471733516224001357015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1442981155677482667571343 2164471733516224001357015)
    ·
      refine ⟨3246707600274336002035523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2164471733516224001357015 3246707600274336002035523)
      ·
        refine ⟨4870061400411504003053285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3246707600274336002035523 4870061400411504003053285)
        ·
          refine ⟨913136512577157000572491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4870061400411504003053285 913136512577157000572491)
          ·
            refine ⟨1369704768865735500858737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 913136512577157000572491 1369704768865735500858737)
            ·
              refine ⟨1027278576649301625644053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1369704768865735500858737 1027278576649301625644053)
              ·
                refine ⟨48153683280436013702065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1027278576649301625644053 48153683280436013702065)
                ·
                  refine ⟨36115262460327010276549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48153683280436013702065 36115262460327010276549)
                  ·
                    refine ⟨6771611711311314426853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36115262460327010276549 6771611711311314426853)
                    ·
                      rfl

theorem cell23_39563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 6, 2, 4].length) (baseStart_39563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_39563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_39563 prefixEnd_39563 := by exact prefixLift 39563
  have htrace : WordTrace (prefixWord ++ tailWord_39563) baseStart_39563 baseEnd_39563 := by
    simpa [prefixWord, tailWord_39563, baseEnd_39563] using wordTrace_append hprefix tailTrace_39563
  have hstable : (prefixWord ++ tailWord_39563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39563).length < 2 ^ (prefixWord ++ tailWord_39563).sum := by decide
  have hdescent : baseEnd_39563 < baseStart_39563 := by decide
  rcases family_descends (prefixWord ++ tailWord_39563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39576 : List Nat := [2, 1, 2, 4, 1, 1, 2, 10]
def baseStart_39576 : Nat := 118140960795 + 39576 * 2 ^ 59
def prefixEnd_39576 : Nat := 4983230072969 + 3 ^ 40 * 39576 * 2
def baseEnd_39576 : Nat := 752648532683051571037

theorem tailTrace_39576 : CollatzResearch.WordTrace tailWord_39576 prefixEnd_39576 752648532683051571037 := by
  unfold tailWord_39576
  simp only [CollatzResearch.WordTrace]
  refine ⟨721727652315192943897291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 962303536420257258529721 721727652315192943897291)
  ·
    refine ⟨1082591478472789415845937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 721727652315192943897291 1082591478472789415845937)
    ·
      refine ⟨811943608854592061884453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1082591478472789415845937 811943608854592061884453)
      ·
        refine ⟨152239426660236011603335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 811943608854592061884453 152239426660236011603335)
        ·
          refine ⟨228359139990354017405003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152239426660236011603335 228359139990354017405003)
          ·
            refine ⟨342538709985531026107505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228359139990354017405003 342538709985531026107505)
            ·
              refine ⟨256904032489148269580629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 342538709985531026107505 256904032489148269580629)
              ·
                refine ⟨752648532683051571037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 256904032489148269580629 752648532683051571037)
                ·
                  rfl

theorem cell23_39576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 10].length) (baseStart_39576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_39576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_39576 prefixEnd_39576 := by exact prefixLift 39576
  have htrace : WordTrace (prefixWord ++ tailWord_39576) baseStart_39576 baseEnd_39576 := by
    simpa [prefixWord, tailWord_39576, baseEnd_39576] using wordTrace_append hprefix tailTrace_39576
  have hstable : (prefixWord ++ tailWord_39576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39576).length < 2 ^ (prefixWord ++ tailWord_39576).sum := by decide
  have hdescent : baseEnd_39576 < baseStart_39576 := by decide
  rcases family_descends (prefixWord ++ tailWord_39576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39580 : List Nat := [2, 2, 3, 2, 2, 3, 1, 1, 1, 6]
def baseStart_39580 : Nat := 118140960795 + 39580 * 2 ^ 59
def prefixEnd_39580 : Nat := 4983230072969 + 3 ^ 40 * 39580 * 2
def baseEnd_39580 : Nat := 6774521435020125589327

theorem tailTrace_39580 : CollatzResearch.WordTrace tailWord_39580 prefixEnd_39580 6774521435020125589327 := by
  unfold tailWord_39580
  simp only [CollatzResearch.WordTrace]
  refine ⟨721800598307947285470097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 962400797743929713960129 721800598307947285470097)
  ·
    refine ⟨541350448730960464102573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 721800598307947285470097 541350448730960464102573)
    ·
      refine ⟨203006418274110174038465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 541350448730960464102573 203006418274110174038465)
      ·
        refine ⟨152254813705582630528849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203006418274110174038465 152254813705582630528849)
        ·
          refine ⟨114191110279186972896637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152254813705582630528849 114191110279186972896637)
          ·
            refine ⟨42821666354695114836239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114191110279186972896637 42821666354695114836239)
            ·
              refine ⟨64232499532042672254359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42821666354695114836239 64232499532042672254359)
              ·
                refine ⟨96348749298064008381539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64232499532042672254359 96348749298064008381539)
                ·
                  refine ⟨144523123947096012572309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 96348749298064008381539 144523123947096012572309)
                  ·
                    refine ⟨6774521435020125589327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 144523123947096012572309 6774521435020125589327)
                    ·
                      rfl

theorem cell23_39580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 1, 1, 6].length) (baseStart_39580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_39580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_39580 prefixEnd_39580 := by exact prefixLift 39580
  have htrace : WordTrace (prefixWord ++ tailWord_39580) baseStart_39580 baseEnd_39580 := by
    simpa [prefixWord, tailWord_39580, baseEnd_39580] using wordTrace_append hprefix tailTrace_39580
  have hstable : (prefixWord ++ tailWord_39580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39580).length < 2 ^ (prefixWord ++ tailWord_39580).sum := by decide
  have hdescent : baseEnd_39580 < baseStart_39580 := by decide
  rcases family_descends (prefixWord ++ tailWord_39580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39647 : List Nat := [1, 1, 2, 3, 2, 3, 3, 2, 1, 3, 2]
def baseStart_39647 : Nat := 118140960795 + 39647 * 2 ^ 59
def prefixEnd_39647 : Nat := 4983230072969 + 3 ^ 40 * 39647 * 2
def baseEnd_39647 : Nat := 20357967508911614630173

theorem tailTrace_39647 : CollatzResearch.WordTrace tailWord_39647 prefixEnd_39647 20357967508911614630173 := by
  unfold tailWord_39647
  simp only [CollatzResearch.WordTrace]
  refine ⟨1446044887373165013629195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 964029924915443342419463 1446044887373165013629195)
  ·
    refine ⟨2169067331059747520443793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1446044887373165013629195 2169067331059747520443793)
    ·
      refine ⟨1626800498294810640332845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2169067331059747520443793 1626800498294810640332845)
      ·
        refine ⟨610050186860553990124817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1626800498294810640332845 610050186860553990124817)
        ·
          refine ⟨457537640145415492593613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 610050186860553990124817 457537640145415492593613)
          ·
            refine ⟨171576615054530809722605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 457537640145415492593613 171576615054530809722605)
            ·
              refine ⟨64341230645449053645977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 171576615054530809722605 64341230645449053645977)
              ·
                refine ⟨48255922984086790234483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64341230645449053645977 48255922984086790234483)
                ·
                  refine ⟨72383884476130185351725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48255922984086790234483 72383884476130185351725)
                  ·
                    refine ⟨27143956678548819506897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 72383884476130185351725 27143956678548819506897)
                    ·
                      refine ⟨20357967508911614630173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 27143956678548819506897 20357967508911614630173)
                      ·
                        rfl

theorem cell23_39647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 2, 1, 3, 2].length) (baseStart_39647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_39647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_39647 prefixEnd_39647 := by exact prefixLift 39647
  have htrace : WordTrace (prefixWord ++ tailWord_39647) baseStart_39647 baseEnd_39647 := by
    simpa [prefixWord, tailWord_39647, baseEnd_39647] using wordTrace_append hprefix tailTrace_39647
  have hstable : (prefixWord ++ tailWord_39647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39647).length < 2 ^ (prefixWord ++ tailWord_39647).sum := by decide
  have hdescent : baseEnd_39647 < baseStart_39647 := by decide
  rcases family_descends (prefixWord ++ tailWord_39647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39663 : List Nat := [1, 1, 2, 1, 5, 2, 2, 1, 2, 1, 5]
def baseStart_39663 : Nat := 118140960795 + 39663 * 2 ^ 59
def prefixEnd_39663 : Nat := 4983230072969 + 3 ^ 40 * 39663 * 2
def baseEnd_39663 : Nat := 20366183199383552030099

theorem tailTrace_39663 : CollatzResearch.WordTrace tailWord_39663 prefixEnd_39663 20366183199383552030099 := by
  unfold tailWord_39663
  simp only [CollatzResearch.WordTrace]
  refine ⟨1446628455315199746211643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 964418970210133164141095 1446628455315199746211643)
  ·
    refine ⟨2169942682972799619317465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1446628455315199746211643 2169942682972799619317465)
    ·
      refine ⟨1627457012229599714488099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2169942682972799619317465 1627457012229599714488099)
      ·
        refine ⟨2441185518344399571732149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1627457012229599714488099 2441185518344399571732149)
        ·
          refine ⟨228861142344787459849889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2441185518344399571732149 228861142344787459849889)
          ·
            refine ⟨171645856758590594887417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 228861142344787459849889 171645856758590594887417)
            ·
              refine ⟨128734392568942946165563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 171645856758590594887417 128734392568942946165563)
              ·
                refine ⟨193101588853414419248345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128734392568942946165563 193101588853414419248345)
                ·
                  refine ⟨144826191640060814436259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 193101588853414419248345 144826191640060814436259)
                  ·
                    refine ⟨217239287460091221654389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 144826191640060814436259 217239287460091221654389)
                    ·
                      refine ⟨20366183199383552030099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 217239287460091221654389 20366183199383552030099)
                      ·
                        rfl

theorem cell23_39663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 1, 2, 1, 5].length) (baseStart_39663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_39663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_39663 prefixEnd_39663 := by exact prefixLift 39663
  have htrace : WordTrace (prefixWord ++ tailWord_39663) baseStart_39663 baseEnd_39663 := by
    simpa [prefixWord, tailWord_39663, baseEnd_39663] using wordTrace_append hprefix tailTrace_39663
  have hstable : (prefixWord ++ tailWord_39663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39663).length < 2 ^ (prefixWord ++ tailWord_39663).sum := by decide
  have hdescent : baseEnd_39663 < baseStart_39663 := by decide
  rcases family_descends (prefixWord ++ tailWord_39663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39713 : List Nat := [1, 2, 3, 2, 1, 2, 3, 1, 1, 7]
def baseStart_39713 : Nat := 118140960795 + 39713 * 2 ^ 59
def prefixEnd_39713 : Nat := 4983230072969 + 3 ^ 40 * 39713 * 2
def baseEnd_39713 : Nat := 6797285744036118801623

theorem tailTrace_39713 : CollatzResearch.WordTrace tailWord_39713 prefixEnd_39713 6797285744036118801623 := by
  unfold tailWord_39713
  simp only [CollatzResearch.WordTrace]
  refine ⟨1448452105134058285531793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 965634736756038857021195 1448452105134058285531793)
  ·
    refine ⟨1086339078850543714148845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1448452105134058285531793 1086339078850543714148845)
    ·
      refine ⟨407377154568953892805817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1086339078850543714148845 407377154568953892805817)
      ·
        refine ⟨305532865926715419604363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 407377154568953892805817 305532865926715419604363)
        ·
          refine ⟨458299298890073129406545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 305532865926715419604363 458299298890073129406545)
          ·
            refine ⟨343724474167554847054909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 458299298890073129406545 343724474167554847054909)
            ·
              refine ⟨128896677812833067645591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 343724474167554847054909 128896677812833067645591)
              ·
                refine ⟨193345016719249601468387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128896677812833067645591 193345016719249601468387)
                ·
                  refine ⟨290017525078874402202581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 193345016719249601468387 290017525078874402202581)
                  ·
                    refine ⟨6797285744036118801623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 290017525078874402202581 6797285744036118801623)
                    ·
                      rfl

theorem cell23_39713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 1, 1, 7].length) (baseStart_39713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_39713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_39713 prefixEnd_39713 := by exact prefixLift 39713
  have htrace : WordTrace (prefixWord ++ tailWord_39713) baseStart_39713 baseEnd_39713 := by
    simpa [prefixWord, tailWord_39713, baseEnd_39713] using wordTrace_append hprefix tailTrace_39713
  have hstable : (prefixWord ++ tailWord_39713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39713).length < 2 ^ (prefixWord ++ tailWord_39713).sum := by decide
  have hdescent : baseEnd_39713 < baseStart_39713 := by decide
  rcases family_descends (prefixWord ++ tailWord_39713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39760 : List Nat := [2, 1, 1, 1, 1, 4, 4, 2, 3, 4]
def baseStart_39760 : Nat := 118140960795 + 39760 * 2 ^ 59
def prefixEnd_39760 : Nat := 4983230072969 + 3 ^ 40 * 39760 * 2
def baseEnd_39760 : Nat := 6805330274289890839051

theorem tailTrace_39760 : CollatzResearch.WordTrace tailWord_39760 prefixEnd_39760 6805330274289890839051 := by
  unfold tailWord_39760
  simp only [CollatzResearch.WordTrace]
  refine ⟨725083167981892656246367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 966777557309190208328489 725083167981892656246367)
  ·
    refine ⟨1087624751972838984369551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 725083167981892656246367 1087624751972838984369551)
    ·
      refine ⟨1631437127959258476554327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1087624751972838984369551 1631437127959258476554327)
      ·
        refine ⟨2447155691938887714831491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1631437127959258476554327 2447155691938887714831491)
        ·
          refine ⟨3670733537908331572247237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2447155691938887714831491 3670733537908331572247237)
          ·
            refine ⟨688262538357812169796357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3670733537908331572247237 688262538357812169796357)
            ·
              refine ⟨129049225942089781836817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 688262538357812169796357 129049225942089781836817)
              ·
                refine ⟨96786919456567336377613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 129049225942089781836817 96786919456567336377613)
                ·
                  refine ⟨36295094796212751141605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 96786919456567336377613 36295094796212751141605)
                  ·
                    refine ⟨6805330274289890839051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36295094796212751141605 6805330274289890839051)
                    ·
                      rfl

theorem cell23_39760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 2, 3, 4].length) (baseStart_39760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_39760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_39760 prefixEnd_39760 := by exact prefixLift 39760
  have htrace : WordTrace (prefixWord ++ tailWord_39760) baseStart_39760 baseEnd_39760 := by
    simpa [prefixWord, tailWord_39760, baseEnd_39760] using wordTrace_append hprefix tailTrace_39760
  have hstable : (prefixWord ++ tailWord_39760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39760).length < 2 ^ (prefixWord ++ tailWord_39760).sum := by decide
  have hdescent : baseEnd_39760 < baseStart_39760 := by decide
  rcases family_descends (prefixWord ++ tailWord_39760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39770 : List Nat := [3, 1, 1, 2, 1, 4, 2, 1, 1, 4, 3]
def baseStart_39770 : Nat := 118140960795 + 39770 * 2 ^ 59
def prefixEnd_39770 : Nat := 4983230072969 + 3 ^ 40 * 39770 * 2
def baseEnd_39770 : Nat := 20421125629414633392107

theorem tailTrace_39770 : CollatzResearch.WordTrace tailWord_39770 prefixEnd_39770 20421125629414633392107 := by
  unfold tailWord_39770
  simp only [CollatzResearch.WordTrace]
  refine ⟨362632766481889255089191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 967020710618371346904509 362632766481889255089191)
  ·
    refine ⟨543949149722833882633787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 362632766481889255089191 543949149722833882633787)
    ·
      refine ⟨815923724584250823950681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 543949149722833882633787 815923724584250823950681)
      ·
        refine ⟨611942793438188117963011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 815923724584250823950681 611942793438188117963011)
        ·
          refine ⟨917914190157282176944517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 611942793438188117963011 917914190157282176944517)
          ·
            refine ⟨172108910654490408177097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 917914190157282176944517 172108910654490408177097)
            ·
              refine ⟨129081682990867806132823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 172108910654490408177097 129081682990867806132823)
              ·
                refine ⟨193622524486301709199235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 129081682990867806132823 193622524486301709199235)
                ·
                  refine ⟨290433786729452563798853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 193622524486301709199235 290433786729452563798853)
                  ·
                    refine ⟨54456335011772355712285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 290433786729452563798853 54456335011772355712285)
                    ·
                      refine ⟨20421125629414633392107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 54456335011772355712285 20421125629414633392107)
                      ·
                        rfl

theorem cell23_39770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 1, 1, 4, 3].length) (baseStart_39770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_39770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_39770 prefixEnd_39770 := by exact prefixLift 39770
  have htrace : WordTrace (prefixWord ++ tailWord_39770) baseStart_39770 baseEnd_39770 := by
    simpa [prefixWord, tailWord_39770, baseEnd_39770] using wordTrace_append hprefix tailTrace_39770
  have hstable : (prefixWord ++ tailWord_39770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39770).length < 2 ^ (prefixWord ++ tailWord_39770).sum := by decide
  have hdescent : baseEnd_39770 < baseStart_39770 := by decide
  rcases family_descends (prefixWord ++ tailWord_39770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39777 : List Nat := [1, 2, 3, 1, 1, 1, 2, 7, 1, 4]
def baseStart_39777 : Nat := 118140960795 + 39777 * 2 ^ 59
def prefixEnd_39777 : Nat := 4983230072969 + 3 ^ 40 * 39777 * 2
def baseEnd_39777 : Nat := 6808239997998702001525

theorem tailTrace_39777 : CollatzResearch.WordTrace tailWord_39777 prefixEnd_39777 6808239997998702001525 := by
  unfold tailWord_39777
  simp only [CollatzResearch.WordTrace]
  refine ⟨1450786376902197215861585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 967190917934798143907723 1450786376902197215861585)
  ·
    refine ⟨1088089782676647911896189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1450786376902197215861585 1088089782676647911896189)
    ·
      refine ⟨408033668503742966961071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1088089782676647911896189 408033668503742966961071)
      ·
        refine ⟨612050502755614450441607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 408033668503742966961071 612050502755614450441607)
        ·
          refine ⟨918075754133421675662411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 612050502755614450441607 918075754133421675662411)
          ·
            refine ⟨1377113631200132513493617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 918075754133421675662411 1377113631200132513493617)
            ·
              refine ⟨1032835223400099385120213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1377113631200132513493617 1032835223400099385120213)
              ·
                refine ⟨24207075548439829338755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1032835223400099385120213 24207075548439829338755)
                ·
                  refine ⟨36310613322659744008133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24207075548439829338755 36310613322659744008133)
                  ·
                    refine ⟨6808239997998702001525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36310613322659744008133 6808239997998702001525)
                    ·
                      rfl

theorem cell23_39777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 7, 1, 4].length) (baseStart_39777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_39777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_39777 prefixEnd_39777 := by exact prefixLift 39777
  have htrace : WordTrace (prefixWord ++ tailWord_39777) baseStart_39777 baseEnd_39777 := by
    simpa [prefixWord, tailWord_39777, baseEnd_39777] using wordTrace_append hprefix tailTrace_39777
  have hstable : (prefixWord ++ tailWord_39777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39777).length < 2 ^ (prefixWord ++ tailWord_39777).sum := by decide
  have hdescent : baseEnd_39777 < baseStart_39777 := by decide
  rcases family_descends (prefixWord ++ tailWord_39777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39901 : List Nat := [1, 4, 3, 1, 2, 3, 1, 2, 2, 4]
def baseStart_39901 : Nat := 118140960795 + 39901 * 2 ^ 59
def prefixEnd_39901 : Nat := 4983230072969 + 3 ^ 40 * 39901 * 2
def baseEnd_39901 : Nat := 6829463865051206951335

theorem tailTrace_39901 : CollatzResearch.WordTrace tailWord_39901 prefixEnd_39901 6829463865051206951335 := by
  unfold tailWord_39901
  simp only [CollatzResearch.WordTrace]
  refine ⟨1455309028452966393375557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 970206018968644262250371 1455309028452966393375557)
  ·
    refine ⟨272870442834931198757917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1455309028452966393375557 272870442834931198757917)
    ·
      refine ⟨102326416063099199534219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 272870442834931198757917 102326416063099199534219)
      ·
        refine ⟨153489624094648799301329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102326416063099199534219 153489624094648799301329)
        ·
          refine ⟨115117218070986599475997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153489624094648799301329 115117218070986599475997)
          ·
            refine ⟨43168956776619974803499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115117218070986599475997 43168956776619974803499)
            ·
              refine ⟨64753435164929962205249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43168956776619974803499 64753435164929962205249)
              ·
                refine ⟨48565076373697471653937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64753435164929962205249 48565076373697471653937)
                ·
                  refine ⟨36423807280273103740453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48565076373697471653937 36423807280273103740453)
                  ·
                    refine ⟨6829463865051206951335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36423807280273103740453 6829463865051206951335)
                    ·
                      rfl

theorem cell23_39901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_39901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_39901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_39901 prefixEnd_39901 := by exact prefixLift 39901
  have htrace : WordTrace (prefixWord ++ tailWord_39901) baseStart_39901 baseEnd_39901 := by
    simpa [prefixWord, tailWord_39901, baseEnd_39901] using wordTrace_append hprefix tailTrace_39901
  have hstable : (prefixWord ++ tailWord_39901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39901).length < 2 ^ (prefixWord ++ tailWord_39901).sum := by decide
  have hdescent : baseEnd_39901 < baseStart_39901 := by decide
  rcases family_descends (prefixWord ++ tailWord_39901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39930 : List Nat := [3, 1, 1, 1, 1, 2, 1, 4, 2, 3, 4]
def baseStart_39930 : Nat := 118140960795 + 39930 * 2 ^ 59
def prefixEnd_39930 : Nat := 4983230072969 + 3 ^ 40 * 39930 * 2
def baseEnd_39930 : Nat := 20503282534134007391371

theorem tailTrace_39930 : CollatzResearch.WordTrace tailWord_39930 prefixEnd_39930 20503282534134007391371 := by
  unfold tailWord_39930
  simp only [CollatzResearch.WordTrace]
  refine ⟨364091686336976086545311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 970911163565269564120829 364091686336976086545311)
  ·
    refine ⟨546137529505464129817967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 364091686336976086545311 546137529505464129817967)
    ·
      refine ⟨819206294258196194726951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 546137529505464129817967 819206294258196194726951)
      ·
        refine ⟨1228809441387294292090427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 819206294258196194726951 1228809441387294292090427)
        ·
          refine ⟨1843214162080941438135641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1228809441387294292090427 1843214162080941438135641)
          ·
            refine ⟨1382410621560706078601731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1843214162080941438135641 1382410621560706078601731)
            ·
              refine ⟨2073615932341059117902597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1382410621560706078601731 2073615932341059117902597)
              ·
                refine ⟨388802987313948584606737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2073615932341059117902597 388802987313948584606737)
                ·
                  refine ⟨291602240485461438455053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 388802987313948584606737 291602240485461438455053)
                  ·
                    refine ⟨109350840182048039420645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 291602240485461438455053 109350840182048039420645)
                    ·
                      refine ⟨20503282534134007391371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 109350840182048039420645 20503282534134007391371)
                      ·
                        rfl

theorem cell23_39930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 2, 3, 4].length) (baseStart_39930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_39930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_39930 prefixEnd_39930 := by exact prefixLift 39930
  have htrace : WordTrace (prefixWord ++ tailWord_39930) baseStart_39930 baseEnd_39930 := by
    simpa [prefixWord, tailWord_39930, baseEnd_39930] using wordTrace_append hprefix tailTrace_39930
  have hstable : (prefixWord ++ tailWord_39930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39930).length < 2 ^ (prefixWord ++ tailWord_39930).sum := by decide
  have hdescent : baseEnd_39930 < baseStart_39930 := by decide
  rcases family_descends (prefixWord ++ tailWord_39930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_39975 : List Nat := [1, 1, 7, 1, 1, 3, 2, 1, 2, 1, 3]
def baseStart_39975 : Nat := 118140960795 + 39975 * 2 ^ 59
def prefixEnd_39975 : Nat := 4983230072969 + 3 ^ 40 * 39975 * 2
def baseEnd_39975 : Nat := 20526389163586331328665

theorem tailTrace_39975 : CollatzResearch.WordTrace tailWord_39975 prefixEnd_39975 20526389163586331328665 := by
  unfold tailWord_39975
  simp only [CollatzResearch.WordTrace]
  refine ⟨1458008030184877031569379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 972005353456584687712919 1458008030184877031569379)
  ·
    refine ⟨2187012045277315547354069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1458008030184877031569379 2187012045277315547354069)
    ·
      refine ⟨51258094811187083141111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 2187012045277315547354069 51258094811187083141111)
      ·
        refine ⟨76887142216780624711667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51258094811187083141111 76887142216780624711667)
        ·
          refine ⟨115330713325170937067501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76887142216780624711667 115330713325170937067501)
          ·
            refine ⟨43249017496939101400313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115330713325170937067501 43249017496939101400313)
            ·
              refine ⟨32436763122704326050235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43249017496939101400313 32436763122704326050235)
              ·
                refine ⟨48655144684056489075353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32436763122704326050235 48655144684056489075353)
                ·
                  refine ⟨36491358513042366806515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48655144684056489075353 36491358513042366806515)
                  ·
                    refine ⟨54737037769563550209773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36491358513042366806515 54737037769563550209773)
                    ·
                      refine ⟨20526389163586331328665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 54737037769563550209773 20526389163586331328665)
                      ·
                        rfl

theorem cell23_39975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_39975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_39975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_39975 prefixEnd_39975 := by exact prefixLift 39975
  have htrace : WordTrace (prefixWord ++ tailWord_39975) baseStart_39975 baseEnd_39975 := by
    simpa [prefixWord, tailWord_39975, baseEnd_39975] using wordTrace_append hprefix tailTrace_39975
  have hstable : (prefixWord ++ tailWord_39975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_39975).length < 2 ^ (prefixWord ++ tailWord_39975).sum := by decide
  have hdescent : baseEnd_39975 < baseStart_39975 := by decide
  rcases family_descends (prefixWord ++ tailWord_39975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40017 : List Nat := [1, 2, 2, 1, 3, 1, 4, 2, 2, 5]
def baseStart_40017 : Nat := 118140960795 + 40017 * 2 ^ 59
def prefixEnd_40017 : Nat := 4983230072969 + 3 ^ 40 * 40017 * 2
def baseEnd_40017 : Nat := 6849318450358389001157

theorem tailTrace_40017 : CollatzResearch.WordTrace tailWord_40017 prefixEnd_40017 6849318450358389001157 := by
  unfold tailWord_40017
  simp only [CollatzResearch.WordTrace]
  refine ⟨1459539896032718204598305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 973026597355145469732203 1459539896032718204598305)
  ·
    refine ⟨1094654922024538653448729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1459539896032718204598305 1094654922024538653448729)
    ·
      refine ⟨820991191518403990086547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1094654922024538653448729 820991191518403990086547)
      ·
        refine ⟨1231486787277605985129821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 820991191518403990086547 1231486787277605985129821)
        ·
          refine ⟨461807545229102244423683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1231486787277605985129821 461807545229102244423683)
          ·
            refine ⟨692711317843653366635525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 461807545229102244423683 692711317843653366635525)
            ·
              refine ⟨129883372095685006244161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 692711317843653366635525 129883372095685006244161)
              ·
                refine ⟨97412529071763754683121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 129883372095685006244161 97412529071763754683121)
                ·
                  refine ⟨73059396803822816012341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 97412529071763754683121 73059396803822816012341)
                  ·
                    refine ⟨6849318450358389001157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 73059396803822816012341 6849318450358389001157)
                    ·
                      rfl

theorem cell23_40017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 2, 2, 5].length) (baseStart_40017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_40017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_40017 prefixEnd_40017 := by exact prefixLift 40017
  have htrace : WordTrace (prefixWord ++ tailWord_40017) baseStart_40017 baseEnd_40017 := by
    simpa [prefixWord, tailWord_40017, baseEnd_40017] using wordTrace_append hprefix tailTrace_40017
  have hstable : (prefixWord ++ tailWord_40017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40017).length < 2 ^ (prefixWord ++ tailWord_40017).sum := by decide
  have hdescent : baseEnd_40017 < baseStart_40017 := by decide
  rcases family_descends (prefixWord ++ tailWord_40017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40037 : List Nat := [1, 3, 1, 3, 2, 1, 2, 2, 1, 3, 4]
def baseStart_40037 : Nat := 118140960795 + 40037 * 2 ^ 59
def prefixEnd_40037 : Nat := 4983230072969 + 3 ^ 40 * 40037 * 2
def baseEnd_40037 : Nat := 20558224964165088753379

theorem tailTrace_40037 : CollatzResearch.WordTrace tailWord_40037 prefixEnd_40037 20558224964165088753379 := by
  unfold tailWord_40037
  simp only [CollatzResearch.WordTrace]
  refine ⟨1460269355960261620326365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 973512903973507746884243 1460269355960261620326365)
  ·
    refine ⟨547601008485098107622387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1460269355960261620326365 547601008485098107622387)
    ·
      refine ⟨821401512727647161433581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 547601008485098107622387 821401512727647161433581)
      ·
        refine ⟨308025567272867685537593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 821401512727647161433581 308025567272867685537593)
        ·
          refine ⟨231019175454650764153195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 308025567272867685537593 231019175454650764153195)
          ·
            refine ⟨346528763181976146229793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231019175454650764153195 346528763181976146229793)
            ·
              refine ⟨259896572386482109672345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 346528763181976146229793 259896572386482109672345)
              ·
                refine ⟨194922429289861582254259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 259896572386482109672345 194922429289861582254259)
                ·
                  refine ⟨292383643934792373381389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 194922429289861582254259 292383643934792373381389)
                  ·
                    refine ⟨109643866475547140018021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 292383643934792373381389 109643866475547140018021)
                    ·
                      refine ⟨20558224964165088753379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 109643866475547140018021 20558224964165088753379)
                      ·
                        rfl

theorem cell23_40037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_40037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_40037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_40037 prefixEnd_40037 := by exact prefixLift 40037
  have htrace : WordTrace (prefixWord ++ tailWord_40037) baseStart_40037 baseEnd_40037 := by
    simpa [prefixWord, tailWord_40037, baseEnd_40037] using wordTrace_append hprefix tailTrace_40037
  have hstable : (prefixWord ++ tailWord_40037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40037).length < 2 ^ (prefixWord ++ tailWord_40037).sum := by decide
  have hdescent : baseEnd_40037 < baseStart_40037 := by decide
  rcases family_descends (prefixWord ++ tailWord_40037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40054 : List Nat := [5, 1, 1, 2, 1, 1, 3, 1, 1, 3, 4]
def baseStart_40054 : Nat := 118140960795 + 40054 * 2 ^ 59
def prefixEnd_40054 : Nat := 4983230072969 + 3 ^ 40 * 40054 * 2
def baseEnd_40054 : Nat := 20566954135291522240801

theorem tailTrace_40054 : CollatzResearch.WordTrace tailWord_40054 prefixEnd_40054 20566954135291522240801 := by
  unfold tailWord_40054
  simp only [CollatzResearch.WordTrace]
  refine ⟨91305587306167095230951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 973926264599115682463477 91305587306167095230951)
  ·
    refine ⟨136958380959250642846427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91305587306167095230951 136958380959250642846427)
    ·
      refine ⟨205437571438875964269641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136958380959250642846427 205437571438875964269641)
      ·
        refine ⟨154078178579156973202231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205437571438875964269641 154078178579156973202231)
        ·
          refine ⟨231117267868735459803347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154078178579156973202231 231117267868735459803347)
          ·
            refine ⟨346675901803103189705021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231117267868735459803347 346675901803103189705021)
            ·
              refine ⟨130003463176163696139383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 346675901803103189705021 130003463176163696139383)
              ·
                refine ⟨195005194764245544209075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130003463176163696139383 195005194764245544209075)
                ·
                  refine ⟨292507792146368316313613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 195005194764245544209075 292507792146368316313613)
                  ·
                    refine ⟨109690422054888118617605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 292507792146368316313613 109690422054888118617605)
                    ·
                      refine ⟨20566954135291522240801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 109690422054888118617605 20566954135291522240801)
                      ·
                        rfl

theorem cell23_40054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_40054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_40054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_40054 prefixEnd_40054 := by exact prefixLift 40054
  have htrace : WordTrace (prefixWord ++ tailWord_40054) baseStart_40054 baseEnd_40054 := by
    simpa [prefixWord, tailWord_40054, baseEnd_40054] using wordTrace_append hprefix tailTrace_40054
  have hstable : (prefixWord ++ tailWord_40054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40054).length < 2 ^ (prefixWord ++ tailWord_40054).sum := by decide
  have hdescent : baseEnd_40054 < baseStart_40054 := by decide
  rcases family_descends (prefixWord ++ tailWord_40054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40074 : List Nat := [3, 1, 2, 3, 1, 1, 2, 1, 4, 2, 3]
def baseStart_40074 : Nat := 118140960795 + 40074 * 2 ^ 59
def prefixEnd_40074 : Nat := 4983230072969 + 3 ^ 40 * 40074 * 2
def baseEnd_40074 : Nat := 20577223748381443990709

theorem tailTrace_40074 : CollatzResearch.WordTrace tailWord_40074 prefixEnd_40074 20577223748381443990709 := by
  unfold tailWord_40074
  simp only [CollatzResearch.WordTrace]
  refine ⟨365404714206554234855819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 974412571217477959615517 365404714206554234855819)
  ·
    refine ⟨548107071309831352283729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 365404714206554234855819 548107071309831352283729)
    ·
      refine ⟨411080303482373514212797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 548107071309831352283729 411080303482373514212797)
      ·
        refine ⟨154155113805890067829799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 411080303482373514212797 154155113805890067829799)
        ·
          refine ⟨231232670708835101744699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154155113805890067829799 231232670708835101744699)
          ·
            refine ⟨346849006063252652617049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231232670708835101744699 346849006063252652617049)
            ·
              refine ⟨260136754547439489462787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 346849006063252652617049 260136754547439489462787)
              ·
                refine ⟨390205131821159234194181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 260136754547439489462787 390205131821159234194181)
                ·
                  refine ⟨73163462216467356411409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 390205131821159234194181 73163462216467356411409)
                  ·
                    refine ⟨54872596662350517308557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 73163462216467356411409 54872596662350517308557)
                    ·
                      refine ⟨20577223748381443990709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 54872596662350517308557 20577223748381443990709)
                      ·
                        rfl

theorem cell23_40074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_40074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_40074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_40074 prefixEnd_40074 := by exact prefixLift 40074
  have htrace : WordTrace (prefixWord ++ tailWord_40074) baseStart_40074 baseEnd_40074 := by
    simpa [prefixWord, tailWord_40074, baseEnd_40074] using wordTrace_append hprefix tailTrace_40074
  have hstable : (prefixWord ++ tailWord_40074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40074).length < 2 ^ (prefixWord ++ tailWord_40074).sum := by decide
  have hdescent : baseEnd_40074 < baseStart_40074 := by decide
  rcases family_descends (prefixWord ++ tailWord_40074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40097 : List Nat := [1, 2, 3, 3, 1, 1, 1, 2, 1, 2, 6]
def baseStart_40097 : Nat := 118140960795 + 40097 * 2 ^ 59
def prefixEnd_40097 : Nat := 4983230072969 + 3 ^ 40 * 40097 * 2
def baseEnd_40097 : Nat := 20589033803434854003103

theorem tailTrace_40097 : CollatzResearch.WordTrace tailWord_40097 prefixEnd_40097 20589033803434854003103 := by
  unfold tailWord_40097
  simp only [CollatzResearch.WordTrace]
  refine ⟨1462457735742891867510545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 974971823828594578340363 1462457735742891867510545)
  ·
    refine ⟨1096843301807168900632909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1462457735742891867510545 1096843301807168900632909)
    ·
      refine ⟨411316238177688337737341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1096843301807168900632909 411316238177688337737341)
      ·
        refine ⟨154243589316633126651503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 411316238177688337737341 154243589316633126651503)
        ·
          refine ⟨231365383974949689977255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154243589316633126651503 231365383974949689977255)
          ·
            refine ⟨347048075962424534965883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231365383974949689977255 347048075962424534965883)
            ·
              refine ⟨520572113943636802448825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 347048075962424534965883 520572113943636802448825)
              ·
                refine ⟨390429085457727601836619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 520572113943636802448825 390429085457727601836619)
                ·
                  refine ⟨585643628186591402754929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 390429085457727601836619 585643628186591402754929)
                  ·
                    refine ⟨439232721139943552066197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 585643628186591402754929 439232721139943552066197)
                    ·
                      refine ⟨20589033803434854003103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 439232721139943552066197 20589033803434854003103)
                      ·
                        rfl

theorem cell23_40097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_40097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_40097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_40097 prefixEnd_40097 := by exact prefixLift 40097
  have htrace : WordTrace (prefixWord ++ tailWord_40097) baseStart_40097 baseEnd_40097 := by
    simpa [prefixWord, tailWord_40097, baseEnd_40097] using wordTrace_append hprefix tailTrace_40097
  have hstable : (prefixWord ++ tailWord_40097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40097).length < 2 ^ (prefixWord ++ tailWord_40097).sum := by decide
  have hdescent : baseEnd_40097 < baseStart_40097 := by decide
  rcases family_descends (prefixWord ++ tailWord_40097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40138 : List Nat := [3, 1, 2, 1, 3, 4, 1, 1, 3, 1, 3]
def baseStart_40138 : Nat := 118140960795 + 40138 * 2 ^ 59
def prefixEnd_40138 : Nat := 4983230072969 + 3 ^ 40 * 40138 * 2
def baseEnd_40138 : Nat := 20610086510269193590415

theorem tailTrace_40138 : CollatzResearch.WordTrace tailWord_40138 prefixEnd_40138 20610086510269193590415 := by
  unfold tailWord_40138
  simp only [CollatzResearch.WordTrace]
  refine ⟨365988282148588967438267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 975968752396237246502045 365988282148588967438267)
  ·
    refine ⟨548982423222883451157401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 365988282148588967438267 548982423222883451157401)
    ·
      refine ⟨411736817417162588368051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 548982423222883451157401 411736817417162588368051)
      ·
        refine ⟨617605226125743882552077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 411736817417162588368051 617605226125743882552077)
        ·
          refine ⟨231601959797153955957029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 617605226125743882552077 231601959797153955957029)
          ·
            refine ⟨43425367461966366741943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 231601959797153955957029 43425367461966366741943)
            ·
              refine ⟨65138051192949550112915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43425367461966366741943 65138051192949550112915)
              ·
                refine ⟨97707076789424325169373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65138051192949550112915 97707076789424325169373)
                ·
                  refine ⟨36640153796034121938515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 97707076789424325169373 36640153796034121938515)
                  ·
                    refine ⟨54960230694051182907773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36640153796034121938515 54960230694051182907773)
                    ·
                      refine ⟨20610086510269193590415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 54960230694051182907773 20610086510269193590415)
                      ·
                        rfl

theorem cell23_40138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 1, 3, 1, 3].length) (baseStart_40138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_40138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_40138 prefixEnd_40138 := by exact prefixLift 40138
  have htrace : WordTrace (prefixWord ++ tailWord_40138) baseStart_40138 baseEnd_40138 := by
    simpa [prefixWord, tailWord_40138, baseEnd_40138] using wordTrace_append hprefix tailTrace_40138
  have hstable : (prefixWord ++ tailWord_40138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40138).length < 2 ^ (prefixWord ++ tailWord_40138).sum := by decide
  have hdescent : baseEnd_40138 < baseStart_40138 := by decide
  rcases family_descends (prefixWord ++ tailWord_40138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40161 : List Nat := [1, 2, 3, 1, 3, 2, 3, 2, 1, 1, 4]
def baseStart_40161 : Nat := 118140960795 + 40161 * 2 ^ 59
def prefixEnd_40161 : Nat := 4983230072969 + 3 ^ 40 * 40161 * 2
def baseEnd_40161 : Nat := 20621896565322603602809

theorem tailTrace_40161 : CollatzResearch.WordTrace tailWord_40161 prefixEnd_40161 20621896565322603602809 := by
  unfold tailWord_40161
  simp only [CollatzResearch.WordTrace]
  refine ⟨1464792007511030797840337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 976528005007353865226891 1464792007511030797840337)
  ·
    refine ⟨1098594005633273098380253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1464792007511030797840337 1098594005633273098380253)
    ·
      refine ⟨411972752112477411892595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1098594005633273098380253 411972752112477411892595)
      ·
        refine ⟨617959128168716117838893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 411972752112477411892595 617959128168716117838893)
        ·
          refine ⟨231734673063268544189585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 617959128168716117838893 231734673063268544189585)
          ·
            refine ⟨173801004797451408142189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 231734673063268544189585 173801004797451408142189)
            ·
              refine ⟨65175376799044278053321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 173801004797451408142189 65175376799044278053321)
              ·
                refine ⟨48881532599283208539991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65175376799044278053321 48881532599283208539991)
                ·
                  refine ⟨73322298898924812809987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48881532599283208539991 73322298898924812809987)
                  ·
                    refine ⟨109983448348387219214981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 73322298898924812809987 109983448348387219214981)
                    ·
                      refine ⟨20621896565322603602809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 109983448348387219214981 20621896565322603602809)
                      ·
                        rfl

theorem cell23_40161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 2, 1, 1, 4].length) (baseStart_40161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_40161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_40161 prefixEnd_40161 := by exact prefixLift 40161
  have htrace : WordTrace (prefixWord ++ tailWord_40161) baseStart_40161 baseEnd_40161 := by
    simpa [prefixWord, tailWord_40161, baseEnd_40161] using wordTrace_append hprefix tailTrace_40161
  have hstable : (prefixWord ++ tailWord_40161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40161).length < 2 ^ (prefixWord ++ tailWord_40161).sum := by decide
  have hdescent : baseEnd_40161 < baseStart_40161 := by decide
  rcases family_descends (prefixWord ++ tailWord_40161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40174 : List Nat := [4, 1, 2, 1, 1, 1, 3, 1, 3, 2, 4]
def baseStart_40174 : Nat := 118140960795 + 40174 * 2 ^ 59
def prefixEnd_40174 : Nat := 4983230072969 + 3 ^ 40 * 40174 * 2
def baseEnd_40174 : Nat := 20628571813831052740249

theorem tailTrace_40174 : CollatzResearch.WordTrace tailWord_40174 prefixEnd_40174 20628571813831052740249 := by
  unfold tailWord_40174
  simp only [CollatzResearch.WordTrace]
  refine ⟨183158269557991752257947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 976844104309289345375717 183158269557991752257947)
  ·
    refine ⟨274737404336987628386921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183158269557991752257947 274737404336987628386921)
    ·
      refine ⟨206053053252740721290191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 274737404336987628386921 206053053252740721290191)
      ·
        refine ⟨309079579879111081935287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206053053252740721290191 309079579879111081935287)
        ·
          refine ⟨463619369818666622902931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 309079579879111081935287 463619369818666622902931)
          ·
            refine ⟨695429054727999934354397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 463619369818666622902931 695429054727999934354397)
            ·
              refine ⟨260785895522999975382899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 695429054727999934354397 260785895522999975382899)
              ·
                refine ⟨391178843284499963074349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 260785895522999975382899 391178843284499963074349)
                ·
                  refine ⟨146692066231687486152881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 391178843284499963074349 146692066231687486152881)
                  ·
                    refine ⟨110019049673765614614661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 146692066231687486152881 110019049673765614614661)
                    ·
                      refine ⟨20628571813831052740249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 110019049673765614614661 20628571813831052740249)
                      ·
                        rfl

theorem cell23_40174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_40174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_40174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_40174 prefixEnd_40174 := by exact prefixLift 40174
  have htrace : WordTrace (prefixWord ++ tailWord_40174) baseStart_40174 baseEnd_40174 := by
    simpa [prefixWord, tailWord_40174, baseEnd_40174] using wordTrace_append hprefix tailTrace_40174
  have hstable : (prefixWord ++ tailWord_40174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40174).length < 2 ^ (prefixWord ++ tailWord_40174).sum := by decide
  have hdescent : baseEnd_40174 < baseStart_40174 := by decide
  rcases family_descends (prefixWord ++ tailWord_40174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40188 : List Nat := [2, 2, 2, 1, 5, 1, 2, 2, 2, 4]
def baseStart_40188 : Nat := 118140960795 + 40188 * 2 ^ 59
def prefixEnd_40188 : Nat := 4983230072969 + 3 ^ 40 * 40188 * 2
def baseEnd_40188 : Nat := 6878586847664665988395

theorem tailTrace_40188 : CollatzResearch.WordTrace tailWord_40188 prefixEnd_40188 6878586847664665988395 := by
  unfold tailWord_40188
  simp only [CollatzResearch.WordTrace]
  refine ⟨732888389206607204536609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 977184518942142939382145 732888389206607204536609)
  ·
    refine ⟨549666291904955403402457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 732888389206607204536609 549666291904955403402457)
    ·
      refine ⟨412249718928716552551843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 549666291904955403402457 412249718928716552551843)
      ·
        refine ⟨618374578393074828827765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 412249718928716552551843 618374578393074828827765)
        ·
          refine ⟨57972616724350765202603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 618374578393074828827765 57972616724350765202603)
          ·
            refine ⟨86958925086526147803905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57972616724350765202603 86958925086526147803905)
            ·
              refine ⟨65219193814894610852929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86958925086526147803905 65219193814894610852929)
              ·
                refine ⟨48914395361170958139697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65219193814894610852929 48914395361170958139697)
                ·
                  refine ⟨36685796520878218604773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48914395361170958139697 36685796520878218604773)
                  ·
                    refine ⟨6878586847664665988395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36685796520878218604773 6878586847664665988395)
                    ·
                      rfl

theorem cell23_40188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 2, 2, 4].length) (baseStart_40188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_40188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_40188 prefixEnd_40188 := by exact prefixLift 40188
  have htrace : WordTrace (prefixWord ++ tailWord_40188) baseStart_40188 baseEnd_40188 := by
    simpa [prefixWord, tailWord_40188, baseEnd_40188] using wordTrace_append hprefix tailTrace_40188
  have hstable : (prefixWord ++ tailWord_40188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40188).length < 2 ^ (prefixWord ++ tailWord_40188).sum := by decide
  have hdescent : baseEnd_40188 < baseStart_40188 := by decide
  rcases family_descends (prefixWord ++ tailWord_40188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40195 : List Nat := [1, 1, 1, 3, 2, 5, 1, 4, 1, 2, 2]
def baseStart_40195 : Nat := 118140960795 + 40195 * 2 ^ 59
def prefixEnd_40195 : Nat := 4983230072969 + 3 ^ 40 * 40195 * 2
def baseEnd_40195 : Nat := 20639354907575470577653

theorem tailTrace_40195 : CollatzResearch.WordTrace tailWord_40195 prefixEnd_40195 20639354907575470577653 := by
  unfold tailWord_40195
  simp only [CollatzResearch.WordTrace]
  refine ⟨1466032089387854604578039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 977354726258569736385359 1466032089387854604578039)
  ·
    refine ⟨2199048134081781906867059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1466032089387854604578039 2199048134081781906867059)
    ·
      refine ⟨3298572201122672860300589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2199048134081781906867059 3298572201122672860300589)
      ·
        refine ⟨1236964575421002322612721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3298572201122672860300589 1236964575421002322612721)
        ·
          refine ⟨927723431565751741959541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1236964575421002322612721 927723431565751741959541)
          ·
            refine ⟨86974071709289225808707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 927723431565751741959541 86974071709289225808707)
            ·
              refine ⟨130461107563933838713061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86974071709289225808707 130461107563933838713061)
              ·
                refine ⟨24461457668237594758699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 130461107563933838713061 24461457668237594758699)
                ·
                  refine ⟨36692186502356392138049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24461457668237594758699 36692186502356392138049)
                  ·
                    refine ⟨27519139876767294103537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36692186502356392138049 27519139876767294103537)
                    ·
                      refine ⟨20639354907575470577653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 27519139876767294103537 20639354907575470577653)
                      ·
                        rfl

theorem cell23_40195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 4, 1, 2, 2].length) (baseStart_40195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_40195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_40195 prefixEnd_40195 := by exact prefixLift 40195
  have htrace : WordTrace (prefixWord ++ tailWord_40195) baseStart_40195 baseEnd_40195 := by
    simpa [prefixWord, tailWord_40195, baseEnd_40195] using wordTrace_append hprefix tailTrace_40195
  have hstable : (prefixWord ++ tailWord_40195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40195).length < 2 ^ (prefixWord ++ tailWord_40195).sum := by decide
  have hdescent : baseEnd_40195 < baseStart_40195 := by decide
  rcases family_descends (prefixWord ++ tailWord_40195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40197 : List Nat := [1, 3, 1, 1, 2, 1, 3, 1, 1, 9]
def baseStart_40197 : Nat := 118140960795 + 40197 * 2 ^ 59
def prefixEnd_40197 : Nat := 4983230072969 + 3 ^ 40 * 40197 * 2
def baseEnd_40197 : Nat := 6880127289628154250881

theorem tailTrace_40197 : CollatzResearch.WordTrace tailWord_40197 prefixEnd_40197 6880127289628154250881 := by
  unfold tailWord_40197
  simp only [CollatzResearch.WordTrace]
  refine ⟨1466105035380608946150845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 977403356920405964100563 1466105035380608946150845)
  ·
    refine ⟨549789388267728354806567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1466105035380608946150845 549789388267728354806567)
    ·
      refine ⟨824684082401592532209851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 549789388267728354806567 824684082401592532209851)
      ·
        refine ⟨1237026123602388798314777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 824684082401592532209851 1237026123602388798314777)
        ·
          refine ⟨927769592701791598736083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1237026123602388798314777 927769592701791598736083)
          ·
            refine ⟨1391654389052687398104125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 927769592701791598736083 1391654389052687398104125)
            ·
              refine ⟨521870395894757774289047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1391654389052687398104125 521870395894757774289047)
              ·
                refine ⟨782805593842136661433571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 521870395894757774289047 782805593842136661433571)
                ·
                  refine ⟨1174208390763204992150357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 782805593842136661433571 1174208390763204992150357)
                  ·
                    refine ⟨6880127289628154250881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 1174208390763204992150357 6880127289628154250881)
                    ·
                      rfl

theorem cell23_40197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 9].length) (baseStart_40197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_40197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_40197 prefixEnd_40197 := by exact prefixLift 40197
  have htrace : WordTrace (prefixWord ++ tailWord_40197) baseStart_40197 baseEnd_40197 := by
    simpa [prefixWord, tailWord_40197, baseEnd_40197] using wordTrace_append hprefix tailTrace_40197
  have hstable : (prefixWord ++ tailWord_40197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40197).length < 2 ^ (prefixWord ++ tailWord_40197).sum := by decide
  have hdescent : baseEnd_40197 < baseStart_40197 := by decide
  rcases family_descends (prefixWord ++ tailWord_40197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40207 : List Nat := [1, 1, 2, 1, 1, 1, 3, 1, 3, 4, 5]
def baseStart_40207 : Nat := 118140960795 + 40207 * 2 ^ 59
def prefixEnd_40207 : Nat := 4983230072969 + 3 ^ 40 * 40207 * 2
def baseEnd_40207 : Nat := 20645516675429423627597

theorem tailTrace_40207 : CollatzResearch.WordTrace tailWord_40207 prefixEnd_40207 20645516675429423627597 := by
  unfold tailWord_40207
  simp only [CollatzResearch.WordTrace]
  refine ⟨1466469765344380654014875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 977646510229587102676583 1466469765344380654014875)
  ·
    refine ⟨2199704648016570981022313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1466469765344380654014875 2199704648016570981022313)
    ·
      refine ⟨1649778486012428235766735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2199704648016570981022313 1649778486012428235766735)
      ·
        refine ⟨2474667729018642353650103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1649778486012428235766735 2474667729018642353650103)
        ·
          refine ⟨3712001593527963530475155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2474667729018642353650103 3712001593527963530475155)
          ·
            refine ⟨5568002390291945295712733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3712001593527963530475155 5568002390291945295712733)
            ·
              refine ⟨2088000896359479485892275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5568002390291945295712733 2088000896359479485892275)
              ·
                refine ⟨3132001344539219228838413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2088000896359479485892275 3132001344539219228838413)
                ·
                  refine ⟨1174500504202207210814405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3132001344539219228838413 1174500504202207210814405)
                  ·
                    refine ⟨220218844537913852027701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1174500504202207210814405 220218844537913852027701)
                    ·
                      refine ⟨20645516675429423627597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 220218844537913852027701 20645516675429423627597)
                      ·
                        rfl

theorem cell23_40207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 4, 5].length) (baseStart_40207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_40207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_40207 prefixEnd_40207 := by exact prefixLift 40207
  have htrace : WordTrace (prefixWord ++ tailWord_40207) baseStart_40207 baseEnd_40207 := by
    simpa [prefixWord, tailWord_40207, baseEnd_40207] using wordTrace_append hprefix tailTrace_40207
  have hstable : (prefixWord ++ tailWord_40207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40207).length < 2 ^ (prefixWord ++ tailWord_40207).sum := by decide
  have hdescent : baseEnd_40207 < baseStart_40207 := by decide
  rcases family_descends (prefixWord ++ tailWord_40207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40245 : List Nat := [1, 3, 3, 1, 2, 4, 1, 2, 2, 1, 3]
def baseStart_40245 : Nat := 118140960795 + 40245 * 2 ^ 59
def prefixEnd_40245 : Nat := 4983230072969 + 3 ^ 40 * 40245 * 2
def baseEnd_40245 : Nat := 20665028940300274952423

theorem tailTrace_40245 : CollatzResearch.WordTrace tailWord_40245 prefixEnd_40245 20665028940300274952423 := by
  unfold tailWord_40245
  simp only [CollatzResearch.WordTrace]
  refine ⟨1467855739206713143898189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 978570492804475429265459 1467855739206713143898189)
  ·
    refine ⟨550445902202517428961821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1467855739206713143898189 550445902202517428961821)
    ·
      refine ⟨206417213325944035860683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 550445902202517428961821 206417213325944035860683)
      ·
        refine ⟨309625819988916053791025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206417213325944035860683 309625819988916053791025)
        ·
          refine ⟨232219364991687040343269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 309625819988916053791025 232219364991687040343269)
          ·
            refine ⟨43541130935941320064363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 232219364991687040343269 43541130935941320064363)
            ·
              refine ⟨65311696403911980096545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43541130935941320064363 65311696403911980096545)
              ·
                refine ⟨48983772302933985072409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65311696403911980096545 48983772302933985072409)
                ·
                  refine ⟨36737829227200488804307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48983772302933985072409 36737829227200488804307)
                  ·
                    refine ⟨55106743840800733206461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36737829227200488804307 55106743840800733206461)
                    ·
                      refine ⟨20665028940300274952423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 55106743840800733206461 20665028940300274952423)
                      ·
                        rfl

theorem cell23_40245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 2, 2, 1, 3].length) (baseStart_40245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_40245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_40245 prefixEnd_40245 := by exact prefixLift 40245
  have htrace : WordTrace (prefixWord ++ tailWord_40245) baseStart_40245 baseEnd_40245 := by
    simpa [prefixWord, tailWord_40245, baseEnd_40245] using wordTrace_append hprefix tailTrace_40245
  have hstable : (prefixWord ++ tailWord_40245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40245).length < 2 ^ (prefixWord ++ tailWord_40245).sum := by decide
  have hdescent : baseEnd_40245 < baseStart_40245 := by decide
  rcases family_descends (prefixWord ++ tailWord_40245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40268 : List Nat := [2, 2, 1, 3, 2, 2, 3, 1, 1, 4, 2]
def baseStart_40268 : Nat := 118140960795 + 40268 * 2 ^ 59
def prefixEnd_40268 : Nat := 4983230072969 + 3 ^ 40 * 40268 * 2
def baseEnd_40268 : Nat := 20676838995353684964817

theorem tailTrace_40268 : CollatzResearch.WordTrace tailWord_40268 prefixEnd_40268 20676838995353684964817 := by
  unfold tailWord_40268
  simp only [CollatzResearch.WordTrace]
  refine ⟨734347309061694035992729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 979129745415592047990305 734347309061694035992729)
  ·
    refine ⟨550760481796270526994547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 734347309061694035992729 550760481796270526994547)
    ·
      refine ⟨826140722694405790491821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 550760481796270526994547 826140722694405790491821)
      ·
        refine ⟨309802771010402171434433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 826140722694405790491821 309802771010402171434433)
        ·
          refine ⟨232352078257801628575825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 309802771010402171434433 232352078257801628575825)
          ·
            refine ⟨174264058693351221431869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 232352078257801628575825 174264058693351221431869)
            ·
              refine ⟨65349022010006708036951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 174264058693351221431869 65349022010006708036951)
              ·
                refine ⟨98023533015010062055427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65349022010006708036951 98023533015010062055427)
                ·
                  refine ⟨147035299522515093083141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 98023533015010062055427 147035299522515093083141)
                  ·
                    refine ⟨27569118660471579953089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 147035299522515093083141 27569118660471579953089)
                    ·
                      refine ⟨20676838995353684964817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 27569118660471579953089 20676838995353684964817)
                      ·
                        rfl

theorem cell23_40268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 1, 1, 4, 2].length) (baseStart_40268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_40268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_40268 prefixEnd_40268 := by exact prefixLift 40268
  have htrace : WordTrace (prefixWord ++ tailWord_40268) baseStart_40268 baseEnd_40268 := by
    simpa [prefixWord, tailWord_40268, baseEnd_40268] using wordTrace_append hprefix tailTrace_40268
  have hstable : (prefixWord ++ tailWord_40268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40268).length < 2 ^ (prefixWord ++ tailWord_40268).sum := by decide
  have hdescent : baseEnd_40268 < baseStart_40268 := by decide
  rcases family_descends (prefixWord ++ tailWord_40268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40311 : List Nat := [1, 1, 3, 1, 1, 2, 4, 1, 2, 5, 2]
def baseStart_40311 : Nat := 118140960795 + 40311 * 2 ^ 59
def prefixEnd_40311 : Nat := 4983230072969 + 3 ^ 40 * 40311 * 2
def baseEnd_40311 : Nat := 20698918663497016727119

theorem tailTrace_40311 : CollatzResearch.WordTrace tailWord_40311 prefixEnd_40311 20698918663497016727119 := by
  unfold tailWord_40311
  simp only [CollatzResearch.WordTrace]
  refine ⟨1470262956967606415800787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 980175304645070943867191 1470262956967606415800787)
  ·
    refine ⟨2205394435451409623701181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1470262956967606415800787 2205394435451409623701181)
    ·
      refine ⟨827022913294278608887943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2205394435451409623701181 827022913294278608887943)
      ·
        refine ⟨1240534369941417913331915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 827022913294278608887943 1240534369941417913331915)
        ·
          refine ⟨1860801554912126869997873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1240534369941417913331915 1860801554912126869997873)
          ·
            refine ⟨1395601166184095152498405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1860801554912126869997873 1395601166184095152498405)
            ·
              refine ⟨261675218659517841093451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1395601166184095152498405 261675218659517841093451)
              ·
                refine ⟨392512827989276761640177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 261675218659517841093451 392512827989276761640177)
                ·
                  refine ⟨294384620991957571230133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 392512827989276761640177 294384620991957571230133)
                  ·
                    refine ⟨27598558217996022302825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 294384620991957571230133 27598558217996022302825)
                    ·
                      refine ⟨20698918663497016727119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 27598558217996022302825 20698918663497016727119)
                      ·
                        rfl

theorem cell23_40311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 2, 5, 2].length) (baseStart_40311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_40311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_40311 prefixEnd_40311 := by exact prefixLift 40311
  have htrace : WordTrace (prefixWord ++ tailWord_40311) baseStart_40311 baseEnd_40311 := by
    simpa [prefixWord, tailWord_40311, baseEnd_40311] using wordTrace_append hprefix tailTrace_40311
  have hstable : (prefixWord ++ tailWord_40311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40311).length < 2 ^ (prefixWord ++ tailWord_40311).sum := by decide
  have hdescent : baseEnd_40311 < baseStart_40311 := by decide
  rcases family_descends (prefixWord ++ tailWord_40311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40314 : List Nat := [3, 1, 1, 1, 1, 1, 2, 5, 1, 2, 5]
def baseStart_40314 : Nat := 118140960795 + 40314 * 2 ^ 59
def prefixEnd_40314 : Nat := 4983230072969 + 3 ^ 40 * 40314 * 2
def baseEnd_40314 : Nat := 20700459105460504989605

theorem tailTrace_40314 : CollatzResearch.WordTrace tailWord_40314 prefixEnd_40314 20700459105460504989605 := by
  unfold tailWord_40314
  simp only [CollatzResearch.WordTrace]
  refine ⟨367593093989184482039999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 980248250637825285439997 367593093989184482039999)
  ·
    refine ⟨551389640983776723059999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 367593093989184482039999 551389640983776723059999)
    ·
      refine ⟨827084461475665084589999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 551389640983776723059999 827084461475665084589999)
      ·
        refine ⟨1240626692213497626884999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 827084461475665084589999 1240626692213497626884999)
        ·
          refine ⟨1860940038320246440327499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1240626692213497626884999 1860940038320246440327499)
          ·
            refine ⟨2791410057480369660491249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1860940038320246440327499 2791410057480369660491249)
            ·
              refine ⟨2093557543110277245368437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2791410057480369660491249 2093557543110277245368437)
              ·
                refine ⟨196271019666588491753291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2093557543110277245368437 196271019666588491753291)
                ·
                  refine ⟨294406529499882737629937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 196271019666588491753291 294406529499882737629937)
                  ·
                    refine ⟨220804897124912053222453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 294406529499882737629937 220804897124912053222453)
                    ·
                      refine ⟨20700459105460504989605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 220804897124912053222453 20700459105460504989605)
                      ·
                        rfl

theorem cell23_40314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 5, 1, 2, 5].length) (baseStart_40314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_40314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_40314 prefixEnd_40314 := by exact prefixLift 40314
  have htrace : WordTrace (prefixWord ++ tailWord_40314) baseStart_40314 baseEnd_40314 := by
    simpa [prefixWord, tailWord_40314, baseEnd_40314] using wordTrace_append hprefix tailTrace_40314
  have hstable : (prefixWord ++ tailWord_40314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40314).length < 2 ^ (prefixWord ++ tailWord_40314).sum := by decide
  have hdescent : baseEnd_40314 < baseStart_40314 := by decide
  rcases family_descends (prefixWord ++ tailWord_40314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40341 : List Nat := [1, 3, 2, 1, 1, 2, 3, 3, 2, 1, 4]
def baseStart_40341 : Nat := 118140960795 + 40341 * 2 ^ 59
def prefixEnd_40341 : Nat := 4983230072969 + 3 ^ 40 * 40341 * 2
def baseEnd_40341 : Nat := 20714323083131899351981

theorem tailTrace_40341 : CollatzResearch.WordTrace tailWord_40341 prefixEnd_40341 20714323083131899351981 := by
  unfold tailWord_40341
  simp only [CollatzResearch.WordTrace]
  refine ⟨1471357146858921539392877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 980904764572614359595251 1471357146858921539392877)
  ·
    refine ⟨551758930072095577272329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1471357146858921539392877 551758930072095577272329)
    ·
      refine ⟨413819197554071682954247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 551758930072095577272329 413819197554071682954247)
      ·
        refine ⟨620728796331107524431371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 413819197554071682954247 620728796331107524431371)
        ·
          refine ⟨931093194496661286647057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 620728796331107524431371 931093194496661286647057)
          ·
            refine ⟨698319895872495964985293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 931093194496661286647057 698319895872495964985293)
            ·
              refine ⟨261869960952185986869485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 698319895872495964985293 261869960952185986869485)
              ·
                refine ⟨98201235357069745076057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 261869960952185986869485 98201235357069745076057)
                ·
                  refine ⟨73650926517802308807043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 98201235357069745076057 73650926517802308807043)
                  ·
                    refine ⟨110476389776703463210565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 73650926517802308807043 110476389776703463210565)
                    ·
                      refine ⟨20714323083131899351981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 110476389776703463210565 20714323083131899351981)
                      ·
                        rfl

theorem cell23_40341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 3, 2, 1, 4].length) (baseStart_40341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_40341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_40341 prefixEnd_40341 := by exact prefixLift 40341
  have htrace : WordTrace (prefixWord ++ tailWord_40341) baseStart_40341 baseEnd_40341 := by
    simpa [prefixWord, tailWord_40341, baseEnd_40341] using wordTrace_append hprefix tailTrace_40341
  have hstable : (prefixWord ++ tailWord_40341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40341).length < 2 ^ (prefixWord ++ tailWord_40341).sum := by decide
  have hdescent : baseEnd_40341 < baseStart_40341 := by decide
  rcases family_descends (prefixWord ++ tailWord_40341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40364 : List Nat := [2, 2, 1, 1, 1, 1, 4, 3, 8]
def baseStart_40364 : Nat := 118140960795 + 40364 * 2 ^ 59
def prefixEnd_40364 : Nat := 4983230072969 + 3 ^ 40 * 40364 * 2
def baseEnd_40364 : Nat := 2302903682020589929375

theorem tailTrace_40364 : CollatzResearch.WordTrace tailWord_40364 prefixEnd_40364 2302903682020589929375 := by
  unfold tailWord_40364
  simp only [CollatzResearch.WordTrace]
  refine ⟨736098012887798233740073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 981464017183730978320097 736098012887798233740073)
  ·
    refine ⟨552073509665848675305055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 736098012887798233740073 552073509665848675305055)
    ·
      refine ⟨828110264498773012957583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 552073509665848675305055 828110264498773012957583)
      ·
        refine ⟨1242165396748159519436375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 828110264498773012957583 1242165396748159519436375)
        ·
          refine ⟨1863248095122239279154563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1242165396748159519436375 1863248095122239279154563)
          ·
            refine ⟨2794872142683358918731845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1863248095122239279154563 2794872142683358918731845)
            ·
              refine ⟨524038526753129797262221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2794872142683358918731845 524038526753129797262221)
              ·
                refine ⟨196514447532423673973333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 524038526753129797262221 196514447532423673973333)
                ·
                  refine ⟨2302903682020589929375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 196514447532423673973333 2302903682020589929375)
                  ·
                    rfl

theorem cell23_40364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 8].length) (baseStart_40364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_40364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_40364 prefixEnd_40364 := by exact prefixLift 40364
  have htrace : WordTrace (prefixWord ++ tailWord_40364) baseStart_40364 baseEnd_40364 := by
    simpa [prefixWord, tailWord_40364, baseEnd_40364] using wordTrace_append hprefix tailTrace_40364
  have hstable : (prefixWord ++ tailWord_40364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40364).length < 2 ^ (prefixWord ++ tailWord_40364).sum := by decide
  have hdescent : baseEnd_40364 < baseStart_40364 := by decide
  rcases family_descends (prefixWord ++ tailWord_40364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40381 : List Nat := [1, 4, 1, 2, 2, 1, 1, 5, 6]
def baseStart_40381 : Nat := 118140960795 + 40381 * 2 ^ 59
def prefixEnd_40381 : Nat := 4983230072969 + 3 ^ 40 * 40381 * 2
def baseEnd_40381 : Nat := 2303873589923526983533

theorem tailTrace_40381 : CollatzResearch.WordTrace tailWord_40381 prefixEnd_40381 2303873589923526983533 := by
  unfold tailWord_40381
  simp only [CollatzResearch.WordTrace]
  refine ⟨1472816066714008370848997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 981877377809338913899331 1472816066714008370848997)
  ·
    refine ⟨276153012508876569534187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1472816066714008370848997 276153012508876569534187)
    ·
      refine ⟨414229518763314854301281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276153012508876569534187 414229518763314854301281)
      ·
        refine ⟨310672139072486140725961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 414229518763314854301281 310672139072486140725961)
        ·
          refine ⟨233004104304364605544471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 310672139072486140725961 233004104304364605544471)
          ·
            refine ⟨349506156456546908316707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233004104304364605544471 349506156456546908316707)
            ·
              refine ⟨524259234684820362475061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 349506156456546908316707 524259234684820362475061)
              ·
                refine ⟨49149303251701908982037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 524259234684820362475061 49149303251701908982037)
                ·
                  refine ⟨2303873589923526983533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 49149303251701908982037 2303873589923526983533)
                  ·
                    rfl

theorem cell23_40381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 5, 6].length) (baseStart_40381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_40381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_40381 prefixEnd_40381 := by exact prefixLift 40381
  have htrace : WordTrace (prefixWord ++ tailWord_40381) baseStart_40381 baseEnd_40381 := by
    simpa [prefixWord, tailWord_40381, baseEnd_40381] using wordTrace_append hprefix tailTrace_40381
  have hstable : (prefixWord ++ tailWord_40381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40381).length < 2 ^ (prefixWord ++ tailWord_40381).sum := by decide
  have hdescent : baseEnd_40381 < baseStart_40381 := by decide
  rcases family_descends (prefixWord ++ tailWord_40381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40431 : List Nat := [1, 1, 2, 1, 4, 1, 2, 1, 5, 1, 4]
def baseStart_40431 : Nat := 118140960795 + 40431 * 2 ^ 59
def prefixEnd_40431 : Nat := 4983230072969 + 3 ^ 40 * 40431 * 2
def baseEnd_40431 : Nat := 20760536342036547226567

theorem tailTrace_40431 : CollatzResearch.WordTrace tailWord_40431 prefixEnd_40431 20760536342036547226567 := by
  unfold tailWord_40431
  simp only [CollatzResearch.WordTrace]
  refine ⟨1474639716532866910169147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 983093144355244606779431 1474639716532866910169147)
  ·
    refine ⟨2211959574799300365253721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1474639716532866910169147 2211959574799300365253721)
    ·
      refine ⟨1658969681099475273940291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2211959574799300365253721 1658969681099475273940291)
      ·
        refine ⟨2488454521649212910910437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1658969681099475273940291 2488454521649212910910437)
        ·
          refine ⟨466585222809227420795707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2488454521649212910910437 466585222809227420795707)
          ·
            refine ⟨699877834213841131193561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 466585222809227420795707 699877834213841131193561)
            ·
              refine ⟨524908375660380848395171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 699877834213841131193561 524908375660380848395171)
              ·
                refine ⟨787362563490571272592757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 524908375660380848395171 787362563490571272592757)
                ·
                  refine ⟨73815240327241056805571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 787362563490571272592757 73815240327241056805571)
                  ·
                    refine ⟨110722860490861585208357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 73815240327241056805571 110722860490861585208357)
                    ·
                      refine ⟨20760536342036547226567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 110722860490861585208357 20760536342036547226567)
                      ·
                        rfl

theorem cell23_40431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 5, 1, 4].length) (baseStart_40431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_40431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_40431 prefixEnd_40431 := by exact prefixLift 40431
  have htrace : WordTrace (prefixWord ++ tailWord_40431) baseStart_40431 baseEnd_40431 := by
    simpa [prefixWord, tailWord_40431, baseEnd_40431] using wordTrace_append hprefix tailTrace_40431
  have hstable : (prefixWord ++ tailWord_40431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40431).length < 2 ^ (prefixWord ++ tailWord_40431).sum := by decide
  have hdescent : baseEnd_40431 < baseStart_40431 := by decide
  rcases family_descends (prefixWord ++ tailWord_40431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40458 : List Nat := [3, 1, 2, 2, 2, 2, 1, 2, 4, 4]
def baseStart_40458 : Nat := 118140960795 + 40458 * 2 ^ 59
def prefixEnd_40458 : Nat := 4983230072969 + 3 ^ 40 * 40458 * 2
def baseEnd_40458 : Nat := 6924800106569313862981

theorem tailTrace_40458 : CollatzResearch.WordTrace tailWord_40458 prefixEnd_40458 6924800106569313862981 := by
  unfold tailWord_40458
  simp only [CollatzResearch.WordTrace]
  refine ⟨368906121858762630350507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 983749658290033680934685 368906121858762630350507)
  ·
    refine ⟨553359182788143945525761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 368906121858762630350507 553359182788143945525761)
    ·
      refine ⟨415019387091107959144321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 553359182788143945525761 415019387091107959144321)
      ·
        refine ⟨311264540318330969358241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 415019387091107959144321 311264540318330969358241)
        ·
          refine ⟨233448405238748227018681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 311264540318330969358241 233448405238748227018681)
          ·
            refine ⟨175086303929061170264011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 233448405238748227018681 175086303929061170264011)
            ·
              refine ⟨262629455893591755396017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 175086303929061170264011 262629455893591755396017)
              ·
                refine ⟨196972091920193816547013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 262629455893591755396017 196972091920193816547013)
                ·
                  refine ⟨36932267235036340602565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 196972091920193816547013 36932267235036340602565)
                  ·
                    refine ⟨6924800106569313862981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36932267235036340602565 6924800106569313862981)
                    ·
                      rfl

theorem cell23_40458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 2, 4, 4].length) (baseStart_40458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_40458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_40458 prefixEnd_40458 := by exact prefixLift 40458
  have htrace : WordTrace (prefixWord ++ tailWord_40458) baseStart_40458 baseEnd_40458 := by
    simpa [prefixWord, tailWord_40458, baseEnd_40458] using wordTrace_append hprefix tailTrace_40458
  have hstable : (prefixWord ++ tailWord_40458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40458).length < 2 ^ (prefixWord ++ tailWord_40458).sum := by decide
  have hdescent : baseEnd_40458 < baseStart_40458 := by decide
  rcases family_descends (prefixWord ++ tailWord_40458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_40459 : List Nat := [1, 1, 1, 1, 8, 2, 1, 3, 1, 1, 3]
def baseStart_40459 : Nat := 118140960795 + 40459 * 2 ^ 59
def prefixEnd_40459 : Nat := 4983230072969 + 3 ^ 40 * 40459 * 2
def baseEnd_40459 : Nat := 20774913800362437676439

theorem tailTrace_40459 : CollatzResearch.WordTrace tailWord_40459 prefixEnd_40459 20774913800362437676439 := by
  unfold tailWord_40459
  simp only [CollatzResearch.WordTrace]
  refine ⟨1475660960431427692188431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 983773973620951794792287 1475660960431427692188431)
  ·
    refine ⟨2213491440647141538282647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1475660960431427692188431 2213491440647141538282647)
    ·
      refine ⟨3320237160970712307423971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2213491440647141538282647 3320237160970712307423971)
      ·
        refine ⟨4980355741456068461135957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3320237160970712307423971 4980355741456068461135957)
        ·
          refine ⟨58363543845188302278937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 4980355741456068461135957 58363543845188302278937)
          ·
            refine ⟨43772657883891226709203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58363543845188302278937 43772657883891226709203)
            ·
              refine ⟨65658986825836840063805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43772657883891226709203 65658986825836840063805)
              ·
                refine ⟨24622120059688815023927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65658986825836840063805 24622120059688815023927)
                ·
                  refine ⟨36933180089533222535891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24622120059688815023927 36933180089533222535891)
                  ·
                    refine ⟨55399770134299833803837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36933180089533222535891 55399770134299833803837)
                    ·
                      refine ⟨20774913800362437676439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 55399770134299833803837 20774913800362437676439)
                      ·
                        rfl

theorem cell23_40459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 3, 1, 1, 3].length) (baseStart_40459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_40459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_40459 prefixEnd_40459 := by exact prefixLift 40459
  have htrace : WordTrace (prefixWord ++ tailWord_40459) baseStart_40459 baseEnd_40459 := by
    simpa [prefixWord, tailWord_40459, baseEnd_40459] using wordTrace_append hprefix tailTrace_40459
  have hstable : (prefixWord ++ tailWord_40459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_40459).length < 2 ^ (prefixWord ++ tailWord_40459).sum := by decide
  have hdescent : baseEnd_40459 < baseStart_40459 := by decide
  rcases family_descends (prefixWord ++ tailWord_40459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
