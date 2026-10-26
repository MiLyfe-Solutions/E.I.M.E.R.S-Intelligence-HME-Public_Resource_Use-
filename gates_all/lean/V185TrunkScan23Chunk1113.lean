import V185TrunkScan23Chunk1112

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6591805 : List Nat := [1, 4, 1, 5, 2, 1, 1, 1, 1, 6]
def baseStart_6591805 : Nat := 118140960795 + 6591805 * 2 ^ 59
def prefixEnd_6591805 : Nat := 4983230072969 + 3 ^ 40 * 6591805 * 2
def baseEnd_6591805 : Nat := 1128254781903562422107449

theorem tailTrace_6591805 : CollatzResearch.WordTrace tailWord_6591805 prefixEnd_6591805 1128254781903562422107449 := by
  unfold tailWord_6591805
  simp only [CollatzResearch.WordTrace]
  refine ⟨240422879884023750510336869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160281919922682500340224579 240422879884023750510336869)
  ·
    refine ⟨45079289978254453220688163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 240422879884023750510336869 45079289978254453220688163)
    ·
      refine ⟨67618934967381679831032245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45079289978254453220688163 67618934967381679831032245)
      ·
        refine ⟨6339275153192032484159273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67618934967381679831032245 6339275153192032484159273)
        ·
          refine ⟨4754456364894024363119455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6339275153192032484159273 4754456364894024363119455)
          ·
            refine ⟨7131684547341036544679183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4754456364894024363119455 7131684547341036544679183)
            ·
              refine ⟨10697526821011554817018775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7131684547341036544679183 10697526821011554817018775)
              ·
                refine ⟨16046290231517332225528163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10697526821011554817018775 16046290231517332225528163)
                ·
                  refine ⟨24069435347275998338292245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16046290231517332225528163 24069435347275998338292245)
                  ·
                    refine ⟨1128254781903562422107449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24069435347275998338292245 1128254781903562422107449)
                    ·
                      rfl

theorem cell23_6591805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 1, 1, 6].length) (baseStart_6591805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6591805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6591805 prefixEnd_6591805 := by exact prefixLift 6591805
  have htrace : WordTrace (prefixWord ++ tailWord_6591805) baseStart_6591805 baseEnd_6591805 := by
    simpa [prefixWord, tailWord_6591805, baseEnd_6591805] using wordTrace_append hprefix tailTrace_6591805
  have hstable : (prefixWord ++ tailWord_6591805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6591805).length < 2 ^ (prefixWord ++ tailWord_6591805).sum := by decide
  have hdescent : baseEnd_6591805 < baseStart_6591805 := by decide
  rcases family_descends (prefixWord ++ tailWord_6591805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6592008 : List Nat := [2, 1, 3, 2, 1, 1, 2, 2, 5, 1, 3]
def baseStart_6592008 : Nat := 118140960795 + 6592008 * 2 ^ 59
def prefixEnd_6592008 : Nat := 4983230072969 + 3 ^ 40 * 6592008 * 2
def baseEnd_6592008 : Nat := 3384868582283549972083913

theorem tailTrace_6592008 : CollatzResearch.WordTrace tailWord_6592008 prefixEnd_6592008 3384868582283549972083913 := by
  unfold tailWord_6592008
  simp only [CollatzResearch.WordTrace]
  refine ⟨120215141951144158089988339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160286855934858877453317785 120215141951144158089988339)
  ·
    refine ⟨180322712926716237134982509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120215141951144158089988339 180322712926716237134982509)
    ·
      refine ⟨67621017347518588925618441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180322712926716237134982509 67621017347518588925618441)
      ·
        refine ⟨50715763010638941694213831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67621017347518588925618441 50715763010638941694213831)
        ·
          refine ⟨76073644515958412541320747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50715763010638941694213831 76073644515958412541320747)
          ·
            refine ⟨114110466773937618811981121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76073644515958412541320747 114110466773937618811981121)
            ·
              refine ⟨85582850080453214108985841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114110466773937618811981121 85582850080453214108985841)
              ·
                refine ⟨64187137560339910581739381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85582850080453214108985841 64187137560339910581739381)
                ·
                  refine ⟨6017544146281866617038067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64187137560339910581739381 6017544146281866617038067)
                  ·
                    refine ⟨9026316219422799925557101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6017544146281866617038067 9026316219422799925557101)
                    ·
                      refine ⟨3384868582283549972083913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9026316219422799925557101 3384868582283549972083913)
                      ·
                        rfl

theorem cell23_6592008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 5, 1, 3].length) (baseStart_6592008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6592008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6592008 prefixEnd_6592008 := by exact prefixLift 6592008
  have htrace : WordTrace (prefixWord ++ tailWord_6592008) baseStart_6592008 baseEnd_6592008 := by
    simpa [prefixWord, tailWord_6592008, baseEnd_6592008] using wordTrace_append hprefix tailTrace_6592008
  have hstable : (prefixWord ++ tailWord_6592008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6592008).length < 2 ^ (prefixWord ++ tailWord_6592008).sum := by decide
  have hdescent : baseEnd_6592008 < baseStart_6592008 := by decide
  rcases family_descends (prefixWord ++ tailWord_6592008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6592071 : List Nat := [1, 1, 4, 1, 5, 11]
def baseStart_6592071 : Nat := 118140960795 + 6592071 * 2 ^ 59
def prefixEnd_6592071 : Nat := 4983230072969 + 3 ^ 40 * 6592071 * 2
def baseEnd_6592071 : Nat := 13929633463229560599161

theorem tailTrace_6592071 : CollatzResearch.WordTrace tailWord_6592071 prefixEnd_6592071 13929633463229560599161 := by
  unfold tailWord_6592071
  simp only [CollatzResearch.WordTrace]
  refine ⟨240432581701060077939520067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160288387800706718626346711 240432581701060077939520067)
  ·
    refine ⟨360648872551590116909280101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240432581701060077939520067 360648872551590116909280101)
    ·
      refine ⟨67621663603423146920490019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 360648872551590116909280101 67621663603423146920490019)
      ·
        refine ⟨101432495405134720380735029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67621663603423146920490019 101432495405134720380735029)
        ·
          refine ⟨9509296444231380035693909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 101432495405134720380735029 9509296444231380035693909)
          ·
            refine ⟨13929633463229560599161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 9509296444231380035693909 13929633463229560599161)
            ·
              rfl

theorem cell23_6592071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 11].length) (baseStart_6592071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6592071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6592071 prefixEnd_6592071 := by exact prefixLift 6592071
  have htrace : WordTrace (prefixWord ++ tailWord_6592071) baseStart_6592071 baseEnd_6592071 := by
    simpa [prefixWord, tailWord_6592071, baseEnd_6592071] using wordTrace_append hprefix tailTrace_6592071
  have hstable : (prefixWord ++ tailWord_6592071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6592071).length < 2 ^ (prefixWord ++ tailWord_6592071).sum := by decide
  have hdescent : baseEnd_6592071 < baseStart_6592071 := by decide
  rcases family_descends (prefixWord ++ tailWord_6592071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6592111 : List Nat := [1, 1, 2, 1, 3, 2, 1, 3, 2, 2, 5]
def baseStart_6592111 : Nat := 118140960795 + 6592111 * 2 ^ 59
def prefixEnd_6592111 : Nat := 4983230072969 + 3 ^ 40 * 6592111 * 2
def baseEnd_6592111 : Nat := 3384921470790963069095939

theorem tailTrace_6592111 : CollatzResearch.WordTrace tailWord_6592111 prefixEnd_6592111 3384921470790963069095939 := by
  unfold tailWord_6592111
  simp only [CollatzResearch.WordTrace]
  refine ⟨240434040620915164770976187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160289360413943443180650791 240434040620915164770976187)
  ·
    refine ⟨360651060931372747156464281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240434040620915164770976187 360651060931372747156464281)
    ·
      refine ⟨270488295698529560367348211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 360651060931372747156464281 270488295698529560367348211)
      ·
        refine ⟨405732443547794340551022317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270488295698529560367348211 405732443547794340551022317)
        ·
          refine ⟨152149666330422877706633369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 405732443547794340551022317 152149666330422877706633369)
          ·
            refine ⟨114112249747817158279975027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152149666330422877706633369 114112249747817158279975027)
            ·
              refine ⟨171168374621725737419962541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114112249747817158279975027 171168374621725737419962541)
              ·
                refine ⟨64188140483147151532485953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 171168374621725737419962541 64188140483147151532485953)
                ·
                  refine ⟨48141105362360363649364465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64188140483147151532485953 48141105362360363649364465)
                  ·
                    refine ⟨36105829021770272737023349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48141105362360363649364465 36105829021770272737023349)
                    ·
                      refine ⟨3384921470790963069095939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36105829021770272737023349 3384921470790963069095939)
                      ·
                        rfl

theorem cell23_6592111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 2, 2, 5].length) (baseStart_6592111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6592111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6592111 prefixEnd_6592111 := by exact prefixLift 6592111
  have htrace : WordTrace (prefixWord ++ tailWord_6592111) baseStart_6592111 baseEnd_6592111 := by
    simpa [prefixWord, tailWord_6592111, baseEnd_6592111] using wordTrace_append hprefix tailTrace_6592111
  have hstable : (prefixWord ++ tailWord_6592111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6592111).length < 2 ^ (prefixWord ++ tailWord_6592111).sum := by decide
  have hdescent : baseEnd_6592111 < baseStart_6592111 := by decide
  rcases family_descends (prefixWord ++ tailWord_6592111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6592132 : List Nat := [2, 3, 2, 1, 4, 1, 1, 1, 4, 1, 3]
def baseStart_6592132 : Nat := 118140960795 + 6592132 * 2 ^ 59
def prefixEnd_6592132 : Nat := 4983230072969 + 3 ^ 40 * 6592132 * 2
def baseEnd_6592132 : Nat := 3384932253884707486933343

theorem tailTrace_6592132 : CollatzResearch.WordTrace tailWord_6592132 prefixEnd_6592132 3384932253884707486933343 := by
  unfold tailWord_6592132
  simp only [CollatzResearch.WordTrace]
  refine ⟨120217403276919542678745325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160289871035892723571660433 120217403276919542678745325)
  ·
    refine ⟨45081526228844828504529497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120217403276919542678745325 45081526228844828504529497)
    ·
      refine ⟨33811144671633621378397123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45081526228844828504529497 33811144671633621378397123)
      ·
        refine ⟨50716717007450432067595685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33811144671633621378397123 50716717007450432067595685)
        ·
          refine ⟨9509384438896956012674191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50716717007450432067595685 9509384438896956012674191)
          ·
            refine ⟨14264076658345434019011287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9509384438896956012674191 14264076658345434019011287)
            ·
              refine ⟨21396114987518151028516931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14264076658345434019011287 21396114987518151028516931)
              ·
                refine ⟨32094172481277226542775397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21396114987518151028516931 32094172481277226542775397)
                ·
                  refine ⟨6017657340239479976770387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32094172481277226542775397 6017657340239479976770387)
                  ·
                    refine ⟨9026486010359219965155581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6017657340239479976770387 9026486010359219965155581)
                    ·
                      refine ⟨3384932253884707486933343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9026486010359219965155581 3384932253884707486933343)
                      ·
                        rfl

theorem cell23_6592132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 1, 4, 1, 3].length) (baseStart_6592132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6592132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6592132 prefixEnd_6592132 := by exact prefixLift 6592132
  have htrace : WordTrace (prefixWord ++ tailWord_6592132) baseStart_6592132 baseEnd_6592132 := by
    simpa [prefixWord, tailWord_6592132, baseEnd_6592132] using wordTrace_append hprefix tailTrace_6592132
  have hstable : (prefixWord ++ tailWord_6592132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6592132).length < 2 ^ (prefixWord ++ tailWord_6592132).sum := by decide
  have hdescent : baseEnd_6592132 < baseStart_6592132 := by decide
  rcases family_descends (prefixWord ++ tailWord_6592132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6592282 : List Nat := [3, 1, 1, 3, 2, 2, 3, 1, 2, 2, 3]
def baseStart_6592282 : Nat := 118140960795 + 6592282 * 2 ^ 59
def prefixEnd_6592282 : Nat := 4983230072969 + 3 ^ 40 * 6592282 * 2
def baseEnd_6592282 : Nat := 3385009275982881900057653

theorem tailTrace_6592282 : CollatzResearch.WordTrace tailWord_6592282 prefixEnd_6592282 3385009275982881900057653 := by
  unfold tailWord_6592282
  simp only [CollatzResearch.WordTrace]
  refine ⟨60110069375823915243862775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160293518335530440650300733 60110069375823915243862775)
  ·
    refine ⟨90165104063735872865794163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60110069375823915243862775 90165104063735872865794163)
    ·
      refine ⟨135247656095603809298691245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90165104063735872865794163 135247656095603809298691245)
      ·
        refine ⟨50717871035851428487009217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135247656095603809298691245 50717871035851428487009217)
        ·
          refine ⟨38038403276888571365256913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50717871035851428487009217 38038403276888571365256913)
          ·
            refine ⟨28528802457666428523942685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38038403276888571365256913 28528802457666428523942685)
            ·
              refine ⟨10698300921624910696478507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28528802457666428523942685 10698300921624910696478507)
              ·
                refine ⟨16047451382437366044717761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10698300921624910696478507 16047451382437366044717761)
                ·
                  refine ⟨12035588536828024533538321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16047451382437366044717761 12035588536828024533538321)
                  ·
                    refine ⟨9026691402621018400153741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12035588536828024533538321 9026691402621018400153741)
                    ·
                      refine ⟨3385009275982881900057653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9026691402621018400153741 3385009275982881900057653)
                      ·
                        rfl

theorem cell23_6592282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 1, 2, 2, 3].length) (baseStart_6592282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6592282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6592282 prefixEnd_6592282 := by exact prefixLift 6592282
  have htrace : WordTrace (prefixWord ++ tailWord_6592282) baseStart_6592282 baseEnd_6592282 := by
    simpa [prefixWord, tailWord_6592282, baseEnd_6592282] using wordTrace_append hprefix tailTrace_6592282
  have hstable : (prefixWord ++ tailWord_6592282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6592282).length < 2 ^ (prefixWord ++ tailWord_6592282).sum := by decide
  have hdescent : baseEnd_6592282 < baseStart_6592282 := by decide
  rcases family_descends (prefixWord ++ tailWord_6592282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6592289 : List Nat := [1, 2, 3, 2, 1, 4, 2, 3, 1, 4]
def baseStart_6592289 : Nat := 118140960795 + 6592289 * 2 ^ 59
def prefixEnd_6592289 : Nat := 4983230072969 + 3 ^ 40 * 6592289 * 2
def baseEnd_6592289 : Nat := 1128337623449154457556707

theorem tailTrace_6592289 : CollatzResearch.WordTrace tailWord_6592289 prefixEnd_6592289 1128337623449154457556707 := by
  unfold tailWord_6592289
  simp only [CollatzResearch.WordTrace]
  refine ⟨240440532814270301170955921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160293688542846867447303947 240440532814270301170955921)
  ·
    refine ⟨180330399610702725878216941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240440532814270301170955921 180330399610702725878216941)
    ·
      refine ⟨67623899854013522204331353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180330399610702725878216941 67623899854013522204331353)
      ·
        refine ⟨50717924890510141653248515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67623899854013522204331353 50717924890510141653248515)
        ·
          refine ⟨76076887335765212479872773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50717924890510141653248515 76076887335765212479872773)
          ·
            refine ⟨14264416375455977339976145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76076887335765212479872773 14264416375455977339976145)
            ·
              refine ⟨10698312281591983004982109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14264416375455977339976145 10698312281591983004982109)
              ·
                refine ⟨4011867105596993626868291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10698312281591983004982109 4011867105596993626868291)
                ·
                  refine ⟨6017800658395490440302437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4011867105596993626868291 6017800658395490440302437)
                  ·
                    refine ⟨1128337623449154457556707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6017800658395490440302437 1128337623449154457556707)
                    ·
                      rfl

theorem cell23_6592289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 3, 1, 4].length) (baseStart_6592289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6592289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6592289 prefixEnd_6592289 := by exact prefixLift 6592289
  have htrace : WordTrace (prefixWord ++ tailWord_6592289) baseStart_6592289 baseEnd_6592289 := by
    simpa [prefixWord, tailWord_6592289, baseEnd_6592289] using wordTrace_append hprefix tailTrace_6592289
  have hstable : (prefixWord ++ tailWord_6592289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6592289).length < 2 ^ (prefixWord ++ tailWord_6592289).sum := by decide
  have hdescent : baseEnd_6592289 < baseStart_6592289 := by decide
  rcases family_descends (prefixWord ++ tailWord_6592289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6592302 : List Nat := [4, 1, 3, 2, 2, 1, 1, 1, 8]
def baseStart_6592302 : Nat := 118140960795 + 6592302 * 2 ^ 59
def prefixEnd_6592302 : Nat := 4983230072969 + 3 ^ 40 * 6592302 * 2
def baseEnd_6592302 : Nat := 376113282843996869089729

theorem tailTrace_6592302 : CollatzResearch.WordTrace tailWord_6592302 prefixEnd_6592302 376113282843996869089729 := by
  unfold tailWord_6592302
  simp only [CollatzResearch.WordTrace]
  refine ⟨30055125870402900548897395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160294004642148802927452773 30055125870402900548897395)
  ·
    refine ⟨45082688805604350823346093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30055125870402900548897395 45082688805604350823346093)
    ·
      refine ⟨16906008302101631558754785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45082688805604350823346093 16906008302101631558754785)
      ·
        refine ⟨12679506226576223669066089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16906008302101631558754785 12679506226576223669066089)
        ·
          refine ⟨9509629669932167751799567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12679506226576223669066089 9509629669932167751799567)
          ·
            refine ⟨14264444504898251627699351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9509629669932167751799567 14264444504898251627699351)
            ·
              refine ⟨21396666757347377441549027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14264444504898251627699351 21396666757347377441549027)
              ·
                refine ⟨32095000136021066162323541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21396666757347377441549027 32095000136021066162323541)
                ·
                  refine ⟨376113282843996869089729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32095000136021066162323541 376113282843996869089729)
                  ·
                    rfl

theorem cell23_6592302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 1, 8].length) (baseStart_6592302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6592302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6592302 prefixEnd_6592302 := by exact prefixLift 6592302
  have htrace : WordTrace (prefixWord ++ tailWord_6592302) baseStart_6592302 baseEnd_6592302 := by
    simpa [prefixWord, tailWord_6592302, baseEnd_6592302] using wordTrace_append hprefix tailTrace_6592302
  have hstable : (prefixWord ++ tailWord_6592302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6592302).length < 2 ^ (prefixWord ++ tailWord_6592302).sum := by decide
  have hdescent : baseEnd_6592302 < baseStart_6592302 := by decide
  rcases family_descends (prefixWord ++ tailWord_6592302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6592312 : List Nat := [2, 1, 2, 1, 3, 3, 1, 3, 3, 1, 3]
def baseStart_6592312 : Nat := 118140960795 + 6592312 * 2 ^ 59
def prefixEnd_6592312 : Nat := 4983230072969 + 3 ^ 40 * 6592312 * 2
def baseEnd_6592312 : Nat := 3385024680402516782682515

theorem tailTrace_6592312 : CollatzResearch.WordTrace tailWord_6592312 prefixEnd_6592312 3385024680402516782682515 := by
  unfold tailWord_6592312
  simp only [CollatzResearch.WordTrace]
  refine ⟨120220685846593488049521595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160294247795457984066028793 120220685846593488049521595)
  ·
    refine ⟨180331028769890232074282393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120220685846593488049521595 180331028769890232074282393)
    ·
      refine ⟨135248271577417674055711795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180331028769890232074282393 135248271577417674055711795)
      ·
        refine ⟨202872407366126511083567693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135248271577417674055711795 202872407366126511083567693)
        ·
          refine ⟨76077152762297441656337885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 202872407366126511083567693 76077152762297441656337885)
          ·
            refine ⟨28528932285861540621126707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76077152762297441656337885 28528932285861540621126707)
            ·
              refine ⟨42793398428792310931690061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28528932285861540621126707 42793398428792310931690061)
              ·
                refine ⟨16047524410797116599383773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42793398428792310931690061 16047524410797116599383773)
                ·
                  refine ⟨6017821654048918724768915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16047524410797116599383773 6017821654048918724768915)
                  ·
                    refine ⟨9026732481073378087153373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6017821654048918724768915 9026732481073378087153373)
                    ·
                      refine ⟨3385024680402516782682515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9026732481073378087153373 3385024680402516782682515)
                      ·
                        rfl

theorem cell23_6592312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 3, 3, 1, 3].length) (baseStart_6592312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6592312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6592312 prefixEnd_6592312 := by exact prefixLift 6592312
  have htrace : WordTrace (prefixWord ++ tailWord_6592312) baseStart_6592312 baseEnd_6592312 := by
    simpa [prefixWord, tailWord_6592312, baseEnd_6592312] using wordTrace_append hprefix tailTrace_6592312
  have hstable : (prefixWord ++ tailWord_6592312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6592312).length < 2 ^ (prefixWord ++ tailWord_6592312).sum := by decide
  have hdescent : baseEnd_6592312 < baseStart_6592312 := by decide
  rcases family_descends (prefixWord ++ tailWord_6592312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6592345 : List Nat := [1, 2, 1, 2, 2, 3, 1, 1, 6, 4]
def baseStart_6592345 : Nat := 118140960795 + 6592345 * 2 ^ 59
def prefixEnd_6592345 : Nat := 4983230072969 + 3 ^ 40 * 6592345 * 2
def baseEnd_6592345 : Nat := 1128347208421371717856621

theorem tailTrace_6592345 : CollatzResearch.WordTrace tailWord_6592345 prefixEnd_6592345 1128347208421371717856621 := by
  unfold tailWord_6592345
  simp only [CollatzResearch.WordTrace]
  refine ⟨240442575302067422734994489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160295050201378281823329659 240442575302067422734994489)
  ·
    refine ⟨180331931476550567051245867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240442575302067422734994489 180331931476550567051245867)
    ·
      refine ⟨270497897214825850576868801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180331931476550567051245867 270497897214825850576868801)
      ·
        refine ⟨202873422911119387932651601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270497897214825850576868801 202873422911119387932651601)
        ·
          refine ⟨152155067183339540949488701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202873422911119387932651601 152155067183339540949488701)
          ·
            refine ⟨57058150193752327856058263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 152155067183339540949488701 57058150193752327856058263)
            ·
              refine ⟨85587225290628491784087395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57058150193752327856058263 85587225290628491784087395)
              ·
                refine ⟨128380837935942737676131093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85587225290628491784087395 128380837935942737676131093)
                ·
                  refine ⟨6017851778247315828568645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 128380837935942737676131093 6017851778247315828568645)
                  ·
                    refine ⟨1128347208421371717856621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6017851778247315828568645 1128347208421371717856621)
                    ·
                      rfl

theorem cell23_6592345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 6, 4].length) (baseStart_6592345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6592345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6592345 prefixEnd_6592345 := by exact prefixLift 6592345
  have htrace : WordTrace (prefixWord ++ tailWord_6592345) baseStart_6592345 baseEnd_6592345 := by
    simpa [prefixWord, tailWord_6592345, baseEnd_6592345] using wordTrace_append hprefix tailTrace_6592345
  have hstable : (prefixWord ++ tailWord_6592345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6592345).length < 2 ^ (prefixWord ++ tailWord_6592345).sum := by decide
  have hdescent : baseEnd_6592345 < baseStart_6592345 := by decide
  rcases family_descends (prefixWord ++ tailWord_6592345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6592352 : List Nat := [2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 4]
def baseStart_6592352 : Nat := 118140960795 + 6592352 * 2 ^ 59
def prefixEnd_6592352 : Nat := 4983230072969 + 3 ^ 40 * 6592352 * 2
def baseEnd_6592352 : Nat := 3385045219628696626182331

theorem tailTrace_6592352 : CollatzResearch.WordTrace tailWord_6592352 prefixEnd_6592352 3385045219628696626182331 := by
  unfold tailWord_6592352
  simp only [CollatzResearch.WordTrace]
  refine ⟨120221415306521031465249655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160295220408694708620332873 120221415306521031465249655)
  ·
    refine ⟨180332122959781547197874483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120221415306521031465249655 180332122959781547197874483)
    ·
      refine ⟨270498184439672320796811725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180332122959781547197874483 270498184439672320796811725)
      ·
        refine ⟨101436819164877120298804397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 270498184439672320796811725 101436819164877120298804397)
        ·
          refine ⟨38038807186828920112051649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101436819164877120298804397 38038807186828920112051649)
          ·
            refine ⟨28529105390121690084038737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38038807186828920112051649 28529105390121690084038737)
            ·
              refine ⟨21396829042591267563029053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28529105390121690084038737 21396829042591267563029053)
              ·
                refine ⟨8023810890971725336135895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21396829042591267563029053 8023810890971725336135895)
                ·
                  refine ⟨12035716336457588004203843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8023810890971725336135895 12035716336457588004203843)
                  ·
                    refine ⟨18053574504686382006305765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12035716336457588004203843 18053574504686382006305765)
                    ·
                      refine ⟨3385045219628696626182331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18053574504686382006305765 3385045219628696626182331)
                      ·
                        rfl

theorem cell23_6592352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 4].length) (baseStart_6592352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6592352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6592352 prefixEnd_6592352 := by exact prefixLift 6592352
  have htrace : WordTrace (prefixWord ++ tailWord_6592352) baseStart_6592352 baseEnd_6592352 := by
    simpa [prefixWord, tailWord_6592352, baseEnd_6592352] using wordTrace_append hprefix tailTrace_6592352
  have hstable : (prefixWord ++ tailWord_6592352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6592352).length < 2 ^ (prefixWord ++ tailWord_6592352).sum := by decide
  have hdescent : baseEnd_6592352 < baseStart_6592352 := by decide
  rcases family_descends (prefixWord ++ tailWord_6592352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6592365 : List Nat := [1, 5, 1, 1, 1, 1, 3, 2, 1, 1, 6]
def baseStart_6592365 : Nat := 118140960795 + 6592365 * 2 ^ 59
def prefixEnd_6592365 : Nat := 4983230072969 + 3 ^ 40 * 6592365 * 2
def baseEnd_6592365 : Nat := 3385051894877205075319771

theorem tailTrace_6592365 : CollatzResearch.WordTrace tailWord_6592365 prefixEnd_6592365 3385051894877205075319771 := by
  unfold tailWord_6592365
  simp only [CollatzResearch.WordTrace]
  refine ⟨240443304761994966150722549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160295536507996644100481699 240443304761994966150722549)
  ·
    refine ⟨22541559821437028076630239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 240443304761994966150722549 22541559821437028076630239)
    ·
      refine ⟨33812339732155542114945359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22541559821437028076630239 33812339732155542114945359)
      ·
        refine ⟨50718509598233313172418039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33812339732155542114945359 50718509598233313172418039)
        ·
          refine ⟨76077764397349969758627059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50718509598233313172418039 76077764397349969758627059)
          ·
            refine ⟨114116646596024954637940589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76077764397349969758627059 114116646596024954637940589)
            ·
              refine ⟨42793742473509357989227721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114116646596024954637940589 42793742473509357989227721)
              ·
                refine ⟨32095306855132018491920791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42793742473509357989227721 32095306855132018491920791)
                ·
                  refine ⟨48142960282698027737881187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32095306855132018491920791 48142960282698027737881187)
                  ·
                    refine ⟨72214440424047041606821781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48142960282698027737881187 72214440424047041606821781)
                    ·
                      refine ⟨3385051894877205075319771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72214440424047041606821781 3385051894877205075319771)
                      ·
                        rfl

theorem cell23_6592365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_6592365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6592365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6592365 prefixEnd_6592365 := by exact prefixLift 6592365
  have htrace : WordTrace (prefixWord ++ tailWord_6592365) baseStart_6592365 baseEnd_6592365 := by
    simpa [prefixWord, tailWord_6592365, baseEnd_6592365] using wordTrace_append hprefix tailTrace_6592365
  have hstable : (prefixWord ++ tailWord_6592365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6592365).length < 2 ^ (prefixWord ++ tailWord_6592365).sum := by decide
  have hdescent : baseEnd_6592365 < baseStart_6592365 := by decide
  rcases family_descends (prefixWord ++ tailWord_6592365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6592414 : List Nat := [4, 3, 1, 3, 2, 1, 2, 2, 1, 1, 3]
def baseStart_6592414 : Nat := 118140960795 + 6592414 * 2 ^ 59
def prefixEnd_6592414 : Nat := 4983230072969 + 3 ^ 40 * 6592414 * 2
def baseEnd_6592414 : Nat := 3385077055429275383607047

theorem tailTrace_6592414 : CollatzResearch.WordTrace tailWord_6592414 prefixEnd_6592414 3385077055429275383607047 := by
  unfold tailWord_6592414
  simp only [CollatzResearch.WordTrace]
  refine ⟨30055636492352180939907037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160296727959211631679504197 30055636492352180939907037)
  ·
    refine ⟨11270863684632067852465139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30055636492352180939907037 11270863684632067852465139)
    ·
      refine ⟨16906295526948101778697709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11270863684632067852465139 16906295526948101778697709)
      ·
        refine ⟨6339860822605538167011641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16906295526948101778697709 6339860822605538167011641)
        ·
          refine ⟨4754895616954153625258731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6339860822605538167011641 4754895616954153625258731)
          ·
            refine ⟨7132343425431230437888097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4754895616954153625258731 7132343425431230437888097)
            ·
              refine ⟨5349257569073422828416073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7132343425431230437888097 5349257569073422828416073)
              ·
                refine ⟨4011943176805067121312055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5349257569073422828416073 4011943176805067121312055)
                ·
                  refine ⟨6017914765207600681968083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4011943176805067121312055 6017914765207600681968083)
                  ·
                    refine ⟨9026872147811401022952125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6017914765207600681968083 9026872147811401022952125)
                    ·
                      refine ⟨3385077055429275383607047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9026872147811401022952125 3385077055429275383607047)
                      ·
                        rfl

theorem cell23_6592414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_6592414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6592414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6592414 prefixEnd_6592414 := by exact prefixLift 6592414
  have htrace : WordTrace (prefixWord ++ tailWord_6592414) baseStart_6592414 baseEnd_6592414 := by
    simpa [prefixWord, tailWord_6592414, baseEnd_6592414] using wordTrace_append hprefix tailTrace_6592414
  have hstable : (prefixWord ++ tailWord_6592414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6592414).length < 2 ^ (prefixWord ++ tailWord_6592414).sum := by decide
  have hdescent : baseEnd_6592414 < baseStart_6592414 := by decide
  rcases family_descends (prefixWord ++ tailWord_6592414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6592420 : List Nat := [2, 3, 1, 2, 1, 5, 2, 2, 1, 2, 2]
def baseStart_6592420 : Nat := 118140960795 + 6592420 * 2 ^ 59
def prefixEnd_6592420 : Nat := 4983230072969 + 3 ^ 40 * 6592420 * 2
def baseEnd_6592420 : Nat := 3385080136313202360132019

theorem tailTrace_6592420 : CollatzResearch.WordTrace tailWord_6592420 prefixEnd_6592420 3385080136313202360132019 := by
  unfold tailWord_6592420
  simp only [CollatzResearch.WordTrace]
  refine ⟨120222655388397855271987357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160296873851197140362649809 120222655388397855271987357)
  ·
    refine ⟨45083495770649195726995259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120222655388397855271987357 45083495770649195726995259)
    ·
      refine ⟨67625243655973793590492889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45083495770649195726995259 67625243655973793590492889)
      ·
        refine ⟨50718932741980345192869667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67625243655973793590492889 50718932741980345192869667)
        ·
          refine ⟨76078399112970517789304501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50718932741980345192869667 76078399112970517789304501)
          ·
            refine ⟨7132349916840986042747297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76078399112970517789304501 7132349916840986042747297)
            ·
              refine ⟨5349262437630739532060473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7132349916840986042747297 5349262437630739532060473)
              ·
                refine ⟨4011946828223054649045355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5349262437630739532060473 4011946828223054649045355)
                ·
                  refine ⟨6017920242334581973568033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4011946828223054649045355 6017920242334581973568033)
                  ·
                    refine ⟨4513440181750936480176025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6017920242334581973568033 4513440181750936480176025)
                    ·
                      refine ⟨3385080136313202360132019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4513440181750936480176025 3385080136313202360132019)
                      ·
                        rfl

theorem cell23_6592420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 2, 2, 1, 2, 2].length) (baseStart_6592420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6592420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6592420 prefixEnd_6592420 := by exact prefixLift 6592420
  have htrace : WordTrace (prefixWord ++ tailWord_6592420) baseStart_6592420 baseEnd_6592420 := by
    simpa [prefixWord, tailWord_6592420, baseEnd_6592420] using wordTrace_append hprefix tailTrace_6592420
  have hstable : (prefixWord ++ tailWord_6592420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6592420).length < 2 ^ (prefixWord ++ tailWord_6592420).sum := by decide
  have hdescent : baseEnd_6592420 < baseStart_6592420 := by decide
  rcases family_descends (prefixWord ++ tailWord_6592420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6592435 : List Nat := [1, 1, 1, 2, 3, 1, 5, 1, 2, 6]
def baseStart_6592435 : Nat := 118140960795 + 6592435 * 2 ^ 59
def prefixEnd_6592435 : Nat := 4983230072969 + 3 ^ 40 * 6592435 * 2
def baseEnd_6592435 : Nat := 1128362612841006600481483

theorem tailTrace_6592435 : CollatzResearch.WordTrace tailWord_6592435 prefixEnd_6592435 1128362612841006600481483 := by
  unfold tailWord_6592435
  simp only [CollatzResearch.WordTrace]
  refine ⟨240445857871741368105770759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160297238581160912070513839 240445857871741368105770759)
  ·
    refine ⟨360668786807612052158656139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240445857871741368105770759 360668786807612052158656139)
    ·
      refine ⟨541003180211418078237984209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360668786807612052158656139 541003180211418078237984209)
      ·
        refine ⟨405752385158563558678488157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 541003180211418078237984209 405752385158563558678488157)
        ·
          refine ⟨152157144434461334504433059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 405752385158563558678488157 152157144434461334504433059)
          ·
            refine ⟨228235716651692001756649589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152157144434461334504433059 228235716651692001756649589)
            ·
              refine ⟨21397098436096125164685899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 228235716651692001756649589 21397098436096125164685899)
              ·
                refine ⟨32095647654144187747028849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21397098436096125164685899 32095647654144187747028849)
                ·
                  refine ⟨24071735740608140810271637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32095647654144187747028849 24071735740608140810271637)
                  ·
                    refine ⟨1128362612841006600481483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24071735740608140810271637 1128362612841006600481483)
                    ·
                      rfl

theorem cell23_6592435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 1, 2, 6].length) (baseStart_6592435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6592435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6592435 prefixEnd_6592435 := by exact prefixLift 6592435
  have htrace : WordTrace (prefixWord ++ tailWord_6592435) baseStart_6592435 baseEnd_6592435 := by
    simpa [prefixWord, tailWord_6592435, baseEnd_6592435] using wordTrace_append hprefix tailTrace_6592435
  have hstable : (prefixWord ++ tailWord_6592435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6592435).length < 2 ^ (prefixWord ++ tailWord_6592435).sum := by decide
  have hdescent : baseEnd_6592435 < baseStart_6592435 := by decide
  rcases family_descends (prefixWord ++ tailWord_6592435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6592455 : List Nat := [1, 1, 4, 1, 1, 2, 1, 1, 3, 4, 4]
def baseStart_6592455 : Nat := 118140960795 + 6592455 * 2 ^ 59
def prefixEnd_6592455 : Nat := 4983230072969 + 3 ^ 40 * 6592455 * 2
def baseEnd_6592455 : Nat := 3385098108136109723194357

theorem tailTrace_6592455 : CollatzResearch.WordTrace tailWord_6592455 prefixEnd_6592455 3385098108136109723194357 := by
  unfold tailWord_6592455
  simp only [CollatzResearch.WordTrace]
  refine ⟨240446587331668911521498819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160297724887779274347665879 240446587331668911521498819)
  ·
    refine ⟨360669880997503367282248229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240446587331668911521498819 360669880997503367282248229)
    ·
      refine ⟨67625602687031881365421543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 360669880997503367282248229 67625602687031881365421543)
      ·
        refine ⟨101438404030547822048132315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67625602687031881365421543 101438404030547822048132315)
        ·
          refine ⟨152157606045821733072198473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101438404030547822048132315 152157606045821733072198473)
          ·
            refine ⟨114118204534366299804148855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152157606045821733072198473 114118204534366299804148855)
            ·
              refine ⟨171177306801549449706223283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114118204534366299804148855 171177306801549449706223283)
              ·
                refine ⟨256765960202324174559334925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171177306801549449706223283 256765960202324174559334925)
                ·
                  refine ⟨96287235075871565459750597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 256765960202324174559334925 96287235075871565459750597)
                  ·
                    refine ⟨18053856576725918523703237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 96287235075871565459750597 18053856576725918523703237)
                    ·
                      refine ⟨3385098108136109723194357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18053856576725918523703237 3385098108136109723194357)
                      ·
                        rfl

theorem cell23_6592455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 4, 4].length) (baseStart_6592455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6592455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6592455 prefixEnd_6592455 := by exact prefixLift 6592455
  have htrace : WordTrace (prefixWord ++ tailWord_6592455) baseStart_6592455 baseEnd_6592455 := by
    simpa [prefixWord, tailWord_6592455, baseEnd_6592455] using wordTrace_append hprefix tailTrace_6592455
  have hstable : (prefixWord ++ tailWord_6592455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6592455).length < 2 ^ (prefixWord ++ tailWord_6592455).sum := by decide
  have hdescent : baseEnd_6592455 < baseStart_6592455 := by decide
  rcases family_descends (prefixWord ++ tailWord_6592455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6592459 : List Nat := [1, 1, 1, 1, 3, 4, 2, 2, 4, 2, 2]
def baseStart_6592459 : Nat := 118140960795 + 6592459 * 2 ^ 59
def prefixEnd_6592459 : Nat := 4983230072969 + 3 ^ 40 * 6592459 * 2
def baseEnd_6592459 : Nat := 3385100162058727707544339

theorem tailTrace_6592459 : CollatzResearch.WordTrace tailWord_6592459 prefixEnd_6592459 3385100162058727707544339 := by
  unfold tailWord_6592459
  simp only [CollatzResearch.WordTrace]
  refine ⟨240446733223654420204644431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160297822149102946803096287 240446733223654420204644431)
  ·
    refine ⟨360670099835481630306966647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240446733223654420204644431 360670099835481630306966647)
    ·
      refine ⟨541005149753222445460449971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360670099835481630306966647 541005149753222445460449971)
      ·
        refine ⟨811507724629833668190674957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 541005149753222445460449971 811507724629833668190674957)
        ·
          refine ⟨304315396736187625571503109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 811507724629833668190674957 304315396736187625571503109)
          ·
            refine ⟨57059136888035179794656833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 304315396736187625571503109 57059136888035179794656833)
            ·
              refine ⟨42794352666026384845992625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57059136888035179794656833 42794352666026384845992625)
              ·
                refine ⟨32095764499519788634494469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42794352666026384845992625 32095764499519788634494469)
                ·
                  refine ⟨6017955843659960368967713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32095764499519788634494469 6017955843659960368967713)
                  ·
                    refine ⟨4513466882744970276725785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6017955843659960368967713 4513466882744970276725785)
                    ·
                      refine ⟨3385100162058727707544339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4513466882744970276725785 3385100162058727707544339)
                      ·
                        rfl

theorem cell23_6592459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 2, 4, 2, 2].length) (baseStart_6592459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6592459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6592459 prefixEnd_6592459 := by exact prefixLift 6592459
  have htrace : WordTrace (prefixWord ++ tailWord_6592459) baseStart_6592459 baseEnd_6592459 := by
    simpa [prefixWord, tailWord_6592459, baseEnd_6592459] using wordTrace_append hprefix tailTrace_6592459
  have hstable : (prefixWord ++ tailWord_6592459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6592459).length < 2 ^ (prefixWord ++ tailWord_6592459).sum := by decide
  have hdescent : baseEnd_6592459 < baseStart_6592459 := by decide
  rcases family_descends (prefixWord ++ tailWord_6592459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6592470 : List Nat := [5, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3]
def baseStart_6592470 : Nat := 118140960795 + 6592470 * 2 ^ 59
def prefixEnd_6592470 : Nat := 4983230072969 + 3 ^ 40 * 6592470 * 2
def baseEnd_6592470 : Nat := 3385105810345927164506789

theorem tailTrace_6592470 : CollatzResearch.WordTrace tailWord_6592470 prefixEnd_6592470 3385105810345927164506789 := by
  unfold tailWord_6592470
  simp only [CollatzResearch.WordTrace]
  refine ⟨15027945901663410567705929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 160298089617743046055529909 15027945901663410567705929)
  ·
    refine ⟨11270959426247557925779447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15027945901663410567705929 11270959426247557925779447)
    ·
      refine ⟨16906439139371336888669171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11270959426247557925779447 16906439139371336888669171)
      ·
        refine ⟨25359658709057005333003757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16906439139371336888669171 25359658709057005333003757)
        ·
          refine ⟨9509872015896376999876409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25359658709057005333003757 9509872015896376999876409)
          ·
            refine ⟨7132404011922282749907307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9509872015896376999876409 7132404011922282749907307)
            ·
              refine ⟨10698606017883424124860961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7132404011922282749907307 10698606017883424124860961)
              ·
                refine ⟨8023954513412568093645721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10698606017883424124860961 8023954513412568093645721)
                ·
                  refine ⟨6017965885059426070234291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8023954513412568093645721 6017965885059426070234291)
                  ·
                    refine ⟨9026948827589139105351437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6017965885059426070234291 9026948827589139105351437)
                    ·
                      refine ⟨3385105810345927164506789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9026948827589139105351437 3385105810345927164506789)
                      ·
                        rfl

theorem cell23_6592470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_6592470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6592470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6592470 prefixEnd_6592470 := by exact prefixLift 6592470
  have htrace : WordTrace (prefixWord ++ tailWord_6592470) baseStart_6592470 baseEnd_6592470 := by
    simpa [prefixWord, tailWord_6592470, baseEnd_6592470] using wordTrace_append hprefix tailTrace_6592470
  have hstable : (prefixWord ++ tailWord_6592470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6592470).length < 2 ^ (prefixWord ++ tailWord_6592470).sum := by decide
  have hdescent : baseEnd_6592470 < baseStart_6592470 := by decide
  rcases family_descends (prefixWord ++ tailWord_6592470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6592495 : List Nat := [1, 1, 2, 1, 4, 2, 1, 1, 3, 7]
def baseStart_6592495 : Nat := 118140960795 + 6592495 * 2 ^ 59
def prefixEnd_6592495 : Nat := 4983230072969 + 3 ^ 40 * 6592495 * 2
def baseEnd_6592495 : Nat := 1128372882454096522231391

theorem tailTrace_6592495 : CollatzResearch.WordTrace tailWord_6592495 prefixEnd_6592495 1128372882454096522231391 := by
  unfold tailWord_6592495
  simp only [CollatzResearch.WordTrace]
  refine ⟨240448046251523998352954939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160298697501015998901969959 240448046251523998352954939)
  ·
    refine ⟨360672069377285997529432409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240448046251523998352954939 360672069377285997529432409)
    ·
      refine ⟨270504052032964498147074307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 360672069377285997529432409 270504052032964498147074307)
      ·
        refine ⟨405756078049446747220611461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270504052032964498147074307 405756078049446747220611461)
        ·
          refine ⟨76079264634271265103864649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 405756078049446747220611461 76079264634271265103864649)
          ·
            refine ⟨57059448475703448827898487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76079264634271265103864649 57059448475703448827898487)
            ·
              refine ⟨85589172713555173241847731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57059448475703448827898487 85589172713555173241847731)
              ·
                refine ⟨128383759070332759862771597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85589172713555173241847731 128383759070332759862771597)
                ·
                  refine ⟨48143909651374784948539349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 128383759070332759862771597 48143909651374784948539349)
                  ·
                    refine ⟨1128372882454096522231391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48143909651374784948539349 1128372882454096522231391)
                    ·
                      rfl

theorem cell23_6592495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 3, 7].length) (baseStart_6592495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6592495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6592495 prefixEnd_6592495 := by exact prefixLift 6592495
  have htrace : WordTrace (prefixWord ++ tailWord_6592495) baseStart_6592495 baseEnd_6592495 := by
    simpa [prefixWord, tailWord_6592495, baseEnd_6592495] using wordTrace_append hprefix tailTrace_6592495
  have hstable : (prefixWord ++ tailWord_6592495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6592495).length < 2 ^ (prefixWord ++ tailWord_6592495).sum := by decide
  have hdescent : baseEnd_6592495 < baseStart_6592495 := by decide
  rcases family_descends (prefixWord ++ tailWord_6592495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6592555 : List Nat := [1, 1, 1, 1, 2, 1, 4, 2, 10]
def baseStart_6592555 : Nat := 118140960795 + 6592555 * 2 ^ 59
def prefixEnd_6592555 : Nat := 4983230072969 + 3 ^ 40 * 6592555 * 2
def baseEnd_6592555 : Nat := 376127717355728814660433

theorem tailTrace_6592555 : CollatzResearch.WordTrace tailWord_6592555 prefixEnd_6592555 376127717355728814660433 := by
  unfold tailWord_6592555
  simp only [CollatzResearch.WordTrace]
  refine ⟨240450234631306628600139119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160300156420871085733426079 240450234631306628600139119)
  ·
    refine ⟨360675351946959942900208679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240450234631306628600139119 360675351946959942900208679)
    ·
      refine ⟨541013027920439914350313019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360675351946959942900208679 541013027920439914350313019)
      ·
        refine ⟨811519541880659871525469529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 541013027920439914350313019 811519541880659871525469529)
        ·
          refine ⟨608639656410494903644102147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 811519541880659871525469529 608639656410494903644102147)
          ·
            refine ⟨912959484615742355466153221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 608639656410494903644102147 912959484615742355466153221)
            ·
              refine ⟨171179903365451691649903729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 912959484615742355466153221 171179903365451691649903729)
              ·
                refine ⟨128384927524088768737427797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 171179903365451691649903729 128384927524088768737427797)
                ·
                  refine ⟨376127717355728814660433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 128384927524088768737427797 376127717355728814660433)
                  ·
                    rfl

theorem cell23_6592555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 10].length) (baseStart_6592555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6592555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6592555 prefixEnd_6592555 := by exact prefixLift 6592555
  have htrace : WordTrace (prefixWord ++ tailWord_6592555) baseStart_6592555 baseEnd_6592555 := by
    simpa [prefixWord, tailWord_6592555, baseEnd_6592555] using wordTrace_append hprefix tailTrace_6592555
  have hstable : (prefixWord ++ tailWord_6592555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6592555).length < 2 ^ (prefixWord ++ tailWord_6592555).sum := by decide
  have hdescent : baseEnd_6592555 < baseStart_6592555 := by decide
  rcases family_descends (prefixWord ++ tailWord_6592555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6592566 : List Nat := [5, 1, 2, 1, 1, 1, 4, 1, 2, 1, 4]
def baseStart_6592566 : Nat := 118140960795 + 6592566 * 2 ^ 59
def prefixEnd_6592566 : Nat := 4983230072969 + 3 ^ 40 * 6592566 * 2
def baseEnd_6592566 : Nat := 3385155104488758788906347

theorem tailTrace_6592566 : CollatzResearch.WordTrace tailWord_6592566 prefixEnd_6592566 3385155104488758788906347 := by
  unfold tailWord_6592566
  simp only [CollatzResearch.WordTrace]
  refine ⟨15028164739641673592424347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 160300423889511184985859701 15028164739641673592424347)
  ·
    refine ⟨22542247109462510388636521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15028164739641673592424347 22542247109462510388636521)
    ·
      refine ⟨16906685332096882791477391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22542247109462510388636521 16906685332096882791477391)
      ·
        refine ⟨25360027998145324187216087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16906685332096882791477391 25360027998145324187216087)
        ·
          refine ⟨38040041997217986280824131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25360027998145324187216087 38040041997217986280824131)
          ·
            refine ⟨57060062995826979421236197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38040041997217986280824131 57060062995826979421236197)
            ·
              refine ⟨10698761811717558641481787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57060062995826979421236197 10698761811717558641481787)
              ·
                refine ⟨16048142717576337962222681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10698761811717558641481787 16048142717576337962222681)
                ·
                  refine ⟨12036107038182253471667011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16048142717576337962222681 12036107038182253471667011)
                  ·
                    refine ⟨18054160557273380207500517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12036107038182253471667011 18054160557273380207500517)
                    ·
                      refine ⟨3385155104488758788906347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18054160557273380207500517 3385155104488758788906347)
                      ·
                        rfl

theorem cell23_6592566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_6592566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6592566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6592566 prefixEnd_6592566 := by exact prefixLift 6592566
  have htrace : WordTrace (prefixWord ++ tailWord_6592566) baseStart_6592566 baseEnd_6592566 := by
    simpa [prefixWord, tailWord_6592566, baseEnd_6592566] using wordTrace_append hprefix tailTrace_6592566
  have hstable : (prefixWord ++ tailWord_6592566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6592566).length < 2 ^ (prefixWord ++ tailWord_6592566).sum := by decide
  have hdescent : baseEnd_6592566 < baseStart_6592566 := by decide
  rcases family_descends (prefixWord ++ tailWord_6592566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6592602 : List Nat := [3, 1, 1, 2, 1, 1, 3, 1, 5, 5]
def baseStart_6592602 : Nat := 118140960795 + 6592602 * 2 ^ 59
def prefixEnd_6592602 : Nat := 4983230072969 + 3 ^ 40 * 6592602 * 2
def baseEnd_6592602 : Nat := 1128391196597440216018727

theorem tailTrace_6592602 : CollatzResearch.WordTrace tailWord_6592602 prefixEnd_6592602 1128391196597440216018727 := by
  unfold tailWord_6592602
  simp only [CollatzResearch.WordTrace]
  refine ⟨60112987215534088906775015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160301299241424237084733373 60112987215534088906775015)
  ·
    refine ⟨90169480823301133360162523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60112987215534088906775015 90169480823301133360162523)
    ·
      refine ⟨135254221234951700040243785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90169480823301133360162523 135254221234951700040243785)
      ·
        refine ⟨101440665926213775030182839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135254221234951700040243785 101440665926213775030182839)
        ·
          refine ⟨152160998889320662545274259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101440665926213775030182839 152160998889320662545274259)
          ·
            refine ⟨228241498333980993817911389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152160998889320662545274259 228241498333980993817911389)
            ·
              refine ⟨85590561875242872681716771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 228241498333980993817911389 85590561875242872681716771)
              ·
                refine ⟨128385842812864309022575157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85590561875242872681716771 128385842812864309022575157)
                ·
                  refine ⟨12036172763706028970866421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 128385842812864309022575157 12036172763706028970866421)
                  ·
                    refine ⟨1128391196597440216018727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12036172763706028970866421 1128391196597440216018727)
                    ·
                      rfl

theorem cell23_6592602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 5, 5].length) (baseStart_6592602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6592602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6592602 prefixEnd_6592602 := by exact prefixLift 6592602
  have htrace : WordTrace (prefixWord ++ tailWord_6592602) baseStart_6592602 baseEnd_6592602 := by
    simpa [prefixWord, tailWord_6592602, baseEnd_6592602] using wordTrace_append hprefix tailTrace_6592602
  have hstable : (prefixWord ++ tailWord_6592602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6592602).length < 2 ^ (prefixWord ++ tailWord_6592602).sum := by decide
  have hdescent : baseEnd_6592602 < baseStart_6592602 := by decide
  rcases family_descends (prefixWord ++ tailWord_6592602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6592609 : List Nat := [1, 2, 3, 1, 1, 2, 1, 4, 1, 5, 2]
def baseStart_6592609 : Nat := 118140960795 + 6592609 * 2 ^ 59
def prefixEnd_6592609 : Nat := 4983230072969 + 3 ^ 40 * 6592609 * 2
def baseEnd_6592609 : Nat := 3385177184156902120668649

theorem tailTrace_6592609 : CollatzResearch.WordTrace tailWord_6592609 prefixEnd_6592609 3385177184156902120668649 := by
  unfold tailWord_6592609
  simp only [CollatzResearch.WordTrace]
  refine ⟨240452204173110995822604881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160301469448740663881736587 240452204173110995822604881)
  ·
    refine ⟨180339153129833246866953661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240452204173110995822604881 180339153129833246866953661)
    ·
      refine ⟨67627182423687467575107623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180339153129833246866953661 67627182423687467575107623)
      ·
        refine ⟨101440773635531201362661435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67627182423687467575107623 101440773635531201362661435)
        ·
          refine ⟨152161160453296802043992153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101440773635531201362661435 152161160453296802043992153)
          ·
            refine ⟨114120870339972601532994115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152161160453296802043992153 114120870339972601532994115)
            ·
              refine ⟨171181305509958902299491173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114120870339972601532994115 171181305509958902299491173)
              ·
                refine ⟨32096494783117294181154595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 171181305509958902299491173 32096494783117294181154595)
                ·
                  refine ⟨48144742174675941271731893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32096494783117294181154595 48144742174675941271731893)
                  ·
                    refine ⟨4513569578875869494224865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48144742174675941271731893 4513569578875869494224865)
                    ·
                      refine ⟨3385177184156902120668649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4513569578875869494224865 3385177184156902120668649)
                      ·
                        rfl

theorem cell23_6592609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 4, 1, 5, 2].length) (baseStart_6592609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6592609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6592609 prefixEnd_6592609 := by exact prefixLift 6592609
  have htrace : WordTrace (prefixWord ++ tailWord_6592609) baseStart_6592609 baseEnd_6592609 := by
    simpa [prefixWord, tailWord_6592609, baseEnd_6592609] using wordTrace_append hprefix tailTrace_6592609
  have hstable : (prefixWord ++ tailWord_6592609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6592609).length < 2 ^ (prefixWord ++ tailWord_6592609).sum := by decide
  have hdescent : baseEnd_6592609 < baseStart_6592609 := by decide
  rcases family_descends (prefixWord ++ tailWord_6592609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6592626 : List Nat := [3, 2, 1, 2, 2, 3, 1, 1, 1, 5, 2]
def baseStart_6592626 : Nat := 118140960795 + 6592626 * 2 ^ 59
def prefixEnd_6592626 : Nat := 4983230072969 + 3 ^ 40 * 6592626 * 2
def baseEnd_6592626 : Nat := 3385185913328028554156071

theorem tailTrace_6592626 : CollatzResearch.WordTrace tailWord_6592626 prefixEnd_6592626 3385185913328028554156071 := by
  unfold tailWord_6592626
  simp only [CollatzResearch.WordTrace]
  refine ⟨60113206053512351931493433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160301882809366271817315821 60113206053512351931493433)
  ·
    refine ⟨45084904540134263948620075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60113206053512351931493433 45084904540134263948620075)
    ·
      refine ⟨67627356810201395922930113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45084904540134263948620075 67627356810201395922930113)
      ·
        refine ⟨50720517607651046942197585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67627356810201395922930113 50720517607651046942197585)
        ·
          refine ⟨38040388205738285206648189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50720517607651046942197585 38040388205738285206648189)
          ·
            refine ⟨14265145577151856952493071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38040388205738285206648189 14265145577151856952493071)
            ·
              refine ⟨21397718365727785428739607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14265145577151856952493071 21397718365727785428739607)
              ·
                refine ⟨32096577548591678143109411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21397718365727785428739607 32096577548591678143109411)
                ·
                  refine ⟨48144866322887517214664117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32096577548591678143109411 48144866322887517214664117)
                  ·
                    refine ⟨4513581217770704738874761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48144866322887517214664117 4513581217770704738874761)
                    ·
                      refine ⟨3385185913328028554156071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4513581217770704738874761 3385185913328028554156071)
                      ·
                        rfl

theorem cell23_6592626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 1, 1, 5, 2].length) (baseStart_6592626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6592626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6592626 prefixEnd_6592626 := by exact prefixLift 6592626
  have htrace : WordTrace (prefixWord ++ tailWord_6592626) baseStart_6592626 baseEnd_6592626 := by
    simpa [prefixWord, tailWord_6592626, baseEnd_6592626] using wordTrace_append hprefix tailTrace_6592626
  have hstable : (prefixWord ++ tailWord_6592626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6592626).length < 2 ^ (prefixWord ++ tailWord_6592626).sum := by decide
  have hdescent : baseEnd_6592626 < baseStart_6592626 := by decide
  rcases family_descends (prefixWord ++ tailWord_6592626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6592633 : List Nat := [1, 2, 1, 3, 4, 1, 1, 5, 1, 1, 3]
def baseStart_6592633 : Nat := 118140960795 + 6592633 * 2 ^ 59
def prefixEnd_6592633 : Nat := 4983230072969 + 3 ^ 40 * 6592633 * 2
def baseEnd_6592633 : Nat := 3385189507692610026768539

theorem tailTrace_6592633 : CollatzResearch.WordTrace tailWord_6592633 prefixEnd_6592633 3385189507692610026768539 := by
  unfold tailWord_6592633
  simp only [CollatzResearch.WordTrace]
  refine ⟨240453079525024047921478553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160302053016682698614319035 240453079525024047921478553)
  ·
    refine ⟨180339809643768035941108915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240453079525024047921478553 180339809643768035941108915)
    ·
      refine ⟨270509714465652053911663373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180339809643768035941108915 270509714465652053911663373)
      ·
        refine ⟨101441142924619520216873765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 270509714465652053911663373 101441142924619520216873765)
        ·
          refine ⟨19020214298366160040663831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101441142924619520216873765 19020214298366160040663831)
          ·
            refine ⟨28530321447549240060995747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19020214298366160040663831 28530321447549240060995747)
            ·
              refine ⟨42795482171323860091493621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28530321447549240060995747 42795482171323860091493621)
              ·
                refine ⟨4012076453561611883577527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42795482171323860091493621 4012076453561611883577527)
                ·
                  refine ⟨6018114680342417825366291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4012076453561611883577527 6018114680342417825366291)
                  ·
                    refine ⟨9027172020513626738049437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6018114680342417825366291 9027172020513626738049437)
                    ·
                      refine ⟨3385189507692610026768539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9027172020513626738049437 3385189507692610026768539)
                      ·
                        rfl

theorem cell23_6592633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 5, 1, 1, 3].length) (baseStart_6592633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6592633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6592633 prefixEnd_6592633 := by exact prefixLift 6592633
  have htrace : WordTrace (prefixWord ++ tailWord_6592633) baseStart_6592633 baseEnd_6592633 := by
    simpa [prefixWord, tailWord_6592633, baseEnd_6592633] using wordTrace_append hprefix tailTrace_6592633
  have hstable : (prefixWord ++ tailWord_6592633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6592633).length < 2 ^ (prefixWord ++ tailWord_6592633).sum := by decide
  have hdescent : baseEnd_6592633 < baseStart_6592633 := by decide
  rcases family_descends (prefixWord ++ tailWord_6592633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6592636 : List Nat := [2, 2, 2, 1, 1, 4, 4, 1, 1, 5]
def baseStart_6592636 : Nat := 118140960795 + 6592636 * 2 ^ 59
def prefixEnd_6592636 : Nat := 4983230072969 + 3 ^ 40 * 6592636 * 2
def baseEnd_6592636 : Nat := 1128397016044857838343675

theorem tailTrace_6592636 : CollatzResearch.WordTrace tailWord_6592636 prefixEnd_6592636 1128397016044857838343675 := by
  unfold tailWord_6592636
  simp only [CollatzResearch.WordTrace]
  refine ⟨120226594472006589716918881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160302125962675452955891841 120226594472006589716918881)
  ·
    refine ⟨90169945854004942287689161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120226594472006589716918881 90169945854004942287689161)
    ·
      refine ⟨67627459390503706715766871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90169945854004942287689161 67627459390503706715766871)
      ·
        refine ⟨101441189085755560073650307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67627459390503706715766871 101441189085755560073650307)
        ·
          refine ⟨152161783628633340110475461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101441189085755560073650307 152161783628633340110475461)
          ·
            refine ⟨28530334430368751270714149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 152161783628633340110475461 28530334430368751270714149)
            ·
              refine ⟨5349437705694140863258903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28530334430368751270714149 5349437705694140863258903)
              ·
                refine ⟨8024156558541211294888355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5349437705694140863258903 8024156558541211294888355)
                ·
                  refine ⟨12036234837811816942332533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8024156558541211294888355 12036234837811816942332533)
                  ·
                    refine ⟨1128397016044857838343675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12036234837811816942332533 1128397016044857838343675)
                    ·
                      rfl

theorem cell23_6592636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 4, 1, 1, 5].length) (baseStart_6592636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6592636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6592636 prefixEnd_6592636 := by exact prefixLift 6592636
  have htrace : WordTrace (prefixWord ++ tailWord_6592636) baseStart_6592636 baseEnd_6592636 := by
    simpa [prefixWord, tailWord_6592636, baseEnd_6592636] using wordTrace_append hprefix tailTrace_6592636
  have hstable : (prefixWord ++ tailWord_6592636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6592636).length < 2 ^ (prefixWord ++ tailWord_6592636).sum := by decide
  have hdescent : baseEnd_6592636 < baseStart_6592636 := by decide
  rcases family_descends (prefixWord ++ tailWord_6592636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6592649 : List Nat := [1, 2, 1, 1, 4, 2, 3, 1, 4, 4]
def baseStart_6592649 : Nat := 118140960795 + 6592649 * 2 ^ 59
def prefixEnd_6592649 : Nat := 4983230072969 + 3 ^ 40 * 6592649 * 2
def baseEnd_6592649 : Nat := 1128399241127693988056155

theorem tailTrace_6592649 : CollatzResearch.WordTrace tailWord_6592649 prefixEnd_6592649 1128399241127693988056155 := by
  unfold tailWord_6592649
  simp only [CollatzResearch.WordTrace]
  refine ⟨240453663092966082654061001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160302442061977388436040667 240453663092966082654061001)
  ·
    refine ⟨180340247319724561990545751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240453663092966082654061001 180340247319724561990545751)
    ·
      refine ⟨270510370979586842985818627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180340247319724561990545751 270510370979586842985818627)
      ·
        refine ⟨405765556469380264478727941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270510370979586842985818627 405765556469380264478727941)
        ·
          refine ⟨76081041838008799589761489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 405765556469380264478727941 76081041838008799589761489)
          ·
            refine ⟨57060781378506599692321117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76081041838008799589761489 57060781378506599692321117)
            ·
              refine ⟨21397793016939974884620419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57060781378506599692321117 21397793016939974884620419)
              ·
                refine ⟨32096689525409962326930629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21397793016939974884620419 32096689525409962326930629)
                ·
                  refine ⟨6018129286014367936299493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32096689525409962326930629 6018129286014367936299493)
                  ·
                    refine ⟨1128399241127693988056155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6018129286014367936299493 1128399241127693988056155)
                    ·
                      rfl

theorem cell23_6592649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 1, 4, 4].length) (baseStart_6592649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6592649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6592649 prefixEnd_6592649 := by exact prefixLift 6592649
  have htrace : WordTrace (prefixWord ++ tailWord_6592649) baseStart_6592649 baseEnd_6592649 := by
    simpa [prefixWord, tailWord_6592649, baseEnd_6592649] using wordTrace_append hprefix tailTrace_6592649
  have hstable : (prefixWord ++ tailWord_6592649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6592649).length < 2 ^ (prefixWord ++ tailWord_6592649).sum := by decide
  have hdescent : baseEnd_6592649 < baseStart_6592649 := by decide
  rcases family_descends (prefixWord ++ tailWord_6592649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6592652 : List Nat := [2, 2, 1, 2, 1, 1, 1, 1, 2, 6, 4]
def baseStart_6592652 : Nat := 118140960795 + 6592652 * 2 ^ 59
def prefixEnd_6592652 : Nat := 4983230072969 + 3 ^ 40 * 6592652 * 2
def baseEnd_6592652 : Nat := 3385199263825045452430951

theorem tailTrace_6592652 : CollatzResearch.WordTrace tailWord_6592652 prefixEnd_6592652 3385199263825045452430951 := by
  unfold tailWord_6592652
  simp only [CollatzResearch.WordTrace]
  refine ⟨120226886255977607083210105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160302515007970142777613473 120226886255977607083210105)
  ·
    refine ⟨90170164691983205312407579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120226886255977607083210105 90170164691983205312407579)
    ·
      refine ⟨135255247037974807968611369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90170164691983205312407579 135255247037974807968611369)
      ·
        refine ⟨101441435278481105976458527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135255247037974807968611369 101441435278481105976458527)
        ·
          refine ⟨152162152917721658964687791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101441435278481105976458527 152162152917721658964687791)
          ·
            refine ⟨228243229376582488447031687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152162152917721658964687791 228243229376582488447031687)
            ·
              refine ⟨342364844064873732670547531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228243229376582488447031687 342364844064873732670547531)
              ·
                refine ⟨513547266097310599005821297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 342364844064873732670547531 513547266097310599005821297)
                ·
                  refine ⟨385160449572982949254365973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 513547266097310599005821297 385160449572982949254365973)
                  ·
                    refine ⟨18054396073733575746298405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 385160449572982949254365973 18054396073733575746298405)
                    ·
                      refine ⟨3385199263825045452430951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18054396073733575746298405 3385199263825045452430951)
                      ·
                        rfl

theorem cell23_6592652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 2, 6, 4].length) (baseStart_6592652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6592652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6592652 prefixEnd_6592652 := by exact prefixLift 6592652
  have htrace : WordTrace (prefixWord ++ tailWord_6592652) baseStart_6592652 baseEnd_6592652 := by
    simpa [prefixWord, tailWord_6592652, baseEnd_6592652] using wordTrace_append hprefix tailTrace_6592652
  have hstable : (prefixWord ++ tailWord_6592652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6592652).length < 2 ^ (prefixWord ++ tailWord_6592652).sum := by decide
  have hdescent : baseEnd_6592652 < baseStart_6592652 := by decide
  rcases family_descends (prefixWord ++ tailWord_6592652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6592669 : List Nat := [1, 4, 2, 1, 1, 4, 1, 1, 1, 1, 6]
def baseStart_6592669 : Nat := 118140960795 + 6592669 * 2 ^ 59
def prefixEnd_6592669 : Nat := 4983230072969 + 3 ^ 40 * 6592669 * 2
def baseEnd_6592669 : Nat := 3385207992996171885918373

theorem tailTrace_6592669 : CollatzResearch.WordTrace tailWord_6592669 prefixEnd_6592669 3385207992996171885918373 := by
  unfold tailWord_6592669
  simp only [CollatzResearch.WordTrace]
  refine ⟨240454392552893626069789061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160302928368595750713192707 240454392552893626069789061)
  ·
    refine ⟨45085198603667554888085449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 240454392552893626069789061 45085198603667554888085449)
    ·
      refine ⟨33813898952750666166064087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45085198603667554888085449 33813898952750666166064087)
      ·
        refine ⟨50720848429125999249096131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33813898952750666166064087 50720848429125999249096131)
        ·
          refine ⟨76081272643688998873644197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50720848429125999249096131 76081272643688998873644197)
          ·
            refine ⟨14265238620691687288808287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76081272643688998873644197 14265238620691687288808287)
            ·
              refine ⟨21397857931037530933212431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14265238620691687288808287 21397857931037530933212431)
              ·
                refine ⟨32096786896556296399818647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21397857931037530933212431 32096786896556296399818647)
                ·
                  refine ⟨48145180344834444599727971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32096786896556296399818647 48145180344834444599727971)
                  ·
                    refine ⟨72217770517251666899591957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48145180344834444599727971 72217770517251666899591957)
                    ·
                      refine ⟨3385207992996171885918373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72217770517251666899591957 3385207992996171885918373)
                      ·
                        rfl

theorem cell23_6592669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_6592669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6592669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6592669 prefixEnd_6592669 := by exact prefixLift 6592669
  have htrace : WordTrace (prefixWord ++ tailWord_6592669) baseStart_6592669 baseEnd_6592669 := by
    simpa [prefixWord, tailWord_6592669, baseEnd_6592669] using wordTrace_append hprefix tailTrace_6592669
  have hstable : (prefixWord ++ tailWord_6592669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6592669).length < 2 ^ (prefixWord ++ tailWord_6592669).sum := by decide
  have hdescent : baseEnd_6592669 < baseStart_6592669 := by decide
  rcases family_descends (prefixWord ++ tailWord_6592669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6592673 : List Nat := [1, 2, 3, 3, 1, 2, 2, 2, 3, 2, 2]
def baseStart_6592673 : Nat := 118140960795 + 6592673 * 2 ^ 59
def prefixEnd_6592673 : Nat := 4983230072969 + 3 ^ 40 * 6592673 * 2
def baseEnd_6592673 : Nat := 3385210046918789870268355

theorem tailTrace_6592673 : CollatzResearch.WordTrace tailWord_6592673 prefixEnd_6592673 3385210046918789870268355 := by
  unfold tailWord_6592673
  simp only [CollatzResearch.WordTrace]
  refine ⟨240454538444879134752934673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160303025629919423168623115 240454538444879134752934673)
  ·
    refine ⟨180340903833659351064701005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240454538444879134752934673 180340903833659351064701005)
    ·
      refine ⟨67627838937622256649262877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180340903833659351064701005 67627838937622256649262877)
      ·
        refine ⟨25360439601608346243473579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67627838937622256649262877 25360439601608346243473579)
        ·
          refine ⟨38040659402412519365210369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25360439601608346243473579 38040659402412519365210369)
          ·
            refine ⟨28530494551809389523907777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38040659402412519365210369 28530494551809389523907777)
            ·
              refine ⟨21397870913857042142930833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28530494551809389523907777 21397870913857042142930833)
              ·
                refine ⟨16048403185392781607198125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21397870913857042142930833 16048403185392781607198125)
                ·
                  refine ⟨6018151194522293102699297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16048403185392781607198125 6018151194522293102699297)
                  ·
                    refine ⟨4513613395891719827024473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6018151194522293102699297 4513613395891719827024473)
                    ·
                      refine ⟨3385210046918789870268355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4513613395891719827024473 3385210046918789870268355)
                      ·
                        rfl

theorem cell23_6592673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 2, 3, 2, 2].length) (baseStart_6592673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6592673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6592673 prefixEnd_6592673 := by exact prefixLift 6592673
  have htrace : WordTrace (prefixWord ++ tailWord_6592673) baseStart_6592673 baseEnd_6592673 := by
    simpa [prefixWord, tailWord_6592673, baseEnd_6592673] using wordTrace_append hprefix tailTrace_6592673
  have hstable : (prefixWord ++ tailWord_6592673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6592673).length < 2 ^ (prefixWord ++ tailWord_6592673).sum := by decide
  have hdescent : baseEnd_6592673 < baseStart_6592673 := by decide
  rcases family_descends (prefixWord ++ tailWord_6592673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6592693 : List Nat := [1, 3, 3, 4, 1, 1, 2, 1, 1, 1, 5]
def baseStart_6592693 : Nat := 118140960795 + 6592693 * 2 ^ 59
def prefixEnd_6592693 : Nat := 4983230072969 + 3 ^ 40 * 6592693 * 2
def baseEnd_6592693 : Nat := 3385220316531879792018263

theorem tailTrace_6592693 : CollatzResearch.WordTrace tailWord_6592693 prefixEnd_6592693 3385220316531879792018263 := by
  unfold tailWord_6592693
  simp only [CollatzResearch.WordTrace]
  refine ⟨240455267904806678168662733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160303511936537785445775155 240455267904806678168662733)
  ·
    refine ⟨90170725464302504313248525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 240455267904806678168662733 90170725464302504313248525)
    ·
      refine ⟨33814022049113439117468197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90170725464302504313248525 33814022049113439117468197)
      ·
        refine ⟨6340129134208769834525287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33814022049113439117468197 6340129134208769834525287)
        ·
          refine ⟨9510193701313154751787931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6340129134208769834525287 9510193701313154751787931)
          ·
            refine ⟨14265290551969732127681897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9510193701313154751787931 14265290551969732127681897)
            ·
              refine ⟨10698967913977299095761423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14265290551969732127681897 10698967913977299095761423)
              ·
                refine ⟨16048451870965948643642135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10698967913977299095761423 16048451870965948643642135)
                ·
                  refine ⟨24072677806448922965463203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16048451870965948643642135 24072677806448922965463203)
                  ·
                    refine ⟨36109016709673384448194805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24072677806448922965463203 36109016709673384448194805)
                    ·
                      refine ⟨3385220316531879792018263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36109016709673384448194805 3385220316531879792018263)
                      ·
                        rfl

theorem cell23_6592693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_6592693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6592693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6592693 prefixEnd_6592693 := by exact prefixLift 6592693
  have htrace : WordTrace (prefixWord ++ tailWord_6592693) baseStart_6592693 baseEnd_6592693 := by
    simpa [prefixWord, tailWord_6592693, baseEnd_6592693] using wordTrace_append hprefix tailTrace_6592693
  have hstable : (prefixWord ++ tailWord_6592693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6592693).length < 2 ^ (prefixWord ++ tailWord_6592693).sum := by decide
  have hdescent : baseEnd_6592693 < baseStart_6592693 := by decide
  rcases family_descends (prefixWord ++ tailWord_6592693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6592766 : List Nat := [4, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3]
def baseStart_6592766 : Nat := 118140960795 + 6592766 * 2 ^ 59
def prefixEnd_6592766 : Nat := 4983230072969 + 3 ^ 40 * 6592766 * 2
def baseEnd_6592766 : Nat := 3385257800619658006405427

theorem tailTrace_6592766 : CollatzResearch.WordTrace tailWord_6592766 prefixEnd_6592766 3385257800619658006405427 := by
  unfold tailWord_6592766
  simp only [CollatzResearch.WordTrace]
  refine ⟨30057241304192776454508769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160305286955694807757380101 30057241304192776454508769)
  ·
    refine ⟨22542930978144582340881577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30057241304192776454508769 22542930978144582340881577)
    ·
      refine ⟨16907198233608436755661183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22542930978144582340881577 16907198233608436755661183)
      ·
        refine ⟨25360797350412655133491775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16907198233608436755661183 25360797350412655133491775)
        ·
          refine ⟨38041196025618982700237663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25360797350412655133491775 38041196025618982700237663)
          ·
            refine ⟨57061794038428474050356495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38041196025618982700237663 57061794038428474050356495)
            ·
              refine ⟨85592691057642711075534743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57061794038428474050356495 85592691057642711075534743)
              ·
                refine ⟨128389036586464066613302115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85592691057642711075534743 128389036586464066613302115)
                ·
                  refine ⟨192583554879696099919953173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 128389036586464066613302115 192583554879696099919953173)
                  ·
                    refine ⟨9027354134985754683747805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 192583554879696099919953173 9027354134985754683747805)
                    ·
                      refine ⟨3385257800619658006405427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9027354134985754683747805 3385257800619658006405427)
                      ·
                        rfl

theorem cell23_6592766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_6592766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6592766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6592766 prefixEnd_6592766 := by exact prefixLift 6592766
  have htrace : WordTrace (prefixWord ++ tailWord_6592766) baseStart_6592766 baseEnd_6592766 := by
    simpa [prefixWord, tailWord_6592766, baseEnd_6592766] using wordTrace_append hprefix tailTrace_6592766
  have hstable : (prefixWord ++ tailWord_6592766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6592766).length < 2 ^ (prefixWord ++ tailWord_6592766).sum := by decide
  have hdescent : baseEnd_6592766 < baseStart_6592766 := by decide
  rcases family_descends (prefixWord ++ tailWord_6592766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6592769 : List Nat := [1, 2, 4, 1, 1, 2, 2, 3, 7]
def baseStart_6592769 : Nat := 118140960795 + 6592769 * 2 ^ 59
def prefixEnd_6592769 : Nat := 4983230072969 + 3 ^ 40 * 6592769 * 2
def baseEnd_6592769 : Nat := 376139926784624610518657

theorem tailTrace_6592769 : CollatzResearch.WordTrace tailWord_6592769 prefixEnd_6592769 376139926784624610518657 := by
  unfold tailWord_6592769
  simp only [CollatzResearch.WordTrace]
  refine ⟨240458039852531343148429361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160305359901687562098952907 240458039852531343148429361)
  ·
    refine ⟨180343529889398507361322021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240458039852531343148429361 180343529889398507361322021)
    ·
      refine ⟨33814411854262220130247879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 180343529889398507361322021 33814411854262220130247879)
      ·
        refine ⟨50721617781393330195371819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33814411854262220130247879 50721617781393330195371819)
        ·
          refine ⟨76082426672089995293057729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50721617781393330195371819 76082426672089995293057729)
          ·
            refine ⟨57061820004067496469793297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76082426672089995293057729 57061820004067496469793297)
            ·
              refine ⟨42796365003050622352344973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57061820004067496469793297 42796365003050622352344973)
              ·
                refine ⟨16048636876143983382129365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42796365003050622352344973 16048636876143983382129365)
                ·
                  refine ⟨376139926784624610518657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16048636876143983382129365 376139926784624610518657)
                  ·
                    rfl

theorem cell23_6592769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 3, 7].length) (baseStart_6592769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6592769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6592769 prefixEnd_6592769 := by exact prefixLift 6592769
  have htrace : WordTrace (prefixWord ++ tailWord_6592769) baseStart_6592769 baseEnd_6592769 := by
    simpa [prefixWord, tailWord_6592769, baseEnd_6592769] using wordTrace_append hprefix tailTrace_6592769
  have hstable : (prefixWord ++ tailWord_6592769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6592769).length < 2 ^ (prefixWord ++ tailWord_6592769).sum := by decide
  have hdescent : baseEnd_6592769 < baseStart_6592769 := by decide
  rcases family_descends (prefixWord ++ tailWord_6592769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6592776 : List Nat := [2, 1, 3, 2, 3, 2, 1, 1, 2, 2, 4]
def baseStart_6592776 : Nat := 118140960795 + 6592776 * 2 ^ 59
def prefixEnd_6592776 : Nat := 4983230072969 + 3 ^ 40 * 6592776 * 2
def baseEnd_6592776 : Nat := 3385262935426202967280381

theorem tailTrace_6592776 : CollatzResearch.WordTrace tailWord_6592776 prefixEnd_6592776 3385262935426202967280381 := by
  unfold tailWord_6592776
  simp only [CollatzResearch.WordTrace]
  refine ⟨120229147581752991671967091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160305530109003988895956121 120229147581752991671967091)
  ·
    refine ⟨180343721372629487507950637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120229147581752991671967091 180343721372629487507950637)
    ·
      refine ⟨67628895514736057815481489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180343721372629487507950637 67628895514736057815481489)
      ·
        refine ⟨50721671636052043361611117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67628895514736057815481489 50721671636052043361611117)
        ·
          refine ⟨19020626863519516260604169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50721671636052043361611117 19020626863519516260604169)
          ·
            refine ⟨14265470147639637195453127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19020626863519516260604169 14265470147639637195453127)
            ·
              refine ⟨21398205221459455793179691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14265470147639637195453127 21398205221459455793179691)
              ·
                refine ⟨32097307832189183689769537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21398205221459455793179691 32097307832189183689769537)
                ·
                  refine ⟨24072980874141887767327153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32097307832189183689769537 24072980874141887767327153)
                  ·
                    refine ⟨18054735655606415825495365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24072980874141887767327153 18054735655606415825495365)
                    ·
                      refine ⟨3385262935426202967280381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18054735655606415825495365 3385262935426202967280381)
                      ·
                        rfl

theorem cell23_6592776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_6592776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6592776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6592776 prefixEnd_6592776 := by exact prefixLift 6592776
  have htrace : WordTrace (prefixWord ++ tailWord_6592776) baseStart_6592776 baseEnd_6592776 := by
    simpa [prefixWord, tailWord_6592776, baseEnd_6592776] using wordTrace_append hprefix tailTrace_6592776
  have hstable : (prefixWord ++ tailWord_6592776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6592776).length < 2 ^ (prefixWord ++ tailWord_6592776).sum := by decide
  have hdescent : baseEnd_6592776 < baseStart_6592776 := by decide
  rcases family_descends (prefixWord ++ tailWord_6592776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6592846 : List Nat := [4, 1, 1, 1, 1, 1, 2, 3, 5, 4]
def baseStart_6592846 : Nat := 118140960795 + 6592846 * 2 ^ 59
def prefixEnd_6592846 : Nat := 4983230072969 + 3 ^ 40 * 6592846 * 2
def baseEnd_6592846 : Nat := 1128432959690672564468353

theorem tailTrace_6592846 : CollatzResearch.WordTrace tailWord_6592846 prefixEnd_6592846 1128432959690672564468353 := by
  unfold tailWord_6592846
  simp only [CollatzResearch.WordTrace]
  refine ⟨30057606034156548162372799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160307232182168256865988261 30057606034156548162372799)
  ·
    refine ⟨45086409051234822243559199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30057606034156548162372799 45086409051234822243559199)
    ·
      refine ⟨67629613576852233365338799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45086409051234822243559199 67629613576852233365338799)
      ·
        refine ⟨101444420365278350048008199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67629613576852233365338799 101444420365278350048008199)
        ·
          refine ⟨152166630547917525072012299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101444420365278350048008199 152166630547917525072012299)
          ·
            refine ⟨228249945821876287608018449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152166630547917525072012299 228249945821876287608018449)
            ·
              refine ⟨171187459366407215706013837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228249945821876287608018449 171187459366407215706013837)
              ·
                refine ⟨64195297262402705889755189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 171187459366407215706013837 64195297262402705889755189)
                ·
                  refine ⟨6018309118350253677164549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64195297262402705889755189 6018309118350253677164549)
                  ·
                    refine ⟨1128432959690672564468353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6018309118350253677164549 1128432959690672564468353)
                    ·
                      rfl

theorem cell23_6592846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 5, 4].length) (baseStart_6592846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6592846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6592846 prefixEnd_6592846 := by exact prefixLift 6592846
  have htrace : WordTrace (prefixWord ++ tailWord_6592846) baseStart_6592846 baseEnd_6592846 := by
    simpa [prefixWord, tailWord_6592846, baseEnd_6592846] using wordTrace_append hprefix tailTrace_6592846
  have hstable : (prefixWord ++ tailWord_6592846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6592846).length < 2 ^ (prefixWord ++ tailWord_6592846).sum := by decide
  have hdescent : baseEnd_6592846 < baseStart_6592846 := by decide
  rcases family_descends (prefixWord ++ tailWord_6592846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6592879 : List Nat := [1, 1, 2, 1, 3, 1, 2, 3, 1, 2, 6]
def baseStart_6592879 : Nat := 118140960795 + 6592879 * 2 ^ 59
def prefixEnd_6592879 : Nat := 4983230072969 + 3 ^ 40 * 6592879 * 2
def baseEnd_6592879 : Nat := 3385315823933616064292407

theorem tailTrace_6592879 : CollatzResearch.WordTrace tailWord_6592879 prefixEnd_6592879 3385315823933616064292407 := by
  unfold tailWord_6592879
  simp only [CollatzResearch.WordTrace]
  refine ⟨240462051882132831934933691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160308034588088554623289127 240462051882132831934933691)
  ·
    refine ⟨360693077823199247902400537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240462051882132831934933691 360693077823199247902400537)
    ·
      refine ⟨270519808367399435926800403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 360693077823199247902400537 270519808367399435926800403)
      ·
        refine ⟨405779712551099153890200605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270519808367399435926800403 405779712551099153890200605)
        ·
          refine ⟨152167392206662182708825227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 405779712551099153890200605 152167392206662182708825227)
          ·
            refine ⟨228251088309993274063237841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152167392206662182708825227 228251088309993274063237841)
            ·
              refine ⟨171188316232494955547428381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228251088309993274063237841 171188316232494955547428381)
              ·
                refine ⟨64195618587185608330285643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 171188316232494955547428381 64195618587185608330285643)
                ·
                  refine ⟨96293427880778412495428465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64195618587185608330285643 96293427880778412495428465)
                  ·
                    refine ⟨72220070910583809371571349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 96293427880778412495428465 72220070910583809371571349)
                    ·
                      refine ⟨3385315823933616064292407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72220070910583809371571349 3385315823933616064292407)
                      ·
                        rfl

theorem cell23_6592879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 2, 6].length) (baseStart_6592879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6592879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6592879 prefixEnd_6592879 := by exact prefixLift 6592879
  have htrace : WordTrace (prefixWord ++ tailWord_6592879) baseStart_6592879 baseEnd_6592879 := by
    simpa [prefixWord, tailWord_6592879, baseEnd_6592879] using wordTrace_append hprefix tailTrace_6592879
  have hstable : (prefixWord ++ tailWord_6592879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6592879).length < 2 ^ (prefixWord ++ tailWord_6592879).sum := by decide
  have hdescent : baseEnd_6592879 < baseStart_6592879 := by decide
  rcases family_descends (prefixWord ++ tailWord_6592879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6592889 : List Nat := [1, 2, 1, 3, 2, 1, 1, 1, 2, 9]
def baseStart_6592889 : Nat := 118140960795 + 6592889 * 2 ^ 59
def prefixEnd_6592889 : Nat := 4983230072969 + 3 ^ 40 * 6592889 * 2
def baseEnd_6592889 : Nat := 1128440319580053675055787

theorem tailTrace_6592889 : CollatzResearch.WordTrace tailWord_6592889 prefixEnd_6592889 1128440319580053675055787 := by
  unfold tailWord_6592889
  simp only [CollatzResearch.WordTrace]
  refine ⟨240462416612096603642797721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160308277741397735761865147 240462416612096603642797721)
  ·
    refine ⟨180346812459072452732098291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240462416612096603642797721 180346812459072452732098291)
    ·
      refine ⟨270520218688608679098147437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180346812459072452732098291 270520218688608679098147437)
      ·
        refine ⟨101445082008228254661805289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 270520218688608679098147437 101445082008228254661805289)
        ·
          refine ⟨76083811506171190996353967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101445082008228254661805289 76083811506171190996353967)
          ·
            refine ⟨114125717259256786494530951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76083811506171190996353967 114125717259256786494530951)
            ·
              refine ⟨171188575888885179741796427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114125717259256786494530951 171188575888885179741796427)
              ·
                refine ⟨256782863833327769612694641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171188575888885179741796427 256782863833327769612694641)
                ·
                  refine ⟨192587147874995827209520981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 256782863833327769612694641 192587147874995827209520981)
                  ·
                    refine ⟨1128440319580053675055787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 192587147874995827209520981 1128440319580053675055787)
                    ·
                      rfl

theorem cell23_6592889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 9].length) (baseStart_6592889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6592889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6592889 prefixEnd_6592889 := by exact prefixLift 6592889
  have htrace : WordTrace (prefixWord ++ tailWord_6592889) baseStart_6592889 baseEnd_6592889 := by
    simpa [prefixWord, tailWord_6592889, baseEnd_6592889] using wordTrace_append hprefix tailTrace_6592889
  have hstable : (prefixWord ++ tailWord_6592889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6592889).length < 2 ^ (prefixWord ++ tailWord_6592889).sum := by decide
  have hdescent : baseEnd_6592889 < baseStart_6592889 := by decide
  rcases family_descends (prefixWord ++ tailWord_6592889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6592893 : List Nat := [1, 4, 1, 1, 2, 3, 4, 1, 6]
def baseStart_6592893 : Nat := 118140960795 + 6592893 * 2 ^ 59
def prefixEnd_6592893 : Nat := 4983230072969 + 3 ^ 40 * 6592893 * 2
def baseEnd_6592893 : Nat := 376147001406975445501927

theorem tailTrace_6592893 : CollatzResearch.WordTrace tailWord_6592893 prefixEnd_6592893 376147001406975445501927 := by
  unfold tailWord_6592893
  simp only [CollatzResearch.WordTrace]
  refine ⟨240462562504082112325943333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160308375002721408217295555 240462562504082112325943333)
  ·
    refine ⟨45086730469515396061114375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 240462562504082112325943333 45086730469515396061114375)
    ·
      refine ⟨67630095704273094091671563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45086730469515396061114375 67630095704273094091671563)
      ·
        refine ⟨101445143556409641137507345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67630095704273094091671563 101445143556409641137507345)
        ·
          refine ⟨76083857667307230853130509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101445143556409641137507345 76083857667307230853130509)
          ·
            refine ⟨28531446625240211569923941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76083857667307230853130509 28531446625240211569923941)
            ·
              refine ⟨5349646242232539669360739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28531446625240211569923941 5349646242232539669360739)
              ·
                refine ⟨8024469363348809504041109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5349646242232539669360739 8024469363348809504041109)
                ·
                  refine ⟨376147001406975445501927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8024469363348809504041109 376147001406975445501927)
                  ·
                    rfl

theorem cell23_6592893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 4, 1, 6].length) (baseStart_6592893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6592893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6592893 prefixEnd_6592893 := by exact prefixLift 6592893
  have htrace : WordTrace (prefixWord ++ tailWord_6592893) baseStart_6592893 baseEnd_6592893 := by
    simpa [prefixWord, tailWord_6592893, baseEnd_6592893] using wordTrace_append hprefix tailTrace_6592893
  have hstable : (prefixWord ++ tailWord_6592893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6592893).length < 2 ^ (prefixWord ++ tailWord_6592893).sum := by decide
  have hdescent : baseEnd_6592893 < baseStart_6592893 := by decide
  rcases family_descends (prefixWord ++ tailWord_6592893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6592903 : List Nat := [1, 1, 4, 2, 2, 1, 2, 1, 5, 1, 3]
def baseStart_6592903 : Nat := 118140960795 + 6592903 * 2 ^ 59
def prefixEnd_6592903 : Nat := 4983230072969 + 3 ^ 40 * 6592903 * 2
def baseEnd_6592903 : Nat := 3385328147469323970392297

theorem tailTrace_6592903 : CollatzResearch.WordTrace tailWord_6592903 prefixEnd_6592903 3385328147469323970392297 := by
  unfold tailWord_6592903
  simp only [CollatzResearch.WordTrace]
  refine ⟨240462927234045884033807363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160308618156030589355871575 240462927234045884033807363)
  ·
    refine ⟨360694390851068826050711045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240462927234045884033807363 360694390851068826050711045)
    ·
      refine ⟨67630198284575404884508321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 360694390851068826050711045 67630198284575404884508321)
      ·
        refine ⟨50722648713431553663381241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67630198284575404884508321 50722648713431553663381241)
        ·
          refine ⟨38041986535073665247535931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50722648713431553663381241 38041986535073665247535931)
          ·
            refine ⟨57062979802610497871303897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38041986535073665247535931 57062979802610497871303897)
            ·
              refine ⟨42797234851957873403477923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57062979802610497871303897 42797234851957873403477923)
              ·
                refine ⟨64195852277936810105216885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42797234851957873403477923 64195852277936810105216885)
                ·
                  refine ⟨6018361151056575947364083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64195852277936810105216885 6018361151056575947364083)
                  ·
                    refine ⟨9027541726584863921046125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6018361151056575947364083 9027541726584863921046125)
                    ·
                      refine ⟨3385328147469323970392297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9027541726584863921046125 3385328147469323970392297)
                      ·
                        rfl

theorem cell23_6592903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 5, 1, 3].length) (baseStart_6592903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6592903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6592903 prefixEnd_6592903 := by exact prefixLift 6592903
  have htrace : WordTrace (prefixWord ++ tailWord_6592903) baseStart_6592903 baseEnd_6592903 := by
    simpa [prefixWord, tailWord_6592903, baseEnd_6592903] using wordTrace_append hprefix tailTrace_6592903
  have hstable : (prefixWord ++ tailWord_6592903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6592903).length < 2 ^ (prefixWord ++ tailWord_6592903).sum := by decide
  have hdescent : baseEnd_6592903 < baseStart_6592903 := by decide
  rcases family_descends (prefixWord ++ tailWord_6592903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6592930 : List Nat := [3, 3, 1, 2, 1, 1, 1, 4, 2, 3, 2]
def baseStart_6592930 : Nat := 118140960795 + 6592930 * 2 ^ 59
def prefixEnd_6592930 : Nat := 4983230072969 + 3 ^ 40 * 6592930 * 2
def baseEnd_6592930 : Nat := 3385342011446995364754673

theorem tailTrace_6592930 : CollatzResearch.WordTrace tailWord_6592930 prefixEnd_6592930 3385342011446995364754673 := by
  unfold tailWord_6592930
  simp only [CollatzResearch.WordTrace]
  refine ⟨60115978001237016911260061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160309274669965378430026829 60115978001237016911260061)
  ·
    refine ⟨22543491750463881341722523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60115978001237016911260061 22543491750463881341722523)
    ·
      refine ⟨33815237625695822012583785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22543491750463881341722523 33815237625695822012583785)
      ·
        refine ⟨25361428219271866509437839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33815237625695822012583785 25361428219271866509437839)
        ·
          refine ⟨38042142328907799764156759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25361428219271866509437839 38042142328907799764156759)
          ·
            refine ⟨57063213493361699646235139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38042142328907799764156759 57063213493361699646235139)
            ·
              refine ⟨85594820240042549469352709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57063213493361699646235139 85594820240042549469352709)
              ·
                refine ⟨16049028795007978025503633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85594820240042549469352709 16049028795007978025503633)
                ·
                  refine ⟨12036771596255983519127725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16049028795007978025503633 12036771596255983519127725)
                  ·
                    refine ⟨4513789348595993819672897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12036771596255983519127725 4513789348595993819672897)
                    ·
                      refine ⟨3385342011446995364754673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4513789348595993819672897 3385342011446995364754673)
                      ·
                        rfl

theorem cell23_6592930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 4, 2, 3, 2].length) (baseStart_6592930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6592930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6592930 prefixEnd_6592930 := by exact prefixLift 6592930
  have htrace : WordTrace (prefixWord ++ tailWord_6592930) baseStart_6592930 baseEnd_6592930 := by
    simpa [prefixWord, tailWord_6592930, baseEnd_6592930] using wordTrace_append hprefix tailTrace_6592930
  have hstable : (prefixWord ++ tailWord_6592930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6592930).length < 2 ^ (prefixWord ++ tailWord_6592930).sum := by decide
  have hdescent : baseEnd_6592930 < baseStart_6592930 := by decide
  rcases family_descends (prefixWord ++ tailWord_6592930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6592946 : List Nat := [3, 2, 1, 1, 1, 1, 4, 1, 3, 1, 5]
def baseStart_6592946 : Nat := 118140960795 + 6592946 * 2 ^ 59
def prefixEnd_6592946 : Nat := 4983230072969 + 3 ^ 40 * 6592946 * 2
def baseEnd_6592946 : Nat := 3385350227137467302154599

theorem tailTrace_6592946 : CollatzResearch.WordTrace tailWord_6592946 prefixEnd_6592946 3385350227137467302154599 := by
  unfold tailWord_6592946
  simp only [CollatzResearch.WordTrace]
  refine ⟨60116123893222525594405673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160309663715260068251748461 60116123893222525594405673)
  ·
    refine ⟨45087092919916894195804255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60116123893222525594405673 45087092919916894195804255)
    ·
      refine ⟨67630639379875341293706383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45087092919916894195804255 67630639379875341293706383)
      ·
        refine ⟨101445959069813011940559575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67630639379875341293706383 101445959069813011940559575)
        ·
          refine ⟨152168938604719517910839363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101445959069813011940559575 152168938604719517910839363)
          ·
            refine ⟨228253407907079276866259045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152168938604719517910839363 228253407907079276866259045)
            ·
              refine ⟨42797513982577364412423571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 228253407907079276866259045 42797513982577364412423571)
              ·
                refine ⟨64196270973866046618635357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42797513982577364412423571 64196270973866046618635357)
                ·
                  refine ⟨24073601615199767481988259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64196270973866046618635357 24073601615199767481988259)
                  ·
                    refine ⟨36110402422799651222982389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24073601615199767481988259 36110402422799651222982389)
                    ·
                      refine ⟨3385350227137467302154599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36110402422799651222982389 3385350227137467302154599)
                      ·
                        rfl

theorem cell23_6592946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 1, 3, 1, 5].length) (baseStart_6592946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6592946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6592946 prefixEnd_6592946 := by exact prefixLift 6592946
  have htrace : WordTrace (prefixWord ++ tailWord_6592946) baseStart_6592946 baseEnd_6592946 := by
    simpa [prefixWord, tailWord_6592946, baseEnd_6592946] using wordTrace_append hprefix tailTrace_6592946
  have hstable : (prefixWord ++ tailWord_6592946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6592946).length < 2 ^ (prefixWord ++ tailWord_6592946).sum := by decide
  have hdescent : baseEnd_6592946 < baseStart_6592946 := by decide
  rcases family_descends (prefixWord ++ tailWord_6592946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6592953 : List Nat := [1, 2, 1, 4, 3, 2, 2, 1, 1, 6]
def baseStart_6592953 : Nat := 118140960795 + 6592953 * 2 ^ 59
def prefixEnd_6592953 : Nat := 4983230072969 + 3 ^ 40 * 6592953 * 2
def baseEnd_6592953 : Nat := 1128451273834016258255689

theorem tailTrace_6592953 : CollatzResearch.WordTrace tailWord_6592953 prefixEnd_6592953 1128451273834016258255689 := by
  unfold tailWord_6592953
  simp only [CollatzResearch.WordTrace]
  refine ⟨240464750883864742573127513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160309833922576495048751675 240464750883864742573127513)
  ·
    refine ⟨180348563162898556929845635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240464750883864742573127513 180348563162898556929845635)
    ·
      refine ⟨270522844744347835394768453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180348563162898556929845635 270522844744347835394768453)
      ·
        refine ⟨50723033389565219136519085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 270522844744347835394768453 50723033389565219136519085)
        ·
          refine ⟨19021137521086957176194657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50723033389565219136519085 19021137521086957176194657)
          ·
            refine ⟨14265853140815217882145993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19021137521086957176194657 14265853140815217882145993)
            ·
              refine ⟨10699389855611413411609495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14265853140815217882145993 10699389855611413411609495)
              ·
                refine ⟨16049084783417120117414243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10699389855611413411609495 16049084783417120117414243)
                ·
                  refine ⟨24073627175125680176121365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16049084783417120117414243 24073627175125680176121365)
                  ·
                    refine ⟨1128451273834016258255689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24073627175125680176121365 1128451273834016258255689)
                    ·
                      rfl

theorem cell23_6592953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 1, 1, 6].length) (baseStart_6592953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6592953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6592953 prefixEnd_6592953 := by exact prefixLift 6592953
  have htrace : WordTrace (prefixWord ++ tailWord_6592953) baseStart_6592953 baseEnd_6592953 := by
    simpa [prefixWord, tailWord_6592953, baseEnd_6592953] using wordTrace_append hprefix tailTrace_6592953
  have hstable : (prefixWord ++ tailWord_6592953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6592953).length < 2 ^ (prefixWord ++ tailWord_6592953).sum := by decide
  have hdescent : baseEnd_6592953 < baseStart_6592953 := by decide
  rcases family_descends (prefixWord ++ tailWord_6592953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6592963 : List Nat := [1, 1, 1, 3, 1, 1, 3, 6, 1, 2, 3]
def baseStart_6592963 : Nat := 118140960795 + 6592963 * 2 ^ 59
def prefixEnd_6592963 : Nat := 4983230072969 + 3 ^ 40 * 6592963 * 2
def baseEnd_6592963 : Nat := 3385358956308593735642021

theorem tailTrace_6592963 : CollatzResearch.WordTrace tailWord_6592963 prefixEnd_6592963 3385358956308593735642021 := by
  unfold tailWord_6592963
  simp only [CollatzResearch.WordTrace]
  refine ⟨240465115613828514280991543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160310077075885676187327695 240465115613828514280991543)
  ·
    refine ⟨360697673420742771421487315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240465115613828514280991543 360697673420742771421487315)
    ·
      refine ⟨541046510131114157132230973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360697673420742771421487315 541046510131114157132230973)
      ·
        refine ⟨202892441299167808924586615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 541046510131114157132230973 202892441299167808924586615)
        ·
          refine ⟨304338661948751713386879923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202892441299167808924586615 304338661948751713386879923)
          ·
            refine ⟨456507992923127570080319885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 304338661948751713386879923 456507992923127570080319885)
            ·
              refine ⟨171190497346172838780119957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 456507992923127570080319885 171190497346172838780119957)
              ·
                refine ⟨8024554563101851817818123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 171190497346172838780119957 8024554563101851817818123)
                ·
                  refine ⟨12036831844652777726727185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8024554563101851817818123 12036831844652777726727185)
                  ·
                    refine ⟨9027623883489583295045389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12036831844652777726727185 9027623883489583295045389)
                    ·
                      refine ⟨3385358956308593735642021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9027623883489583295045389 3385358956308593735642021)
                      ·
                        rfl

theorem cell23_6592963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 6, 1, 2, 3].length) (baseStart_6592963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6592963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6592963 prefixEnd_6592963 := by exact prefixLift 6592963
  have htrace : WordTrace (prefixWord ++ tailWord_6592963) baseStart_6592963 baseEnd_6592963 := by
    simpa [prefixWord, tailWord_6592963, baseEnd_6592963] using wordTrace_append hprefix tailTrace_6592963
  have hstable : (prefixWord ++ tailWord_6592963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6592963).length < 2 ^ (prefixWord ++ tailWord_6592963).sum := by decide
  have hdescent : baseEnd_6592963 < baseStart_6592963 := by decide
  rcases family_descends (prefixWord ++ tailWord_6592963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6592964 : List Nat := [2, 3, 3, 2, 2, 2, 1, 1, 2, 3, 2]
def baseStart_6592964 : Nat := 118140960795 + 6592964 * 2 ^ 59
def prefixEnd_6592964 : Nat := 4983230072969 + 3 ^ 40 * 6592964 * 2
def baseEnd_6592964 : Nat := 3385359469789248231729517

theorem tailTrace_6592964 : CollatzResearch.WordTrace tailWord_6592964 prefixEnd_6592964 3385359469789248231729517 := by
  unfold tailWord_6592964
  simp only [CollatzResearch.WordTrace]
  refine ⟨120232576043412445725888973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160310101391216594301185297 120232576043412445725888973)
  ·
    refine ⟨45087216016279667147208365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120232576043412445725888973 45087216016279667147208365)
    ·
      refine ⟨16907706006104875180203137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45087216016279667147208365 16907706006104875180203137)
      ·
        refine ⟨12680779504578656385152353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16907706006104875180203137 12680779504578656385152353)
        ·
          refine ⟨9510584628433992288864265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12680779504578656385152353 9510584628433992288864265)
          ·
            refine ⟨7132938471325494216648199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9510584628433992288864265 7132938471325494216648199)
            ·
              refine ⟨10699407706988241324972299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7132938471325494216648199 10699407706988241324972299)
              ·
                refine ⟨16049111560482361987458449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10699407706988241324972299 16049111560482361987458449)
                ·
                  refine ⟨12036833670361771490593837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16049111560482361987458449 12036833670361771490593837)
                  ·
                    refine ⟨4513812626385664308972689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12036833670361771490593837 4513812626385664308972689)
                    ·
                      refine ⟨3385359469789248231729517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4513812626385664308972689 3385359469789248231729517)
                      ·
                        rfl

theorem cell23_6592964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_6592964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6592964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6592964 prefixEnd_6592964 := by exact prefixLift 6592964
  have htrace : WordTrace (prefixWord ++ tailWord_6592964) baseStart_6592964 baseEnd_6592964 := by
    simpa [prefixWord, tailWord_6592964, baseEnd_6592964] using wordTrace_append hprefix tailTrace_6592964
  have hstable : (prefixWord ++ tailWord_6592964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6592964).length < 2 ^ (prefixWord ++ tailWord_6592964).sum := by decide
  have hdescent : baseEnd_6592964 < baseStart_6592964 := by decide
  rcases family_descends (prefixWord ++ tailWord_6592964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6593101 : List Nat := [1, 6, 1, 1, 2, 2, 2, 2, 2, 2, 2]
def baseStart_6593101 : Nat := 118140960795 + 6593101 * 2 ^ 59
def prefixEnd_6593101 : Nat := 4983230072969 + 3 ^ 40 * 6593101 * 2
def baseEnd_6593101 : Nat := 3385429816638914195716387

theorem tailTrace_6593101 : CollatzResearch.WordTrace tailWord_6593101 prefixEnd_6593101 3385429816638914195716387 := by
  unfold tailWord_6593101
  simp only [CollatzResearch.WordTrace]
  refine ⟨240470148887328563849515157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160313432591552375899676771 240470148887328563849515157)
  ·
    refine ⟨11272038229093526430446023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 240470148887328563849515157 11272038229093526430446023)
    ·
      refine ⟨16908057343640289645669035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11272038229093526430446023 16908057343640289645669035)
      ·
        refine ⟨25362086015460434468503553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16908057343640289645669035 25362086015460434468503553)
        ·
          refine ⟨19021564511595325851377665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25362086015460434468503553 19021564511595325851377665)
          ·
            refine ⟨14266173383696494388533249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19021564511595325851377665 14266173383696494388533249)
            ·
              refine ⟨10699630037772370791399937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14266173383696494388533249 10699630037772370791399937)
              ·
                refine ⟨8024722528329278093549953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10699630037772370791399937 8024722528329278093549953)
                ·
                  refine ⟨6018541896246958570162465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8024722528329278093549953 6018541896246958570162465)
                  ·
                    refine ⟨4513906422185218927621849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6018541896246958570162465 4513906422185218927621849)
                    ·
                      refine ⟨3385429816638914195716387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4513906422185218927621849 3385429816638914195716387)
                      ·
                        rfl

theorem cell23_6593101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 2, 2, 2, 2].length) (baseStart_6593101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6593101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6593101 prefixEnd_6593101 := by exact prefixLift 6593101
  have htrace : WordTrace (prefixWord ++ tailWord_6593101) baseStart_6593101 baseEnd_6593101 := by
    simpa [prefixWord, tailWord_6593101, baseEnd_6593101] using wordTrace_append hprefix tailTrace_6593101
  have hstable : (prefixWord ++ tailWord_6593101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6593101).length < 2 ^ (prefixWord ++ tailWord_6593101).sum := by decide
  have hdescent : baseEnd_6593101 < baseStart_6593101 := by decide
  rcases family_descends (prefixWord ++ tailWord_6593101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6593103 : List Nat := [1, 1, 2, 1, 1, 2, 6, 2, 2, 5]
def baseStart_6593103 : Nat := 118140960795 + 6593103 * 2 ^ 59
def prefixEnd_6593103 : Nat := 4983230072969 + 3 ^ 40 * 6593103 * 2
def baseEnd_6593103 : Nat := 1128476947866741062630459

theorem tailTrace_6593103 : CollatzResearch.WordTrace tailWord_6593103 prefixEnd_6593103 1128476947866741062630459 := by
  unfold tailWord_6593103
  simp only [CollatzResearch.WordTrace]
  refine ⟨240470221833321318191087963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160313481222214212127391975 240470221833321318191087963)
  ·
    refine ⟨360705332749981977286631945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240470221833321318191087963 360705332749981977286631945)
    ·
      refine ⟨270528999562486482964973959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 360705332749981977286631945 270528999562486482964973959)
      ·
        refine ⟨405793499343729724447460939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270528999562486482964973959 405793499343729724447460939)
        ·
          refine ⟨608690249015594586671191409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 405793499343729724447460939 608690249015594586671191409)
          ·
            refine ⟨456517686761695940003393557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 608690249015594586671191409 456517686761695940003393557)
            ·
              refine ⟨21399266566954497187659073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 456517686761695940003393557 21399266566954497187659073)
              ·
                refine ⟨16049449925215872890744305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21399266566954497187659073 16049449925215872890744305)
                ·
                  refine ⟨12037087443911904668058229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16049449925215872890744305 12037087443911904668058229)
                  ·
                    refine ⟨1128476947866741062630459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12037087443911904668058229 1128476947866741062630459)
                    ·
                      rfl

theorem cell23_6593103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 2, 2, 5].length) (baseStart_6593103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6593103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6593103 prefixEnd_6593103 := by exact prefixLift 6593103
  have htrace : WordTrace (prefixWord ++ tailWord_6593103) baseStart_6593103 baseEnd_6593103 := by
    simpa [prefixWord, tailWord_6593103, baseEnd_6593103] using wordTrace_append hprefix tailTrace_6593103
  have hstable : (prefixWord ++ tailWord_6593103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6593103).length < 2 ^ (prefixWord ++ tailWord_6593103).sum := by decide
  have hdescent : baseEnd_6593103 < baseStart_6593103 := by decide
  rcases family_descends (prefixWord ++ tailWord_6593103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6593118 : List Nat := [4, 4, 1, 2, 1, 1, 2, 1, 1, 4, 2]
def baseStart_6593118 : Nat := 118140960795 + 6593118 * 2 ^ 59
def prefixEnd_6593118 : Nat := 4983230072969 + 3 ^ 40 * 6593118 * 2
def baseEnd_6593118 : Nat := 3385438545810040629203809

theorem tailTrace_6593118 : CollatzResearch.WordTrace tailWord_6593118 prefixEnd_6593118 3385438545810040629203809 := by
  unfold tailWord_6593118
  simp only [CollatzResearch.WordTrace]
  refine ⟨30058846116033371969110501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160313845952177983835256005 30058846116033371969110501)
  ·
    refine ⟨5636033646756257244208219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30058846116033371969110501 5636033646756257244208219)
    ·
      refine ⟨8454050470134385866312329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5636033646756257244208219 8454050470134385866312329)
      ·
        refine ⟨6340537852600789399734247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8454050470134385866312329 6340537852600789399734247)
        ·
          refine ⟨9510806778901184099601371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6340537852600789399734247 9510806778901184099601371)
          ·
            refine ⟨14266210168351776149402057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9510806778901184099601371 14266210168351776149402057)
            ·
              refine ⟨10699657626263832112051543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14266210168351776149402057 10699657626263832112051543)
              ·
                refine ⟨16049486439395748168077315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10699657626263832112051543 16049486439395748168077315)
                ·
                  refine ⟨24074229659093622252115973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16049486439395748168077315 24074229659093622252115973)
                  ·
                    refine ⟨4513918061080054172271745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24074229659093622252115973 4513918061080054172271745)
                    ·
                      refine ⟨3385438545810040629203809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4513918061080054172271745 3385438545810040629203809)
                      ·
                        rfl

theorem cell23_6593118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_6593118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6593118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6593118 prefixEnd_6593118 := by exact prefixLift 6593118
  have htrace : WordTrace (prefixWord ++ tailWord_6593118) baseStart_6593118 baseEnd_6593118 := by
    simpa [prefixWord, tailWord_6593118, baseEnd_6593118] using wordTrace_append hprefix tailTrace_6593118
  have hstable : (prefixWord ++ tailWord_6593118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6593118).length < 2 ^ (prefixWord ++ tailWord_6593118).sum := by decide
  have hdescent : baseEnd_6593118 < baseStart_6593118 := by decide
  rcases family_descends (prefixWord ++ tailWord_6593118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6593123 : List Nat := [1, 1, 1, 5, 1, 2, 2, 2, 1, 3, 4]
def baseStart_6593123 : Nat := 118140960795 + 6593123 * 2 ^ 59
def prefixEnd_6593123 : Nat := 4983230072969 + 3 ^ 40 * 6593123 * 2
def baseEnd_6593123 : Nat := 3385441113213313109641285

theorem tailTrace_6593123 : CollatzResearch.WordTrace tailWord_6593123 prefixEnd_6593123 3385441113213313109641285 := by
  unfold tailWord_6593123
  simp only [CollatzResearch.WordTrace]
  refine ⟨240470951293248861606816023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160313967528832574404544015 240470951293248861606816023)
  ·
    refine ⟨360706426939873292410224035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240470951293248861606816023 360706426939873292410224035)
    ·
      refine ⟨541059640409809938615336053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360706426939873292410224035 541059640409809938615336053)
      ·
        refine ⟨50724341288419681745187755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 541059640409809938615336053 50724341288419681745187755)
        ·
          refine ⟨76086511932629522617781633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50724341288419681745187755 76086511932629522617781633)
          ·
            refine ⟨57064883949472141963336225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76086511932629522617781633 57064883949472141963336225)
            ·
              refine ⟨42798662962104106472502169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57064883949472141963336225 42798662962104106472502169)
              ·
                refine ⟨32098997221578079854376627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42798662962104106472502169 32098997221578079854376627)
                ·
                  refine ⟨48148495832367119781564941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32098997221578079854376627 48148495832367119781564941)
                  ·
                    refine ⟨18055685937137669918086853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48148495832367119781564941 18055685937137669918086853)
                    ·
                      refine ⟨3385441113213313109641285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18055685937137669918086853 3385441113213313109641285)
                      ·
                        rfl

theorem cell23_6593123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_6593123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6593123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6593123 prefixEnd_6593123 := by exact prefixLift 6593123
  have htrace : WordTrace (prefixWord ++ tailWord_6593123) baseStart_6593123 baseEnd_6593123 := by
    simpa [prefixWord, tailWord_6593123, baseEnd_6593123] using wordTrace_append hprefix tailTrace_6593123
  have hstable : (prefixWord ++ tailWord_6593123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6593123).length < 2 ^ (prefixWord ++ tailWord_6593123).sum := by decide
  have hdescent : baseEnd_6593123 < baseStart_6593123 := by decide
  rcases family_descends (prefixWord ++ tailWord_6593123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6593153 : List Nat := [1, 2, 4, 2, 1, 1, 1, 1, 1, 3, 6]
def baseStart_6593153 : Nat := 118140960795 + 6593153 * 2 ^ 59
def prefixEnd_6593153 : Nat := 4983230072969 + 3 ^ 40 * 6593153 * 2
def baseEnd_6593153 : Nat := 3385456517632947992266147

theorem tailTrace_6593153 : CollatzResearch.WordTrace tailWord_6593153 prefixEnd_6593153 3385456517632947992266147 := by
  unfold tailWord_6593153
  simp only [CollatzResearch.WordTrace]
  refine ⟨240472045483140176730408113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160314696988760117820272075 240472045483140176730408113)
  ·
    refine ⟨180354034112355132547806085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240472045483140176730408113 180354034112355132547806085)
    ·
      refine ⟨33816381396066587352713641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 180354034112355132547806085 33816381396066587352713641)
      ·
        refine ⟨25362286047049940514535231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33816381396066587352713641 25362286047049940514535231)
        ·
          refine ⟨38043429070574910771802847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25362286047049940514535231 38043429070574910771802847)
          ·
            refine ⟨57065143605862366157704271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38043429070574910771802847 57065143605862366157704271)
            ·
              refine ⟨85597715408793549236556407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57065143605862366157704271 85597715408793549236556407)
              ·
                refine ⟨128396573113190323854834611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85597715408793549236556407 128396573113190323854834611)
                ·
                  refine ⟨192594859669785485782251917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 128396573113190323854834611 192594859669785485782251917)
                  ·
                    refine ⟨72223072376169557168344469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 192594859669785485782251917 72223072376169557168344469)
                    ·
                      refine ⟨3385456517632947992266147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72223072376169557168344469 3385456517632947992266147)
                      ·
                        rfl

theorem cell23_6593153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_6593153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6593153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6593153 prefixEnd_6593153 := by exact prefixLift 6593153
  have htrace : WordTrace (prefixWord ++ tailWord_6593153) baseStart_6593153 baseEnd_6593153 := by
    simpa [prefixWord, tailWord_6593153, baseEnd_6593153] using wordTrace_append hprefix tailTrace_6593153
  have hstable : (prefixWord ++ tailWord_6593153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6593153).length < 2 ^ (prefixWord ++ tailWord_6593153).sum := by decide
  have hdescent : baseEnd_6593153 < baseStart_6593153 := by decide
  rcases family_descends (prefixWord ++ tailWord_6593153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6593163 : List Nat := [1, 1, 1, 1, 4, 1, 2, 6, 6]
def baseStart_6593163 : Nat := 118140960795 + 6593163 * 2 ^ 59
def prefixEnd_6593163 : Nat := 4983230072969 + 3 ^ 40 * 6593163 * 2
def baseEnd_6593163 : Nat := 376162405826610328126789

theorem tailTrace_6593163 : CollatzResearch.WordTrace tailWord_6593163 prefixEnd_6593163 376162405826610328126789 := by
  unfold tailWord_6593163
  simp only [CollatzResearch.WordTrace]
  refine ⟨240472410213103948438272143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160314940142069298958848095 240472410213103948438272143)
  ·
    refine ⟨360708615319655922657408215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240472410213103948438272143 360708615319655922657408215)
    ·
      refine ⟨541062922979483883986112323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360708615319655922657408215 541062922979483883986112323)
      ·
        refine ⟨811594384469225825979168485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 541062922979483883986112323 811594384469225825979168485)
        ·
          refine ⟨152173947087979842371094091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 811594384469225825979168485 152173947087979842371094091)
          ·
            refine ⟨228260920631969763556641137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152173947087979842371094091 228260920631969763556641137)
            ·
              refine ⟨171195690473977322667480853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228260920631969763556641137 171195690473977322667480853)
              ·
                refine ⟨8024797990967687000038165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 171195690473977322667480853 8024797990967687000038165)
                ·
                  refine ⟨376162405826610328126789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8024797990967687000038165 376162405826610328126789)
                  ·
                    rfl

theorem cell23_6593163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 6, 6].length) (baseStart_6593163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6593163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6593163 prefixEnd_6593163 := by exact prefixLift 6593163
  have htrace : WordTrace (prefixWord ++ tailWord_6593163) baseStart_6593163 baseEnd_6593163 := by
    simpa [prefixWord, tailWord_6593163, baseEnd_6593163] using wordTrace_append hprefix tailTrace_6593163
  have hstable : (prefixWord ++ tailWord_6593163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6593163).length < 2 ^ (prefixWord ++ tailWord_6593163).sum := by decide
  have hdescent : baseEnd_6593163 < baseStart_6593163 := by decide
  rcases family_descends (prefixWord ++ tailWord_6593163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6593210 : List Nat := [3, 1, 1, 1, 2, 3, 1, 5, 1, 5]
def baseStart_6593210 : Nat := 118140960795 + 6593210 * 2 ^ 59
def prefixEnd_6593210 : Nat := 4983230072969 + 3 ^ 40 * 6593210 * 2
def baseEnd_6593210 : Nat := 1128495262010084756417795

theorem tailTrace_6593210 : CollatzResearch.WordTrace tailWord_6593210 prefixEnd_6593210 1128495262010084756417795 := by
  unfold tailWord_6593210
  simp only [CollatzResearch.WordTrace]
  refine ⟨60118531110983418866308271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160316082962622450310155389 60118531110983418866308271)
  ·
    refine ⟨90177796666475128299462407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60118531110983418866308271 90177796666475128299462407)
    ·
      refine ⟨135266694999712692449193611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90177796666475128299462407 135266694999712692449193611)
      ·
        refine ⟨202900042499569038673790417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135266694999712692449193611 202900042499569038673790417)
        ·
          refine ⟨152175031874676779005342813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202900042499569038673790417 152175031874676779005342813)
          ·
            refine ⟨57065636953003792127003555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 152175031874676779005342813 57065636953003792127003555)
            ·
              refine ⟨85598455429505688190505333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57065636953003792127003555 85598455429505688190505333)
              ·
                refine ⟨8024855196516158267859875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85598455429505688190505333 8024855196516158267859875)
                ·
                  refine ⟨12037282794774237401789813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8024855196516158267859875 12037282794774237401789813)
                  ·
                    refine ⟨1128495262010084756417795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12037282794774237401789813 1128495262010084756417795)
                    ·
                      rfl

theorem cell23_6593210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 5, 1, 5].length) (baseStart_6593210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6593210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6593210 prefixEnd_6593210 := by exact prefixLift 6593210
  have htrace : WordTrace (prefixWord ++ tailWord_6593210) baseStart_6593210 baseEnd_6593210 := by
    simpa [prefixWord, tailWord_6593210, baseEnd_6593210] using wordTrace_append hprefix tailTrace_6593210
  have hstable : (prefixWord ++ tailWord_6593210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6593210).length < 2 ^ (prefixWord ++ tailWord_6593210).sum := by decide
  have hdescent : baseEnd_6593210 < baseStart_6593210 := by decide
  rcases family_descends (prefixWord ++ tailWord_6593210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6593223 : List Nat := [1, 1, 4, 1, 1, 1, 2, 1, 5, 6]
def baseStart_6593223 : Nat := 118140960795 + 6593223 * 2 ^ 59
def prefixEnd_6593223 : Nat := 4983230072969 + 3 ^ 40 * 6593223 * 2
def baseEnd_6593223 : Nat := 1128497487092920906130275

theorem tailTrace_6593223 : CollatzResearch.WordTrace tailWord_6593223 prefixEnd_6593223 1128497487092920906130275 := by
  unfold tailWord_6593223
  simp only [CollatzResearch.WordTrace]
  refine ⟨240474598592886578685456323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160316399061924385790304215 240474598592886578685456323)
  ·
    refine ⟨360711897889329868028184485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240474598592886578685456323 360711897889329868028184485)
    ·
      refine ⟨67633480854249350255284591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 360711897889329868028184485 67633480854249350255284591)
      ·
        refine ⟨101450221281374025382926887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67633480854249350255284591 101450221281374025382926887)
        ·
          refine ⟨152175331922061038074390331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101450221281374025382926887 152175331922061038074390331)
          ·
            refine ⟨228262997883091557111585497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152175331922061038074390331 228262997883091557111585497)
            ·
              refine ⟨171197248412318667833689123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228262997883091557111585497 171197248412318667833689123)
              ·
                refine ⟨256795872618478001750533685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171197248412318667833689123 256795872618478001750533685)
                ·
                  refine ⟨24074613057982312664112533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 256795872618478001750533685 24074613057982312664112533)
                  ·
                    refine ⟨1128497487092920906130275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24074613057982312664112533 1128497487092920906130275)
                    ·
                      rfl

theorem cell23_6593223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 5, 6].length) (baseStart_6593223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6593223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6593223 prefixEnd_6593223 := by exact prefixLift 6593223
  have htrace : WordTrace (prefixWord ++ tailWord_6593223) baseStart_6593223 baseEnd_6593223 := by
    simpa [prefixWord, tailWord_6593223, baseEnd_6593223] using wordTrace_append hprefix tailTrace_6593223
  have hstable : (prefixWord ++ tailWord_6593223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6593223).length < 2 ^ (prefixWord ++ tailWord_6593223).sum := by decide
  have hdescent : baseEnd_6593223 < baseStart_6593223 := by decide
  rcases family_descends (prefixWord ++ tailWord_6593223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6593224 : List Nat := [2, 1, 3, 1, 2, 5, 1, 1, 3, 1, 3]
def baseStart_6593224 : Nat := 118140960795 + 6593224 * 2 ^ 59
def prefixEnd_6593224 : Nat := 4983230072969 + 3 ^ 40 * 6593224 * 2
def baseEnd_6593224 : Nat := 3385492974759417214478321

theorem tailTrace_6593224 : CollatzResearch.WordTrace tailWord_6593224 prefixEnd_6593224 3385492974759417214478321 := by
  unfold tailWord_6593224
  simp only [CollatzResearch.WordTrace]
  refine ⟨120237317532941477928121363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160316423377255303904161817 120237317532941477928121363)
  ·
    refine ⟨180355976299412216892182045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120237317532941477928121363 180355976299412216892182045)
    ·
      refine ⟨67633491112279581334568267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180355976299412216892182045 67633491112279581334568267)
      ·
        refine ⟨101450236668419372001852401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67633491112279581334568267 101450236668419372001852401)
        ·
          refine ⟨76087677501314529001389301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101450236668419372001852401 76087677501314529001389301)
          ·
            refine ⟨7133219765748237093880247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76087677501314529001389301 7133219765748237093880247)
            ·
              refine ⟨10699829648622355640820371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7133219765748237093880247 10699829648622355640820371)
              ·
                refine ⟨16049744472933533461230557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10699829648622355640820371 16049744472933533461230557)
                ·
                  refine ⟨6018654177350075047961459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16049744472933533461230557 6018654177350075047961459)
                  ·
                    refine ⟨9027981266025112571942189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6018654177350075047961459 9027981266025112571942189)
                    ·
                      refine ⟨3385492974759417214478321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9027981266025112571942189 3385492974759417214478321)
                      ·
                        rfl

theorem cell23_6593224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 1, 3, 1, 3].length) (baseStart_6593224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6593224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6593224 prefixEnd_6593224 := by exact prefixLift 6593224
  have htrace : WordTrace (prefixWord ++ tailWord_6593224) baseStart_6593224 baseEnd_6593224 := by
    simpa [prefixWord, tailWord_6593224, baseEnd_6593224] using wordTrace_append hprefix tailTrace_6593224
  have hstable : (prefixWord ++ tailWord_6593224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6593224).length < 2 ^ (prefixWord ++ tailWord_6593224).sum := by decide
  have hdescent : baseEnd_6593224 < baseStart_6593224 := by decide
  rcases family_descends (prefixWord ++ tailWord_6593224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6593244 : List Nat := [2, 2, 5, 1, 1, 1, 3, 2, 1, 5]
def baseStart_6593244 : Nat := 118140960795 + 6593244 * 2 ^ 59
def prefixEnd_6593244 : Nat := 4983230072969 + 3 ^ 40 * 6593244 * 2
def baseEnd_6593244 : Nat := 1128501081457502378742743

theorem tailTrace_6593244 : CollatzResearch.WordTrace tailWord_6593244 prefixEnd_6593244 1128501081457502378742743 := by
  unfold tailWord_6593244
  simp only [CollatzResearch.WordTrace]
  refine ⟨120237682262905249635985393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160316909683873666181313857 120237682262905249635985393)
  ·
    refine ⟨90178261697178937226989045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120237682262905249635985393 90178261697178937226989045)
    ·
      refine ⟨8454212034110525365030223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90178261697178937226989045 8454212034110525365030223)
      ·
        refine ⟨12681318051165788047545335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8454212034110525365030223 12681318051165788047545335)
        ·
          refine ⟨19021977076748682071318003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12681318051165788047545335 19021977076748682071318003)
          ·
            refine ⟨28532965615123023106977005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19021977076748682071318003 28532965615123023106977005)
            ·
              refine ⟨10699862105671133665116377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28532965615123023106977005 10699862105671133665116377)
              ·
                refine ⟨8024896579253350248837283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10699862105671133665116377 8024896579253350248837283)
                ·
                  refine ⟨12037344868880025373255925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8024896579253350248837283 12037344868880025373255925)
                  ·
                    refine ⟨1128501081457502378742743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12037344868880025373255925 1128501081457502378742743)
                    ·
                      rfl

theorem cell23_6593244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_6593244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6593244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6593244 prefixEnd_6593244 := by exact prefixLift 6593244
  have htrace : WordTrace (prefixWord ++ tailWord_6593244) baseStart_6593244 baseEnd_6593244 := by
    simpa [prefixWord, tailWord_6593244, baseEnd_6593244] using wordTrace_append hprefix tailTrace_6593244
  have hstable : (prefixWord ++ tailWord_6593244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6593244).length < 2 ^ (prefixWord ++ tailWord_6593244).sum := by decide
  have hdescent : baseEnd_6593244 < baseStart_6593244 := by decide
  rcases family_descends (prefixWord ++ tailWord_6593244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6593247 : List Nat := [1, 1, 2, 3, 2, 3, 3, 2, 1, 1, 4]
def baseStart_6593247 : Nat := 118140960795 + 6593247 * 2 ^ 59
def prefixEnd_6593247 : Nat := 4983230072969 + 3 ^ 40 * 6593247 * 2
def baseEnd_6593247 : Nat := 3385504784814470624490715

theorem tailTrace_6593247 : CollatzResearch.WordTrace tailWord_6593247 prefixEnd_6593247 3385504784814470624490715 := by
  unfold tailWord_6593247
  simp only [CollatzResearch.WordTrace]
  refine ⟨240475473944799630784329995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160316982629866420522886663 240475473944799630784329995)
  ·
    refine ⟨360713210917199446176494993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240475473944799630784329995 360713210917199446176494993)
    ·
      refine ⟨270534908187899584632371245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 360713210917199446176494993 270534908187899584632371245)
      ·
        refine ⟨101450590570462344237139217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 270534908187899584632371245 101450590570462344237139217)
        ·
          refine ⟨76087942927846758177854413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101450590570462344237139217 76087942927846758177854413)
          ·
            refine ⟨28532978597942534316695405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76087942927846758177854413 28532978597942534316695405)
            ·
              refine ⟨10699866974228450368760777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28532978597942534316695405 10699866974228450368760777)
              ·
                refine ⟨8024900230671337776570583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10699866974228450368760777 8024900230671337776570583)
                ·
                  refine ⟨12037350346007006664855875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8024900230671337776570583 12037350346007006664855875)
                  ·
                    refine ⟨18056025519010509997283813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12037350346007006664855875 18056025519010509997283813)
                    ·
                      refine ⟨3385504784814470624490715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18056025519010509997283813 3385504784814470624490715)
                      ·
                        rfl

theorem cell23_6593247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 2, 1, 1, 4].length) (baseStart_6593247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6593247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6593247 prefixEnd_6593247 := by exact prefixLift 6593247
  have htrace : WordTrace (prefixWord ++ tailWord_6593247) baseStart_6593247 baseEnd_6593247 := by
    simpa [prefixWord, tailWord_6593247, baseEnd_6593247] using wordTrace_append hprefix tailTrace_6593247
  have hstable : (prefixWord ++ tailWord_6593247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6593247).length < 2 ^ (prefixWord ++ tailWord_6593247).sum := by decide
  have hdescent : baseEnd_6593247 < baseStart_6593247 := by decide
  rcases family_descends (prefixWord ++ tailWord_6593247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6593287 : List Nat := [1, 1, 4, 4, 1, 3, 1, 8]
def baseStart_6593287 : Nat := 118140960795 + 6593287 * 2 ^ 59
def prefixEnd_6593287 : Nat := 4983230072969 + 3 ^ 40 * 6593287 * 2
def baseEnd_6593287 : Nat := 125389826816320387703353

theorem tailTrace_6593287 : CollatzResearch.WordTrace tailWord_6593287 prefixEnd_6593287 125389826816320387703353 := by
  unfold tailWord_6593287
  simp only [CollatzResearch.WordTrace]
  refine ⟨240476932864654717615786115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160317955243103145077190743 240476932864654717615786115)
  ·
    refine ⟨360715399296982076423679173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240476932864654717615786115 360715399296982076423679173)
    ·
      refine ⟨67634137368184139329439845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 360715399296982076423679173 67634137368184139329439845)
      ·
        refine ⟨12681400756534526124269971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67634137368184139329439845 12681400756534526124269971)
        ·
          refine ⟨19022101134801789186404957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12681400756534526124269971 19022101134801789186404957)
          ·
            refine ⟨7133287925550670944901859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19022101134801789186404957 7133287925550670944901859)
            ·
              refine ⟨10699931888326006417352789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7133287925550670944901859 10699931888326006417352789)
              ·
                refine ⟨125389826816320387703353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10699931888326006417352789 125389826816320387703353)
                ·
                  rfl

theorem cell23_6593287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 8].length) (baseStart_6593287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6593287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6593287 prefixEnd_6593287 := by exact prefixLift 6593287
  have htrace : WordTrace (prefixWord ++ tailWord_6593287) baseStart_6593287 baseEnd_6593287 := by
    simpa [prefixWord, tailWord_6593287, baseEnd_6593287] using wordTrace_append hprefix tailTrace_6593287
  have hstable : (prefixWord ++ tailWord_6593287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6593287).length < 2 ^ (prefixWord ++ tailWord_6593287).sum := by decide
  have hdescent : baseEnd_6593287 < baseStart_6593287 := by decide
  rcases family_descends (prefixWord ++ tailWord_6593287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6593298 : List Nat := [3, 2, 4, 1, 2, 1, 1, 2, 3, 2, 2]
def baseStart_6593298 : Nat := 118140960795 + 6593298 * 2 ^ 59
def prefixEnd_6593298 : Nat := 4983230072969 + 3 ^ 40 * 6593298 * 2
def baseEnd_6593298 : Nat := 3385530972327849924952981

theorem tailTrace_6593298 : CollatzResearch.WordTrace tailWord_6593298 prefixEnd_6593298 3385530972327849924952981 := by
  unfold tailWord_6593298
  simp only [CollatzResearch.WordTrace]
  refine ⟨60119333516903716623609137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160318222711743244329624365 60119333516903716623609137)
  ·
    refine ⟨45089500137677787467706853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60119333516903716623609137 45089500137677787467706853)
    ·
      refine ⟨8454281275814585150195035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45089500137677787467706853 8454281275814585150195035)
      ·
        refine ⟨12681421913721877725292553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8454281275814585150195035 12681421913721877725292553)
        ·
          refine ⟨9511066435291408293969415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12681421913721877725292553 9511066435291408293969415)
          ·
            refine ⟨14266599652937112440954123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9511066435291408293969415 14266599652937112440954123)
            ·
              refine ⟨21399899479405668661431185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14266599652937112440954123 21399899479405668661431185)
              ·
                refine ⟨16049924609554251496073389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21399899479405668661431185 16049924609554251496073389)
                ·
                  refine ⟨6018721728582844311027521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16049924609554251496073389 6018721728582844311027521)
                  ·
                    refine ⟨4514041296437133233270641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6018721728582844311027521 4514041296437133233270641)
                    ·
                      refine ⟨3385530972327849924952981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4514041296437133233270641 3385530972327849924952981)
                      ·
                        rfl

theorem cell23_6593298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_6593298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6593298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6593298 prefixEnd_6593298 := by exact prefixLift 6593298
  have htrace : WordTrace (prefixWord ++ tailWord_6593298) baseStart_6593298 baseEnd_6593298 := by
    simpa [prefixWord, tailWord_6593298, baseEnd_6593298] using wordTrace_append hprefix tailTrace_6593298
  have hstable : (prefixWord ++ tailWord_6593298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6593298).length < 2 ^ (prefixWord ++ tailWord_6593298).sum := by decide
  have hdescent : baseEnd_6593298 < baseStart_6593298 := by decide
  rcases family_descends (prefixWord ++ tailWord_6593298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6593324 : List Nat := [2, 2, 1, 1, 1, 4, 3, 3, 1, 3, 2]
def baseStart_6593324 : Nat := 118140960795 + 6593324 * 2 ^ 59
def prefixEnd_6593324 : Nat := 4983230072969 + 3 ^ 40 * 6593324 * 2
def baseEnd_6593324 : Nat := 3385544322824866823227861

theorem tailTrace_6593324 : CollatzResearch.WordTrace tailWord_6593324 prefixEnd_6593324 3385544322824866823227861 := by
  unfold tailWord_6593324
  simp only [CollatzResearch.WordTrace]
  refine ⟨120239141182760336467441513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160318854910347115289922017 120239141182760336467441513)
  ·
    refine ⟨90179355887070252350581135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120239141182760336467441513 90179355887070252350581135)
    ·
      refine ⟨135269033830605378525871703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90179355887070252350581135 135269033830605378525871703)
      ·
        refine ⟨202903550745908067788807555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135269033830605378525871703 202903550745908067788807555)
        ·
          refine ⟨304355326118862101683211333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202903550745908067788807555 304355326118862101683211333)
          ·
            refine ⟨57066623647286644065602125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 304355326118862101683211333 57066623647286644065602125)
            ·
              refine ⟨21399983867732491524600797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57066623647286644065602125 21399983867732491524600797)
              ·
                refine ⟨8024993950399684321725299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21399983867732491524600797 8024993950399684321725299)
                ·
                  refine ⟨12037490925599526482587949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8024993950399684321725299 12037490925599526482587949)
                  ·
                    refine ⟨4514059097099822430970481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12037490925599526482587949 4514059097099822430970481)
                    ·
                      refine ⟨3385544322824866823227861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4514059097099822430970481 3385544322824866823227861)
                      ·
                        rfl

theorem cell23_6593324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 3, 2].length) (baseStart_6593324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6593324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6593324 prefixEnd_6593324 := by exact prefixLift 6593324
  have htrace : WordTrace (prefixWord ++ tailWord_6593324) baseStart_6593324 baseEnd_6593324 := by
    simpa [prefixWord, tailWord_6593324, baseEnd_6593324] using wordTrace_append hprefix tailTrace_6593324
  have hstable : (prefixWord ++ tailWord_6593324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6593324).length < 2 ^ (prefixWord ++ tailWord_6593324).sum := by decide
  have hdescent : baseEnd_6593324 < baseStart_6593324 := by decide
  rcases family_descends (prefixWord ++ tailWord_6593324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6593325 : List Nat := [1, 5, 3, 2, 2, 1, 1, 2, 2, 4]
def baseStart_6593325 : Nat := 118140960795 + 6593325 * 2 ^ 59
def prefixEnd_6593325 : Nat := 4983230072969 + 3 ^ 40 * 6593325 * 2
def baseEnd_6593325 : Nat := 1128514945435173773105119

theorem tailTrace_6593325 : CollatzResearch.WordTrace tailWord_6593325 prefixEnd_6593325 1128514945435173773105119 := by
  unfold tailWord_6593325
  simp only [CollatzResearch.WordTrace]
  refine ⟨240478318838517050105669429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160318879225678033403779619 240478318838517050105669429)
  ·
    refine ⟨22544842391110973447406509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 240478318838517050105669429 22544842391110973447406509)
    ·
      refine ⟨8454315896666615042777441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22544842391110973447406509 8454315896666615042777441)
      ·
        refine ⟨6340736922499961282083081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8454315896666615042777441 6340736922499961282083081)
        ·
          refine ⟨4755552691874970961562311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6340736922499961282083081 4755552691874970961562311)
          ·
            refine ⟨7133329037812456442343467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4755552691874970961562311 7133329037812456442343467)
            ·
              refine ⟨10699993556718684663515201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7133329037812456442343467 10699993556718684663515201)
              ·
                refine ⟨8024995167539013497636401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10699993556718684663515201 8024995167539013497636401)
                ·
                  refine ⟨6018746375654260123227301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8024995167539013497636401 6018746375654260123227301)
                  ·
                    refine ⟨1128514945435173773105119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6018746375654260123227301 1128514945435173773105119)
                    ·
                      rfl

theorem cell23_6593325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_6593325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6593325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6593325 prefixEnd_6593325 := by exact prefixLift 6593325
  have htrace : WordTrace (prefixWord ++ tailWord_6593325) baseStart_6593325 baseEnd_6593325 := by
    simpa [prefixWord, tailWord_6593325, baseEnd_6593325] using wordTrace_append hprefix tailTrace_6593325
  have hstable : (prefixWord ++ tailWord_6593325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6593325).length < 2 ^ (prefixWord ++ tailWord_6593325).sum := by decide
  have hdescent : baseEnd_6593325 < baseStart_6593325 := by decide
  rcases family_descends (prefixWord ++ tailWord_6593325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6593330 : List Nat := [3, 2, 1, 1, 3, 1, 1, 1, 4, 6]
def baseStart_6593330 : Nat := 118140960795 + 6593330 * 2 ^ 59
def prefixEnd_6593330 : Nat := 4983230072969 + 3 ^ 40 * 6593330 * 2
def baseEnd_6593330 : Nat := 1128515801236264599917611

theorem tailTrace_6593330 : CollatzResearch.WordTrace tailWord_6593330 prefixEnd_6593330 1128515801236264599917611 := by
  unfold tailWord_6593330
  simp only [CollatzResearch.WordTrace]
  refine ⟨60119625300874733989900361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160319000802332623973067629 60119625300874733989900361)
  ·
    refine ⟨45089718975656050492425271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60119625300874733989900361 45089718975656050492425271)
    ·
      refine ⟨67634578463484075738637907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45089718975656050492425271 67634578463484075738637907)
      ·
        refine ⟨101451867695226113607956861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67634578463484075738637907 101451867695226113607956861)
        ·
          refine ⟨38044450385709792602983823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101451867695226113607956861 38044450385709792602983823)
          ·
            refine ⟨57066675578564688904475735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38044450385709792602983823 57066675578564688904475735)
            ·
              refine ⟨85600013367847033356713603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57066675578564688904475735 85600013367847033356713603)
              ·
                refine ⟨128400020051770550035070405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85600013367847033356713603 128400020051770550035070405)
                ·
                  refine ⟨24075003759706978131575701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 128400020051770550035070405 24075003759706978131575701)
                  ·
                    refine ⟨1128515801236264599917611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24075003759706978131575701 1128515801236264599917611)
                    ·
                      rfl

theorem cell23_6593330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 4, 6].length) (baseStart_6593330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6593330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6593330 prefixEnd_6593330 := by exact prefixLift 6593330
  have htrace : WordTrace (prefixWord ++ tailWord_6593330) baseStart_6593330 baseEnd_6593330 := by
    simpa [prefixWord, tailWord_6593330, baseEnd_6593330] using wordTrace_append hprefix tailTrace_6593330
  have hstable : (prefixWord ++ tailWord_6593330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6593330).length < 2 ^ (prefixWord ++ tailWord_6593330).sum := by decide
  have hdescent : baseEnd_6593330 < baseStart_6593330 := by decide
  rcases family_descends (prefixWord ++ tailWord_6593330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6593331 : List Nat := [1, 1, 1, 2, 6, 3, 1, 2, 2, 1, 3]
def baseStart_6593331 : Nat := 118140960795 + 6593331 * 2 ^ 59
def prefixEnd_6593331 : Nat := 4983230072969 + 3 ^ 40 * 6593331 * 2
def baseEnd_6593331 : Nat := 3385547917189448295840329

theorem tailTrace_6593331 : CollatzResearch.WordTrace tailWord_6593331 prefixEnd_6593331 3385547917189448295840329 := by
  unfold tailWord_6593331
  simp only [CollatzResearch.WordTrace]
  refine ⟨240478537676495313130387847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160319025117663542086925231 240478537676495313130387847)
  ·
    refine ⟨360717806514742969695581771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240478537676495313130387847 360717806514742969695581771)
    ·
      refine ⟨541076709772114454543372657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360717806514742969695581771 541076709772114454543372657)
      ·
        refine ⟨405807532329085840907529493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 541076709772114454543372657 405807532329085840907529493)
        ·
          refine ⟨19022228077925898792540445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 405807532329085840907529493 19022228077925898792540445)
          ·
            refine ⟨7133335529222212047202667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19022228077925898792540445 7133335529222212047202667)
            ·
              refine ⟨10700003293833318070804001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7133335529222212047202667 10700003293833318070804001)
              ·
                refine ⟨8025002470374988553103001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10700003293833318070804001 8025002470374988553103001)
                ·
                  refine ⟨6018751852781241414827251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8025002470374988553103001 6018751852781241414827251)
                  ·
                    refine ⟨9028127779171862122240877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6018751852781241414827251 9028127779171862122240877)
                    ·
                      refine ⟨3385547917189448295840329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9028127779171862122240877 3385547917189448295840329)
                      ·
                        rfl

theorem cell23_6593331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 2, 2, 1, 3].length) (baseStart_6593331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6593331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6593331 prefixEnd_6593331 := by exact prefixLift 6593331
  have htrace : WordTrace (prefixWord ++ tailWord_6593331) baseStart_6593331 baseEnd_6593331 := by
    simpa [prefixWord, tailWord_6593331, baseEnd_6593331] using wordTrace_append hprefix tailTrace_6593331
  have hstable : (prefixWord ++ tailWord_6593331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6593331).length < 2 ^ (prefixWord ++ tailWord_6593331).sum := by decide
  have hdescent : baseEnd_6593331 < baseStart_6593331 := by decide
  rcases family_descends (prefixWord ++ tailWord_6593331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6593340 : List Nat := [2, 2, 2, 2, 1, 1, 1, 2, 4, 1, 5]
def baseStart_6593340 : Nat := 118140960795 + 6593340 * 2 ^ 59
def prefixEnd_6593340 : Nat := 4983230072969 + 3 ^ 40 * 6593340 * 2
def baseEnd_6593340 : Nat := 3385552538515338760627787

theorem tailTrace_6593340 : CollatzResearch.WordTrace tailWord_6593340 prefixEnd_6593340 3385552538515338760627787 := by
  unfold tailWord_6593340
  simp only [CollatzResearch.WordTrace]
  refine ⟨120239432966731353833732737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160319243955641805111643649 120239432966731353833732737)
  ·
    refine ⟨90179574725048515375299553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120239432966731353833732737 90179574725048515375299553)
    ·
      refine ⟨67634681043786386531474665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90179574725048515375299553 67634681043786386531474665)
      ·
        refine ⟨50726010782839789898605999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67634681043786386531474665 50726010782839789898605999)
        ·
          refine ⟨76089016174259684847908999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50726010782839789898605999 76089016174259684847908999)
          ·
            refine ⟨114133524261389527271863499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76089016174259684847908999 114133524261389527271863499)
            ·
              refine ⟨171200286392084290907795249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114133524261389527271863499 171200286392084290907795249)
              ·
                refine ⟨128400214794063218180846437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 171200286392084290907795249 128400214794063218180846437)
                ·
                  refine ⟨24075040273886853408908707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 128400214794063218180846437 24075040273886853408908707)
                  ·
                    refine ⟨36112560410830280113363061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24075040273886853408908707 36112560410830280113363061)
                    ·
                      refine ⟨3385552538515338760627787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36112560410830280113363061 3385552538515338760627787)
                      ·
                        rfl

theorem cell23_6593340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_6593340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6593340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6593340 prefixEnd_6593340 := by exact prefixLift 6593340
  have htrace : WordTrace (prefixWord ++ tailWord_6593340) baseStart_6593340 baseEnd_6593340 := by
    simpa [prefixWord, tailWord_6593340, baseEnd_6593340] using wordTrace_append hprefix tailTrace_6593340
  have hstable : (prefixWord ++ tailWord_6593340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6593340).length < 2 ^ (prefixWord ++ tailWord_6593340).sum := by decide
  have hdescent : baseEnd_6593340 < baseStart_6593340 := by decide
  rcases family_descends (prefixWord ++ tailWord_6593340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6593348 : List Nat := [2, 3, 4, 2, 1, 2, 1, 1, 1, 3, 3]
def baseStart_6593348 : Nat := 118140960795 + 6593348 * 2 ^ 59
def prefixEnd_6593348 : Nat := 4983230072969 + 3 ^ 40 * 6593348 * 2
def baseEnd_6593348 : Nat := 3385556646360574729327751

theorem tailTrace_6593348 : CollatzResearch.WordTrace tailWord_6593348 prefixEnd_6593348 3385556646360574729327751 := by
  unfold tailWord_6593348
  simp only [CollatzResearch.WordTrace]
  refine ⟨120239578858716862516878349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160319438478289150022504465 120239578858716862516878349)
  ·
    refine ⟨45089842072018823443829381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120239578858716862516878349 45089842072018823443829381)
    ·
      refine ⟨8454345388503529395718009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45089842072018823443829381 8454345388503529395718009)
      ·
        refine ⟨6340759041377647046788507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8454345388503529395718009 6340759041377647046788507)
        ·
          refine ⟨9511138562066470570182761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6340759041377647046788507 9511138562066470570182761)
          ·
            refine ⟨7133353921549852927637071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9511138562066470570182761 7133353921549852927637071)
            ·
              refine ⟨10700030882324779391455607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7133353921549852927637071 10700030882324779391455607)
              ·
                refine ⟨16050046323487169087183411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10700030882324779391455607 16050046323487169087183411)
                ·
                  refine ⟨24075069485230753630775117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16050046323487169087183411 24075069485230753630775117)
                  ·
                    refine ⟨9028151056961532611540669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24075069485230753630775117 9028151056961532611540669)
                    ·
                      refine ⟨3385556646360574729327751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9028151056961532611540669 3385556646360574729327751)
                      ·
                        rfl

theorem cell23_6593348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_6593348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6593348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6593348 prefixEnd_6593348 := by exact prefixLift 6593348
  have htrace : WordTrace (prefixWord ++ tailWord_6593348) baseStart_6593348 baseEnd_6593348 := by
    simpa [prefixWord, tailWord_6593348, baseEnd_6593348] using wordTrace_append hprefix tailTrace_6593348
  have hstable : (prefixWord ++ tailWord_6593348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6593348).length < 2 ^ (prefixWord ++ tailWord_6593348).sum := by decide
  have hdescent : baseEnd_6593348 < baseStart_6593348 := by decide
  rcases family_descends (prefixWord ++ tailWord_6593348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6593360 : List Nat := [2, 1, 1, 1, 1, 4, 4, 2, 7]
def baseStart_6593360 : Nat := 118140960795 + 6593360 * 2 ^ 59
def prefixEnd_6593360 : Nat := 4983230072969 + 3 ^ 40 * 6593360 * 2
def baseEnd_6593360 : Nat := 376173645347603186930855

theorem tailTrace_6593360 : CollatzResearch.WordTrace tailWord_6593360 prefixEnd_6593360 376173645347603186930855 := by
  unfold tailWord_6593360
  simp only [CollatzResearch.WordTrace]
  refine ⟨120239797696695125541596767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160319730262260167388795689 120239797696695125541596767)
  ·
    refine ⟨180359696545042688312395151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120239797696695125541596767 180359696545042688312395151)
    ·
      refine ⟨270539544817564032468592727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180359696545042688312395151 270539544817564032468592727)
      ·
        refine ⟨405809317226346048702889091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270539544817564032468592727 405809317226346048702889091)
        ·
          refine ⟨608713975839519073054333637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 405809317226346048702889091 608713975839519073054333637)
          ·
            refine ⟨114133870469909826197687557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 608713975839519073054333637 114133870469909826197687557)
            ·
              refine ⟨21400100713108092412066417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 114133870469909826197687557 21400100713108092412066417)
              ·
                refine ⟨16050075534831069309049813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21400100713108092412066417 16050075534831069309049813)
                ·
                  refine ⟨376173645347603186930855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16050075534831069309049813 376173645347603186930855)
                  ·
                    rfl

theorem cell23_6593360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 2, 7].length) (baseStart_6593360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6593360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6593360 prefixEnd_6593360 := by exact prefixLift 6593360
  have htrace : WordTrace (prefixWord ++ tailWord_6593360) baseStart_6593360 baseEnd_6593360 := by
    simpa [prefixWord, tailWord_6593360, baseEnd_6593360] using wordTrace_append hprefix tailTrace_6593360
  have hstable : (prefixWord ++ tailWord_6593360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6593360).length < 2 ^ (prefixWord ++ tailWord_6593360).sum := by decide
  have hdescent : baseEnd_6593360 < baseStart_6593360 := by decide
  rcases family_descends (prefixWord ++ tailWord_6593360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6593377 : List Nat := [1, 2, 3, 1, 1, 1, 2, 7, 5]
def baseStart_6593377 : Nat := 118140960795 + 6593377 * 2 ^ 59
def prefixEnd_6593377 : Nat := 4983230072969 + 3 ^ 40 * 6593377 * 2
def baseEnd_6593377 : Nat := 376174615255506123985013

theorem tailTrace_6593377 : CollatzResearch.WordTrace tailWord_6593377 prefixEnd_6593377 376174615255506123985013 := by
  unfold tailWord_6593377
  simp only [CollatzResearch.WordTrace]
  refine ⟨240480215434328662986562385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160320143622885775324374923 240480215434328662986562385)
  ·
    refine ⟨180360161575746497239921789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240480215434328662986562385 180360161575746497239921789)
    ·
      refine ⟨67635060590904936464970671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180360161575746497239921789 67635060590904936464970671)
      ·
        refine ⟨101452590886357404697456007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67635060590904936464970671 101452590886357404697456007)
        ·
          refine ⟨152178886329536107046184011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101452590886357404697456007 152178886329536107046184011)
          ·
            refine ⟨228268329494304160569276017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152178886329536107046184011 228268329494304160569276017)
            ·
              refine ⟨171201247120728120426957013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228268329494304160569276017 171201247120728120426957013)
              ·
                refine ⟨4012529229392065322506805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 171201247120728120426957013 4012529229392065322506805)
                ·
                  refine ⟨376174615255506123985013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4012529229392065322506805 376174615255506123985013)
                  ·
                    rfl

theorem cell23_6593377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 7, 5].length) (baseStart_6593377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6593377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6593377 prefixEnd_6593377 := by exact prefixLift 6593377
  have htrace : WordTrace (prefixWord ++ tailWord_6593377) baseStart_6593377 baseEnd_6593377 := by
    simpa [prefixWord, tailWord_6593377, baseEnd_6593377] using wordTrace_append hprefix tailTrace_6593377
  have hstable : (prefixWord ++ tailWord_6593377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6593377).length < 2 ^ (prefixWord ++ tailWord_6593377).sum := by decide
  have hdescent : baseEnd_6593377 < baseStart_6593377 := by decide
  rcases family_descends (prefixWord ++ tailWord_6593377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6593420 : List Nat := [2, 2, 1, 2, 1, 2, 2, 1, 2, 8]
def baseStart_6593420 : Nat := 118140960795 + 6593420 * 2 ^ 59
def prefixEnd_6593420 : Nat := 4983230072969 + 3 ^ 40 * 6593420 * 2
def baseEnd_6593420 : Nat := 1128531205655899482542473

theorem tailTrace_6593420 : CollatzResearch.WordTrace tailWord_6593420 prefixEnd_6593420 1128531205655899482542473 := by
  unfold tailWord_6593420
  simp only [CollatzResearch.WordTrace]
  refine ⟨120240891886586440665188857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160321189182115254220251809 120240891886586440665188857)
  ·
    refine ⟨90180668914939830498891643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120240891886586440665188857 90180668914939830498891643)
    ·
      refine ⟨135271003372409745748337465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90180668914939830498891643 135271003372409745748337465)
      ·
        refine ⟨101453252529307309311253099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135271003372409745748337465 101453252529307309311253099)
        ·
          refine ⟨152179878793960963966879649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101453252529307309311253099 152179878793960963966879649)
          ·
            refine ⟨114134909095470722975159737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152179878793960963966879649 114134909095470722975159737)
            ·
              refine ⟨85601181821603042231369803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114134909095470722975159737 85601181821603042231369803)
              ·
                refine ⟨128401772732404563347054705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85601181821603042231369803 128401772732404563347054705)
                ·
                  refine ⟨96301329549303422510291029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 128401772732404563347054705 96301329549303422510291029)
                  ·
                    refine ⟨1128531205655899482542473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 96301329549303422510291029 1128531205655899482542473)
                    ·
                      rfl

theorem cell23_6593420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 8].length) (baseStart_6593420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6593420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6593420 prefixEnd_6593420 := by exact prefixLift 6593420
  have htrace : WordTrace (prefixWord ++ tailWord_6593420) baseStart_6593420 baseEnd_6593420 := by
    simpa [prefixWord, tailWord_6593420, baseEnd_6593420] using wordTrace_append hprefix tailTrace_6593420
  have hstable : (prefixWord ++ tailWord_6593420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6593420).length < 2 ^ (prefixWord ++ tailWord_6593420).sum := by decide
  have hdescent : baseEnd_6593420 < baseStart_6593420 := by decide
  rcases family_descends (prefixWord ++ tailWord_6593420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6593427 : List Nat := [1, 1, 1, 2, 1, 2, 1, 3, 3, 6, 2]
def baseStart_6593427 : Nat := 118140960795 + 6593427 * 2 ^ 59
def prefixEnd_6593427 : Nat := 4983230072969 + 3 ^ 40 * 6593427 * 2
def baseEnd_6593427 : Nat := 3385597211332279920239887

theorem tailTrace_6593427 : CollatzResearch.WordTrace tailWord_6593427 prefixEnd_6593427 3385597211332279920239887 := by
  unfold tailWord_6593427
  simp only [CollatzResearch.WordTrace]
  refine ⟨240482039084147521525882535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160321359389431681017255023 240482039084147521525882535)
  ·
    refine ⟨360723058626221282288823803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240482039084147521525882535 360723058626221282288823803)
    ·
      refine ⟨541084587939331923433235705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360723058626221282288823803 541084587939331923433235705)
      ·
        refine ⟨405813440954498942574926779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 541084587939331923433235705 405813440954498942574926779)
        ·
          refine ⟨608720161431748413862390169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 405813440954498942574926779 608720161431748413862390169)
          ·
            refine ⟨456540121073811310396792627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 608720161431748413862390169 456540121073811310396792627)
            ·
              refine ⟨684810181610716965595188941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 456540121073811310396792627 684810181610716965595188941)
              ·
                refine ⟨256803818104018862098195853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 684810181610716965595188941 256803818104018862098195853)
                ·
                  refine ⟨96301431789007073286823445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 256803818104018862098195853 96301431789007073286823445)
                  ·
                    refine ⟨4514129615109706560319849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 96301431789007073286823445 4514129615109706560319849)
                    ·
                      refine ⟨3385597211332279920239887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4514129615109706560319849 3385597211332279920239887)
                      ·
                        rfl

theorem cell23_6593427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 6, 2].length) (baseStart_6593427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6593427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6593427 prefixEnd_6593427 := by exact prefixLift 6593427
  have htrace : WordTrace (prefixWord ++ tailWord_6593427) baseStart_6593427 baseEnd_6593427 := by
    simpa [prefixWord, tailWord_6593427, baseEnd_6593427] using wordTrace_append hprefix tailTrace_6593427
  have hstable : (prefixWord ++ tailWord_6593427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6593427).length < 2 ^ (prefixWord ++ tailWord_6593427).sum := by decide
  have hdescent : baseEnd_6593427 < baseStart_6593427 := by decide
  rcases family_descends (prefixWord ++ tailWord_6593427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6593444 : List Nat := [2, 3, 1, 2, 1, 2, 2, 2, 2, 4, 2]
def baseStart_6593444 : Nat := 118140960795 + 6593444 * 2 ^ 59
def prefixEnd_6593444 : Nat := 4983230072969 + 3 ^ 40 * 6593444 * 2
def baseEnd_6593444 : Nat := 3385605940503406353727309

theorem tailTrace_6593444 : CollatzResearch.WordTrace tailWord_6593444 prefixEnd_6593444 3385605940503406353727309 := by
  unfold tailWord_6593444
  simp only [CollatzResearch.WordTrace]
  refine ⟨120241329562542966714625693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160321772750057288952834257 120241329562542966714625693)
  ·
    refine ⟨45090498585953612517984635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120241329562542966714625693 45090498585953612517984635)
    ·
      refine ⟨67635747878930418776976953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45090498585953612517984635 67635747878930418776976953)
      ·
        refine ⟨50726810909197814082732715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67635747878930418776976953 50726810909197814082732715)
        ·
          refine ⟨76090216363796721124099073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50726810909197814082732715 76090216363796721124099073)
          ·
            refine ⟨57067662272847540843074305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76090216363796721124099073 57067662272847540843074305)
            ·
              refine ⟨42800746704635655632305729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57067662272847540843074305 42800746704635655632305729)
              ·
                refine ⟨32100560028476741724229297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42800746704635655632305729 32100560028476741724229297)
                ·
                  refine ⟨24075420021357556293171973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32100560028476741724229297 24075420021357556293171973)
                  ·
                    refine ⟨4514141254004541804969745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24075420021357556293171973 4514141254004541804969745)
                    ·
                      refine ⟨3385605940503406353727309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4514141254004541804969745 3385605940503406353727309)
                      ·
                        rfl

theorem cell23_6593444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 2, 2, 4, 2].length) (baseStart_6593444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6593444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6593444 prefixEnd_6593444 := by exact prefixLift 6593444
  have htrace : WordTrace (prefixWord ++ tailWord_6593444) baseStart_6593444 baseEnd_6593444 := by
    simpa [prefixWord, tailWord_6593444, baseEnd_6593444] using wordTrace_append hprefix tailTrace_6593444
  have hstable : (prefixWord ++ tailWord_6593444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6593444).length < 2 ^ (prefixWord ++ tailWord_6593444).sum := by decide
  have hdescent : baseEnd_6593444 < baseStart_6593444 := by decide
  rcases family_descends (prefixWord ++ tailWord_6593444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6593501 : List Nat := [1, 4, 3, 1, 2, 3, 1, 2, 6]
def baseStart_6593501 : Nat := 118140960795 + 6593501 * 2 ^ 59
def prefixEnd_6593501 : Nat := 4983230072969 + 3 ^ 40 * 6593501 * 2
def baseEnd_6593501 : Nat := 376181689877856958968283

theorem tailTrace_6593501 : CollatzResearch.WordTrace tailWord_6593501 prefixEnd_6593501 376181689877856958968283 := by
  unfold tailWord_6593501
  simp only [CollatzResearch.WordTrace]
  refine ⟨240484738085879432164076357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160323158723919621442717571 240484738085879432164076357)
  ·
    refine ⟨45090888391102393530764317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 240484738085879432164076357 45090888391102393530764317)
    ·
      refine ⟨16909083146663397574036619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45090888391102393530764317 16909083146663397574036619)
      ·
        refine ⟨25363624719995096361054929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16909083146663397574036619 25363624719995096361054929)
        ·
          refine ⟨19022718539996322270791197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25363624719995096361054929 19022718539996322270791197)
          ·
            refine ⟨7133519452498620851546699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19022718539996322270791197 7133519452498620851546699)
            ·
              refine ⟨10700279178747931277320049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7133519452498620851546699 10700279178747931277320049)
              ·
                refine ⟨8025209384060948457990037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10700279178747931277320049 8025209384060948457990037)
                ·
                  refine ⟨376181689877856958968283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8025209384060948457990037 376181689877856958968283)
                  ·
                    rfl

theorem cell23_6593501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 2, 6].length) (baseStart_6593501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6593501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6593501 prefixEnd_6593501 := by exact prefixLift 6593501
  have htrace : WordTrace (prefixWord ++ tailWord_6593501) baseStart_6593501 baseEnd_6593501 := by
    simpa [prefixWord, tailWord_6593501, baseEnd_6593501] using wordTrace_append hprefix tailTrace_6593501
  have hstable : (prefixWord ++ tailWord_6593501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6593501).length < 2 ^ (prefixWord ++ tailWord_6593501).sum := by decide
  have hdescent : baseEnd_6593501 < baseStart_6593501 := by decide
  rcases family_descends (prefixWord ++ tailWord_6593501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6593511 : List Nat := [1, 1, 5, 2, 2, 1, 1, 3, 3, 1, 3]
def baseStart_6593511 : Nat := 118140960795 + 6593511 * 2 ^ 59
def prefixEnd_6593511 : Nat := 4983230072969 + 3 ^ 40 * 6593511 * 2
def baseEnd_6593511 : Nat := 3385640343707257591589501

theorem tailTrace_6593511 : CollatzResearch.WordTrace tailWord_6593511 prefixEnd_6593511 3385640343707257591589501 := by
  unfold tailWord_6593511
  simp only [CollatzResearch.WordTrace]
  refine ⟨240485102815843203871940387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160323401877228802581293591 240485102815843203871940387)
  ·
    refine ⟨360727654223764805807910581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240485102815843203871940387 360727654223764805807910581)
    ·
      refine ⟨33818217583477950544491617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 360727654223764805807910581 33818217583477950544491617)
      ·
        refine ⟨25363663187608462908368713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33818217583477950544491617 25363663187608462908368713)
        ·
          refine ⟨19022747390706347181276535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25363663187608462908368713 19022747390706347181276535)
          ·
            refine ⟨28534121086059520771914803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19022747390706347181276535 28534121086059520771914803)
            ·
              refine ⟨42801181629089281157872205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28534121086059520771914803 42801181629089281157872205)
              ·
                refine ⟨16050443110908480434202077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42801181629089281157872205 16050443110908480434202077)
                ·
                  refine ⟨6018916166590680162825779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16050443110908480434202077 6018916166590680162825779)
                  ·
                    refine ⟨9028374249886020244238669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6018916166590680162825779 9028374249886020244238669)
                    ·
                      refine ⟨3385640343707257591589501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9028374249886020244238669 3385640343707257591589501)
                      ·
                        rfl

theorem cell23_6593511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_6593511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6593511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6593511 prefixEnd_6593511 := by exact prefixLift 6593511
  have htrace : WordTrace (prefixWord ++ tailWord_6593511) baseStart_6593511 baseEnd_6593511 := by
    simpa [prefixWord, tailWord_6593511, baseEnd_6593511] using wordTrace_append hprefix tailTrace_6593511
  have hstable : (prefixWord ++ tailWord_6593511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6593511).length < 2 ^ (prefixWord ++ tailWord_6593511).sum := by decide
  have hdescent : baseEnd_6593511 < baseStart_6593511 := by decide
  rcases family_descends (prefixWord ++ tailWord_6593511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6593544 : List Nat := [2, 1, 3, 2, 1, 3, 1, 2, 4, 4]
def baseStart_6593544 : Nat := 118140960795 + 6593544 * 2 ^ 59
def prefixEnd_6593544 : Nat := 4983230072969 + 3 ^ 40 * 6593544 * 2
def baseEnd_6593544 : Nat := 1128552429522951987492283

theorem tailTrace_6593544 : CollatzResearch.WordTrace tailWord_6593544 prefixEnd_6593544 1128552429522951987492283 := by
  unfold tailWord_6593544
  simp only [CollatzResearch.WordTrace]
  refine ⟨120243153212361825253945843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160324204283149100338594457 120243153212361825253945843)
  ·
    refine ⟨180364729818542737880918765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120243153212361825253945843 180364729818542737880918765)
    ·
      refine ⟨67636773681953526705344537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180364729818542737880918765 67636773681953526705344537)
      ·
        refine ⟨50727580261465145029008403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67636773681953526705344537 50727580261465145029008403)
        ·
          refine ⟨76091370392197717543512605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50727580261465145029008403 76091370392197717543512605)
          ·
            refine ⟨28534263897074144078817227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76091370392197717543512605 28534263897074144078817227)
            ·
              refine ⟨42801395845611216118225841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28534263897074144078817227 42801395845611216118225841)
              ·
                refine ⟨32101046884208412088669381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42801395845611216118225841 32101046884208412088669381)
                ·
                  refine ⟨6018946290789077266625509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32101046884208412088669381 6018946290789077266625509)
                  ·
                    refine ⟨1128552429522951987492283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6018946290789077266625509 1128552429522951987492283)
                    ·
                      rfl

theorem cell23_6593544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 2, 4, 4].length) (baseStart_6593544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6593544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6593544 prefixEnd_6593544 := by exact prefixLift 6593544
  have htrace : WordTrace (prefixWord ++ tailWord_6593544) baseStart_6593544 baseEnd_6593544 := by
    simpa [prefixWord, tailWord_6593544, baseEnd_6593544] using wordTrace_append hprefix tailTrace_6593544
  have hstable : (prefixWord ++ tailWord_6593544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6593544).length < 2 ^ (prefixWord ++ tailWord_6593544).sum := by decide
  have hdescent : baseEnd_6593544 < baseStart_6593544 := by decide
  rcases family_descends (prefixWord ++ tailWord_6593544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6593557 : List Nat := [1, 3, 2, 1, 4, 1, 11]
def baseStart_6593557 : Nat := 118140960795 + 6593557 * 2 ^ 59
def prefixEnd_6593557 : Nat := 4983230072969 + 3 ^ 40 * 6593557 * 2
def baseEnd_6593557 : Nat := 41798320540955116192769

theorem tailTrace_6593557 : CollatzResearch.WordTrace tailWord_6593557 prefixEnd_6593557 41798320540955116192769 := by
  unfold tailWord_6593557
  simp only [CollatzResearch.WordTrace]
  refine ⟨240486780573676553728114925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160324520382451035818743283 240486780573676553728114925)
  ·
    refine ⟨90182542715128707648043097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 240486780573676553728114925 90182542715128707648043097)
    ·
      refine ⟨67636907036346530736032323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90182542715128707648043097 67636907036346530736032323)
      ·
        refine ⟨101455360554519796104048485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67636907036346530736032323 101455360554519796104048485)
        ·
          refine ⟨19022880103972461769509091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101455360554519796104048485 19022880103972461769509091)
          ·
            refine ⟨28534320155958692654263637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19022880103972461769509091 28534320155958692654263637)
            ·
              refine ⟨41798320540955116192769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 28534320155958692654263637 41798320540955116192769)
              ·
                rfl

theorem cell23_6593557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 11].length) (baseStart_6593557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6593557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6593557 prefixEnd_6593557 := by exact prefixLift 6593557
  have htrace : WordTrace (prefixWord ++ tailWord_6593557) baseStart_6593557 baseEnd_6593557 := by
    simpa [prefixWord, tailWord_6593557, baseEnd_6593557] using wordTrace_append hprefix tailTrace_6593557
  have hstable : (prefixWord ++ tailWord_6593557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6593557).length < 2 ^ (prefixWord ++ tailWord_6593557).sum := by decide
  have hdescent : baseEnd_6593557 < baseStart_6593557 := by decide
  rcases family_descends (prefixWord ++ tailWord_6593557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6593578 : List Nat := [3, 1, 4, 1, 3, 1, 1, 3, 2, 4]
def baseStart_6593578 : Nat := 118140960795 + 6593578 * 2 ^ 59
def prefixEnd_6593578 : Nat := 4983230072969 + 3 ^ 40 * 6593578 * 2
def baseEnd_6593578 : Nat := 1128558248970369609817231

theorem tailTrace_6593578 : CollatzResearch.WordTrace tailWord_6593578 prefixEnd_6593578 1128558248970369609817231 := by
  unfold tailWord_6593578
  simp only [CollatzResearch.WordTrace]
  refine ⟨60121886626650118578657347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160325031004400316209752925 60121886626650118578657347)
  ·
    refine ⟨90182829939975177867986021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60121886626650118578657347 90182829939975177867986021)
    ·
      refine ⟨16909280613745345850247379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90182829939975177867986021 16909280613745345850247379)
      ·
        refine ⟨25363920920618018775371069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16909280613745345850247379 25363920920618018775371069)
        ·
          refine ⟨9511470345231757040764151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25363920920618018775371069 9511470345231757040764151)
          ·
            refine ⟨14267205517847635561146227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9511470345231757040764151 14267205517847635561146227)
            ·
              refine ⟨21400808276771453341719341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14267205517847635561146227 21400808276771453341719341)
              ·
                refine ⟨8025303103789295003144753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21400808276771453341719341 8025303103789295003144753)
                ·
                  refine ⟨6018977327841971252358565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8025303103789295003144753 6018977327841971252358565)
                  ·
                    refine ⟨1128558248970369609817231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6018977327841971252358565 1128558248970369609817231)
                    ·
                      rfl

theorem cell23_6593578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_6593578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6593578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6593578 prefixEnd_6593578 := by exact prefixLift 6593578
  have htrace : WordTrace (prefixWord ++ tailWord_6593578) baseStart_6593578 baseEnd_6593578 := by
    simpa [prefixWord, tailWord_6593578, baseEnd_6593578] using wordTrace_append hprefix tailTrace_6593578
  have hstable : (prefixWord ++ tailWord_6593578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6593578).length < 2 ^ (prefixWord ++ tailWord_6593578).sum := by decide
  have hdescent : baseEnd_6593578 < baseStart_6593578 := by decide
  rcases family_descends (prefixWord ++ tailWord_6593578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6593584 : List Nat := [2, 1, 1, 1, 2, 4, 2, 3, 1, 3, 3]
def baseStart_6593584 : Nat := 118140960795 + 6593584 * 2 ^ 59
def prefixEnd_6593584 : Nat := 4983230072969 + 3 ^ 40 * 6593584 * 2
def baseEnd_6593584 : Nat := 3385677827795035805976665

theorem tailTrace_6593584 : CollatzResearch.WordTrace tailWord_6593584 prefixEnd_6593584 3385677827795035805976665 := by
  unfold tailWord_6593584
  simp only [CollatzResearch.WordTrace]
  refine ⟨120243882672289368669673903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160325176896385824892898537 120243882672289368669673903)
  ·
    refine ⟨180365824008434053004510855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120243882672289368669673903 180365824008434053004510855)
    ·
      refine ⟨270548736012651079506766283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180365824008434053004510855 270548736012651079506766283)
      ·
        refine ⟨405823104018976619260149425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270548736012651079506766283 405823104018976619260149425)
        ·
          refine ⟨304367328014232464445112069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 405823104018976619260149425 304367328014232464445112069)
          ·
            refine ⟨57068874002668587083458513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 304367328014232464445112069 57068874002668587083458513)
            ·
              refine ⟨42801655502001440312593885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57068874002668587083458513 42801655502001440312593885)
              ·
                refine ⟨16050620813250540117222707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42801655502001440312593885 16050620813250540117222707)
                ·
                  refine ⟨24075931219875810175834061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16050620813250540117222707 24075931219875810175834061)
                  ·
                    refine ⟨9028474207453428815937773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24075931219875810175834061 9028474207453428815937773)
                    ·
                      refine ⟨3385677827795035805976665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9028474207453428815937773 3385677827795035805976665)
                      ·
                        rfl

theorem cell23_6593584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 3, 1, 3, 3].length) (baseStart_6593584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6593584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6593584 prefixEnd_6593584 := by exact prefixLift 6593584
  have htrace : WordTrace (prefixWord ++ tailWord_6593584) baseStart_6593584 baseEnd_6593584 := by
    simpa [prefixWord, tailWord_6593584, baseEnd_6593584] using wordTrace_append hprefix tailTrace_6593584
  have hstable : (prefixWord ++ tailWord_6593584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6593584).length < 2 ^ (prefixWord ++ tailWord_6593584).sum := by decide
  have hdescent : baseEnd_6593584 < baseStart_6593584 := by decide
  rcases family_descends (prefixWord ++ tailWord_6593584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6593588 : List Nat := [2, 5, 1, 2, 1, 2, 1, 1, 3, 2, 3]
def baseStart_6593588 : Nat := 118140960795 + 6593588 * 2 ^ 59
def prefixEnd_6593588 : Nat := 4983230072969 + 3 ^ 40 * 6593588 * 2
def baseEnd_6593588 : Nat := 3385679881717653790326647

theorem tailTrace_6593588 : CollatzResearch.WordTrace tailWord_6593588 prefixEnd_6593588 3385679881717653790326647 := by
  unfold tailWord_6593588
  simp only [CollatzResearch.WordTrace]
  refine ⟨120243955618282123011246709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160325274157709497348328945 120243955618282123011246709)
  ·
    refine ⟨11272870839213949032304379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 120243955618282123011246709 11272870839213949032304379)
    ·
      refine ⟨16909306258820923548456569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11272870839213949032304379 16909306258820923548456569)
      ·
        refine ⟨12681979694115692661342427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16909306258820923548456569 12681979694115692661342427)
        ·
          refine ⟨19022969541173538992013641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12681979694115692661342427 19022969541173538992013641)
          ·
            refine ⟨14267227155880154244010231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19022969541173538992013641 14267227155880154244010231)
            ·
              refine ⟨21400840733820231366015347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14267227155880154244010231 21400840733820231366015347)
              ·
                refine ⟨32101261100730347049023021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21400840733820231366015347 32101261100730347049023021)
                ·
                  refine ⟨12037972912773880143383633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32101261100730347049023021 12037972912773880143383633)
                  ·
                    refine ⟨9028479684580410107537725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12037972912773880143383633 9028479684580410107537725)
                    ·
                      refine ⟨3385679881717653790326647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9028479684580410107537725 3385679881717653790326647)
                      ·
                        rfl

theorem cell23_6593588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_6593588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6593588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6593588 prefixEnd_6593588 := by exact prefixLift 6593588
  have htrace : WordTrace (prefixWord ++ tailWord_6593588) baseStart_6593588 baseEnd_6593588 := by
    simpa [prefixWord, tailWord_6593588, baseEnd_6593588] using wordTrace_append hprefix tailTrace_6593588
  have hstable : (prefixWord ++ tailWord_6593588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6593588).length < 2 ^ (prefixWord ++ tailWord_6593588).sum := by decide
  have hdescent : baseEnd_6593588 < baseStart_6593588 := by decide
  rcases family_descends (prefixWord ++ tailWord_6593588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6593618 : List Nat := [3, 2, 2, 1, 3, 1, 1, 4, 2, 1, 3]
def baseStart_6593618 : Nat := 118140960795 + 6593618 * 2 ^ 59
def prefixEnd_6593618 : Nat := 4983230072969 + 3 ^ 40 * 6593618 * 2
def baseEnd_6593618 : Nat := 3385695286137288672951509

theorem tailTrace_6593618 : CollatzResearch.WordTrace tailWord_6593618 prefixEnd_6593618 3385695286137288672951509 := by
  unfold tailWord_6593618
  simp only [CollatzResearch.WordTrace]
  refine ⟨60122251356613890286521377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160326003617637040764057005 60122251356613890286521377)
  ·
    refine ⟨45091688517460417714891033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60122251356613890286521377 45091688517460417714891033)
    ·
      refine ⟨33818766388095313286168275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45091688517460417714891033 33818766388095313286168275)
      ·
        refine ⟨50728149582142969929252413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33818766388095313286168275 50728149582142969929252413)
        ·
          refine ⟨19023056093303613723469655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50728149582142969929252413 19023056093303613723469655)
          ·
            refine ⟨28534584139955420585204483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19023056093303613723469655 28534584139955420585204483)
            ·
              refine ⟨42801876209933130877806725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28534584139955420585204483 42801876209933130877806725)
              ·
                refine ⟨8025351789362462039588761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42801876209933130877806725 8025351789362462039588761)
                ·
                  refine ⟨6019013842021846529691571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8025351789362462039588761 6019013842021846529691571)
                  ·
                    refine ⟨9028520763032769794537357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6019013842021846529691571 9028520763032769794537357)
                    ·
                      refine ⟨3385695286137288672951509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9028520763032769794537357 3385695286137288672951509)
                      ·
                        rfl

theorem cell23_6593618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 4, 2, 1, 3].length) (baseStart_6593618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6593618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6593618 prefixEnd_6593618 := by exact prefixLift 6593618
  have htrace : WordTrace (prefixWord ++ tailWord_6593618) baseStart_6593618 baseEnd_6593618 := by
    simpa [prefixWord, tailWord_6593618, baseEnd_6593618] using wordTrace_append hprefix tailTrace_6593618
  have hstable : (prefixWord ++ tailWord_6593618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6593618).length < 2 ^ (prefixWord ++ tailWord_6593618).sum := by decide
  have hdescent : baseEnd_6593618 < baseStart_6593618 := by decide
  rcases family_descends (prefixWord ++ tailWord_6593618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6593641 : List Nat := [1, 2, 1, 1, 1, 6, 1, 3, 1, 4, 2]
def baseStart_6593641 : Nat := 118140960795 + 6593641 * 2 ^ 59
def prefixEnd_6593641 : Nat := 4983230072969 + 3 ^ 40 * 6593641 * 2
def baseEnd_6593641 : Nat := 3385707096192342082963903

theorem tailTrace_6593641 : CollatzResearch.WordTrace tailWord_6593641 prefixEnd_6593641 3385707096192342082963903 := by
  unfold tailWord_6593641
  simp only [CollatzResearch.WordTrace]
  refine ⟨240489844305372236074172777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160326562870248157382781851 240489844305372236074172777)
  ·
    refine ⟨180367383229029177055629583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240489844305372236074172777 180367383229029177055629583)
    ·
      refine ⟨270551074843543765583444375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180367383229029177055629583 270551074843543765583444375)
      ·
        refine ⟨405826612265315648375166563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270551074843543765583444375 405826612265315648375166563)
        ·
          refine ⟨608739918397973472562749845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 405826612265315648375166563 608739918397973472562749845)
          ·
            refine ⟨28534683674905006526378899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 608739918397973472562749845 28534683674905006526378899)
            ·
              refine ⟨42802025512357509789568349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28534683674905006526378899 42802025512357509789568349)
              ·
                refine ⟨16050759567134066171088131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42802025512357509789568349 16050759567134066171088131)
                ·
                  refine ⟨24076139350701099256632197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16050759567134066171088131 24076139350701099256632197)
                  ·
                    refine ⟨4514276128256456110618537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24076139350701099256632197 4514276128256456110618537)
                    ·
                      refine ⟨3385707096192342082963903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4514276128256456110618537 3385707096192342082963903)
                      ·
                        rfl

theorem cell23_6593641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 3, 1, 4, 2].length) (baseStart_6593641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6593641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6593641 prefixEnd_6593641 := by exact prefixLift 6593641
  have htrace : WordTrace (prefixWord ++ tailWord_6593641) baseStart_6593641 baseEnd_6593641 := by
    simpa [prefixWord, tailWord_6593641, baseEnd_6593641] using wordTrace_append hprefix tailTrace_6593641
  have hstable : (prefixWord ++ tailWord_6593641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6593641).length < 2 ^ (prefixWord ++ tailWord_6593641).sum := by decide
  have hdescent : baseEnd_6593641 < baseStart_6593641 := by decide
  rcases family_descends (prefixWord ++ tailWord_6593641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6593644 : List Nat := [2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 3]
def baseStart_6593644 : Nat := 118140960795 + 6593644 * 2 ^ 59
def prefixEnd_6593644 : Nat := 4983230072969 + 3 ^ 40 * 6593644 * 2
def baseEnd_6593644 : Nat := 3385708636634305571226389

theorem tailTrace_6593644 : CollatzResearch.WordTrace tailWord_6593644 prefixEnd_6593644 3385708636634305571226389 := by
  unfold tailWord_6593644
  simp only [CollatzResearch.WordTrace]
  refine ⟨120244976862180683793265993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160326635816240911724354657 120244976862180683793265993)
  ·
    refine ⟨90183732646635512844949495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120244976862180683793265993 90183732646635512844949495)
    ·
      refine ⟨135275598969953269267424243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90183732646635512844949495 135275598969953269267424243)
      ·
        refine ⟨202913398454929903901136365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135275598969953269267424243 202913398454929903901136365)
        ·
          refine ⟨76092524420598713962926137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 202913398454929903901136365 76092524420598713962926137)
          ·
            refine ⟨57069393315449035472194603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76092524420598713962926137 57069393315449035472194603)
            ·
              refine ⟨85604089973173553208291905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57069393315449035472194603 85604089973173553208291905)
              ·
                refine ⟨64203067479880164906218929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85604089973173553208291905 64203067479880164906218929)
                ·
                  refine ⟨48152300609910123679664197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64203067479880164906218929 48152300609910123679664197)
                  ·
                    refine ⟨9028556364358148189937037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48152300609910123679664197 9028556364358148189937037)
                    ·
                      refine ⟨3385708636634305571226389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9028556364358148189937037 3385708636634305571226389)
                      ·
                        rfl

theorem cell23_6593644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 3].length) (baseStart_6593644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6593644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6593644 prefixEnd_6593644 := by exact prefixLift 6593644
  have htrace : WordTrace (prefixWord ++ tailWord_6593644) baseStart_6593644 baseEnd_6593644 := by
    simpa [prefixWord, tailWord_6593644, baseEnd_6593644] using wordTrace_append hprefix tailTrace_6593644
  have hstable : (prefixWord ++ tailWord_6593644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6593644).length < 2 ^ (prefixWord ++ tailWord_6593644).sum := by decide
  have hdescent : baseEnd_6593644 < baseStart_6593644 := by decide
  rcases family_descends (prefixWord ++ tailWord_6593644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6593692 : List Nat := [2, 2, 3, 2, 1, 3, 3, 1, 2, 2, 2]
def baseStart_6593692 : Nat := 118140960795 + 6593692 * 2 ^ 59
def prefixEnd_6593692 : Nat := 4983230072969 + 3 ^ 40 * 6593692 * 2
def baseEnd_6593692 : Nat := 3385733283705721383426169

theorem tailTrace_6593692 : CollatzResearch.WordTrace tailWord_6593692 prefixEnd_6593692 3385733283705721383426169 := by
  unfold tailWord_6593692
  simp only [CollatzResearch.WordTrace]
  refine ⟨120245852214093735892139665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160327802952124981189519553 120245852214093735892139665)
  ·
    refine ⟨90184389160570301919104749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120245852214093735892139665 90184389160570301919104749)
    ·
      refine ⟨33819145935213863219664281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90184389160570301919104749 33819145935213863219664281)
      ·
        refine ⟨25364359451410397414748211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33819145935213863219664281 25364359451410397414748211)
        ·
          refine ⟨38046539177115596122122317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25364359451410397414748211 38046539177115596122122317)
          ·
            refine ⟨14267452191418348545795869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38046539177115596122122317 14267452191418348545795869)
            ·
              refine ⟨5350294571781880704673451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14267452191418348545795869 5350294571781880704673451)
              ·
                refine ⟨8025441857672821057010177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5350294571781880704673451 8025441857672821057010177)
                ·
                  refine ⟨6019081393254615792757633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8025441857672821057010177 6019081393254615792757633)
                  ·
                    refine ⟨4514311044940961844568225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6019081393254615792757633 4514311044940961844568225)
                    ·
                      refine ⟨3385733283705721383426169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4514311044940961844568225 3385733283705721383426169)
                      ·
                        rfl

theorem cell23_6593692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 3, 1, 2, 2, 2].length) (baseStart_6593692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6593692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6593692 prefixEnd_6593692 := by exact prefixLift 6593692
  have htrace : WordTrace (prefixWord ++ tailWord_6593692) baseStart_6593692 baseEnd_6593692 := by
    simpa [prefixWord, tailWord_6593692, baseEnd_6593692] using wordTrace_append hprefix tailTrace_6593692
  have hstable : (prefixWord ++ tailWord_6593692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6593692).length < 2 ^ (prefixWord ++ tailWord_6593692).sum := by decide
  have hdescent : baseEnd_6593692 < baseStart_6593692 := by decide
  rcases family_descends (prefixWord ++ tailWord_6593692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6593731 : List Nat := [1, 1, 1, 3, 1, 1, 1, 6, 2, 4, 2]
def baseStart_6593731 : Nat := 118140960795 + 6593731 * 2 ^ 59
def prefixEnd_6593731 : Nat := 4983230072969 + 3 ^ 40 * 6593731 * 2
def baseEnd_6593731 : Nat := 3385753309451246730838489

theorem tailTrace_6593731 : CollatzResearch.WordTrace tailWord_6593731 prefixEnd_6593731 3385753309451246730838489 := by
  unfold tailWord_6593731
  simp only [CollatzResearch.WordTrace]
  refine ⟨240493126875046181444949047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160328751250030787629966031 240493126875046181444949047)
  ·
    refine ⟨360739690312569272167423571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240493126875046181444949047 360739690312569272167423571)
    ·
      refine ⟨541109535468853908251135357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360739690312569272167423571 541109535468853908251135357)
      ·
        refine ⟨202916075800820215594175759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 541109535468853908251135357 202916075800820215594175759)
        ·
          refine ⟨304374113701230323391263639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202916075800820215594175759 304374113701230323391263639)
          ·
            refine ⟨456561170551845485086895459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 304374113701230323391263639 456561170551845485086895459)
            ·
              refine ⟨684841755827768227630343189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 456561170551845485086895459 684841755827768227630343189)
              ·
                refine ⟨32101957304426635670172337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 684841755827768227630343189 32101957304426635670172337)
                ·
                  refine ⟨24076467978319976752629253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32101957304426635670172337 24076467978319976752629253)
                  ·
                    refine ⟨4514337745934995641117985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24076467978319976752629253 4514337745934995641117985)
                    ·
                      refine ⟨3385753309451246730838489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4514337745934995641117985 3385753309451246730838489)
                      ·
                        rfl

theorem cell23_6593731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 6, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 6, 2, 4, 2].length) (baseStart_6593731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6593731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6593731 prefixEnd_6593731 := by exact prefixLift 6593731
  have htrace : WordTrace (prefixWord ++ tailWord_6593731) baseStart_6593731 baseEnd_6593731 := by
    simpa [prefixWord, tailWord_6593731, baseEnd_6593731] using wordTrace_append hprefix tailTrace_6593731
  have hstable : (prefixWord ++ tailWord_6593731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6593731).length < 2 ^ (prefixWord ++ tailWord_6593731).sum := by decide
  have hdescent : baseEnd_6593731 < baseStart_6593731 := by decide
  rcases family_descends (prefixWord ++ tailWord_6593731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6593768 : List Nat := [2, 1, 4, 1, 2, 1, 4, 1, 2, 2, 3]
def baseStart_6593768 : Nat := 118140960795 + 6593768 * 2 ^ 59
def prefixEnd_6593768 : Nat := 4983230072969 + 3 ^ 40 * 6593768 * 2
def baseEnd_6593768 : Nat := 3385772308235463086075819

theorem tailTrace_6593768 : CollatzResearch.WordTrace tailWord_6593768 prefixEnd_6593768 3385772308235463086075819 := by
  unfold tailWord_6593768
  simp only [CollatzResearch.WordTrace]
  refine ⟨120247238187956068382022979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160329650917274757842697305 120247238187956068382022979)
  ·
    refine ⟨180370857281934102573034469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120247238187956068382022979 180370857281934102573034469)
    ·
      refine ⟨33819535740362644232443963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 180370857281934102573034469 33819535740362644232443963)
      ·
        refine ⟨50729303610543966348665945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33819535740362644232443963 50729303610543966348665945)
        ·
          refine ⟨38046977707907974761499459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50729303610543966348665945 38046977707907974761499459)
          ·
            refine ⟨57070466561861962142249189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38046977707907974761499459 57070466561861962142249189)
            ·
              refine ⟨10700712480349117901671723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57070466561861962142249189 10700712480349117901671723)
              ·
                refine ⟨16051068720523676852507585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10700712480349117901671723 16051068720523676852507585)
                ·
                  refine ⟨12038301540392757639380689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16051068720523676852507585 12038301540392757639380689)
                  ·
                    refine ⟨9028726155294568229535517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12038301540392757639380689 9028726155294568229535517)
                    ·
                      refine ⟨3385772308235463086075819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9028726155294568229535517 3385772308235463086075819)
                      ·
                        rfl

theorem cell23_6593768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 1, 2, 2, 3].length) (baseStart_6593768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6593768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6593768 prefixEnd_6593768 := by exact prefixLift 6593768
  have htrace : WordTrace (prefixWord ++ tailWord_6593768) baseStart_6593768 baseEnd_6593768 := by
    simpa [prefixWord, tailWord_6593768, baseEnd_6593768] using wordTrace_append hprefix tailTrace_6593768
  have hstable : (prefixWord ++ tailWord_6593768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6593768).length < 2 ^ (prefixWord ++ tailWord_6593768).sum := by decide
  have hdescent : baseEnd_6593768 < baseStart_6593768 := by decide
  rcases family_descends (prefixWord ++ tailWord_6593768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6593788 : List Nat := [2, 2, 2, 1, 5, 1, 2, 2, 6]
def baseStart_6593788 : Nat := 118140960795 + 6593788 * 2 ^ 59
def prefixEnd_6593788 : Nat := 4983230072969 + 3 ^ 40 * 6593788 * 2
def baseEnd_6593788 : Nat := 376198064205394778647303

theorem tailTrace_6593788 : CollatzResearch.WordTrace tailWord_6593788 prefixEnd_6593788 376198064205394778647303 := by
  unfold tailWord_6593788
  simp only [CollatzResearch.WordTrace]
  refine ⟨120247602917919840089887009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160330137223893120119849345 120247602917919840089887009)
  ·
    refine ⟨90185702188439880067415257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120247602917919840089887009 90185702188439880067415257)
    ·
      refine ⟨67639276641329910050561443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90185702188439880067415257 67639276641329910050561443)
      ·
        refine ⟨101458914961994865075842165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67639276641329910050561443 101458914961994865075842165)
        ·
          refine ⟨9511773277687018600860203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 101458914961994865075842165 9511773277687018600860203)
          ·
            refine ⟨14267659916530527901290305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9511773277687018600860203 14267659916530527901290305)
            ·
              refine ⟨10700744937397895925967729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14267659916530527901290305 10700744937397895925967729)
              ·
                refine ⟨8025558703048421944475797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10700744937397895925967729 8025558703048421944475797)
                ·
                  refine ⟨376198064205394778647303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8025558703048421944475797 376198064205394778647303)
                  ·
                    rfl

theorem cell23_6593788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 2, 6].length) (baseStart_6593788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6593788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6593788 prefixEnd_6593788 := by exact prefixLift 6593788
  have htrace : WordTrace (prefixWord ++ tailWord_6593788) baseStart_6593788 baseEnd_6593788 := by
    simpa [prefixWord, tailWord_6593788, baseEnd_6593788] using wordTrace_append hprefix tailTrace_6593788
  have hstable : (prefixWord ++ tailWord_6593788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6593788).length < 2 ^ (prefixWord ++ tailWord_6593788).sum := by decide
  have hdescent : baseEnd_6593788 < baseStart_6593788 := by decide
  rcases family_descends (prefixWord ++ tailWord_6593788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6593832 : List Nat := [2, 1, 5, 1, 2, 1, 1, 5, 1, 1, 3]
def baseStart_6593832 : Nat := 118140960795 + 6593832 * 2 ^ 59
def prefixEnd_6593832 : Nat := 4983230072969 + 3 ^ 40 * 6593832 * 2
def baseEnd_6593832 : Nat := 3385805170997350835675525

theorem tailTrace_6593832 : CollatzResearch.WordTrace tailWord_6593832 prefixEnd_6593832 3385805170997350835675525 := by
  unfold tailWord_6593832
  simp only [CollatzResearch.WordTrace]
  refine ⟨120248405323840137847187875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160331207098453517129583833 120248405323840137847187875)
  ·
    refine ⟨180372607985760206770781813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120248405323840137847187875 180372607985760206770781813)
    ·
      refine ⟨16909931998665019384760795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 180372607985760206770781813 16909931998665019384760795)
      ·
        refine ⟨25364897997997529077141193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16909931998665019384760795 25364897997997529077141193)
        ·
          refine ⟨19023673498498146807855895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25364897997997529077141193 19023673498498146807855895)
          ·
            refine ⟨28535510247747220211783843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19023673498498146807855895 28535510247747220211783843)
            ·
              refine ⟨42803265371620830317675765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28535510247747220211783843 42803265371620830317675765)
              ·
                refine ⟨4012806128589452842282103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42803265371620830317675765 4012806128589452842282103)
                ·
                  refine ⟨6019209192884179263423155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4012806128589452842282103 6019209192884179263423155)
                  ·
                    refine ⟨9028813789326268895134733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6019209192884179263423155 9028813789326268895134733)
                    ·
                      refine ⟨3385805170997350835675525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9028813789326268895134733 3385805170997350835675525)
                      ·
                        rfl

theorem cell23_6593832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 5, 1, 1, 3].length) (baseStart_6593832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6593832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6593832 prefixEnd_6593832 := by exact prefixLift 6593832
  have htrace : WordTrace (prefixWord ++ tailWord_6593832) baseStart_6593832 baseEnd_6593832 := by
    simpa [prefixWord, tailWord_6593832, baseEnd_6593832] using wordTrace_append hprefix tailTrace_6593832
  have hstable : (prefixWord ++ tailWord_6593832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6593832).length < 2 ^ (prefixWord ++ tailWord_6593832).sum := by decide
  have hdescent : baseEnd_6593832 < baseStart_6593832 := by decide
  rcases family_descends (prefixWord ++ tailWord_6593832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6593855 : List Nat := [1, 1, 2, 2, 4, 2, 1, 3, 3, 2, 2]
def baseStart_6593855 : Nat := 118140960795 + 6593855 * 2 ^ 59
def prefixEnd_6593855 : Nat := 4983230072969 + 3 ^ 40 * 6593855 * 2
def baseEnd_6593855 : Nat := 3385816981052404245687919

theorem tailTrace_6593855 : CollatzResearch.WordTrace tailWord_6593855 prefixEnd_6593855 3385816981052404245687919 := by
  unfold tailWord_6593855
  simp only [CollatzResearch.WordTrace]
  refine ⟨240497649526596950622463019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160331766351064633748308679 240497649526596950622463019)
  ·
    refine ⟨360746474289895425933694529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240497649526596950622463019 360746474289895425933694529)
    ·
      refine ⟨270559855717421569450270897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 360746474289895425933694529 270559855717421569450270897)
      ·
        refine ⟨202919891788066177087703173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270559855717421569450270897 202919891788066177087703173)
        ·
          refine ⟨38047479710262408203944345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 202919891788066177087703173 38047479710262408203944345)
          ·
            refine ⟨28535609782696806152958259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38047479710262408203944345 28535609782696806152958259)
            ·
              refine ⟨42803414674045209229437389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28535609782696806152958259 42803414674045209229437389)
              ·
                refine ⟨16051280502766953461039021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42803414674045209229437389 16051280502766953461039021)
                ·
                  refine ⟨6019230188537607547889633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16051280502766953461039021 6019230188537607547889633)
                  ·
                    refine ⟨4514422641403205660917225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6019230188537607547889633 4514422641403205660917225)
                    ·
                      refine ⟨3385816981052404245687919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4514422641403205660917225 3385816981052404245687919)
                      ·
                        rfl

theorem cell23_6593855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 3, 3, 2, 2].length) (baseStart_6593855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6593855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6593855 prefixEnd_6593855 := by exact prefixLift 6593855
  have htrace : WordTrace (prefixWord ++ tailWord_6593855) baseStart_6593855 baseEnd_6593855 := by
    simpa [prefixWord, tailWord_6593855, baseEnd_6593855] using wordTrace_append hprefix tailTrace_6593855
  have hstable : (prefixWord ++ tailWord_6593855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6593855).length < 2 ^ (prefixWord ++ tailWord_6593855).sum := by decide
  have hdescent : baseEnd_6593855 < baseStart_6593855 := by decide
  rcases family_descends (prefixWord ++ tailWord_6593855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6593868 : List Nat := [2, 2, 1, 3, 2, 2, 3, 1, 1, 2, 4]
def baseStart_6593868 : Nat := 118140960795 + 6593868 * 2 ^ 59
def prefixEnd_6593868 : Nat := 4983230072969 + 3 ^ 40 * 6593868 * 2
def baseEnd_6593868 : Nat := 3385823656300912694825359

theorem tailTrace_6593868 : CollatzResearch.WordTrace tailWord_6593868 prefixEnd_6593868 3385823656300912694825359 := by
  unfold tailWord_6593868
  simp only [CollatzResearch.WordTrace]
  refine ⟨120249061837774926921343129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160332082450366569228457505 120249061837774926921343129)
  ·
    refine ⟨90186796378331195191007347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120249061837774926921343129 90186796378331195191007347)
    ·
      refine ⟨135280194567496792786511021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90186796378331195191007347 135280194567496792786511021)
      ·
        refine ⟨50730072962811297294941633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135280194567496792786511021 50730072962811297294941633)
        ·
          refine ⟨38047554722108472971206225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50730072962811297294941633 38047554722108472971206225)
          ·
            refine ⟨28535666041581354728404669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38047554722108472971206225 28535666041581354728404669)
            ·
              refine ⟨10700874765593008023151751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28535666041581354728404669 10700874765593008023151751)
              ·
                refine ⟨16051312148389512034727627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10700874765593008023151751 16051312148389512034727627)
                ·
                  refine ⟨24076968222584268052091441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16051312148389512034727627 24076968222584268052091441)
                  ·
                    refine ⟨18057726166938201039068581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24076968222584268052091441 18057726166938201039068581)
                    ·
                      refine ⟨3385823656300912694825359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18057726166938201039068581 3385823656300912694825359)
                      ·
                        rfl

theorem cell23_6593868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 1, 1, 2, 4].length) (baseStart_6593868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6593868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6593868 prefixEnd_6593868 := by exact prefixLift 6593868
  have htrace : WordTrace (prefixWord ++ tailWord_6593868) baseStart_6593868 baseEnd_6593868 := by
    simpa [prefixWord, tailWord_6593868, baseEnd_6593868] using wordTrace_append hprefix tailTrace_6593868
  have hstable : (prefixWord ++ tailWord_6593868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6593868).length < 2 ^ (prefixWord ++ tailWord_6593868).sum := by decide
  have hdescent : baseEnd_6593868 < baseStart_6593868 := by decide
  rcases family_descends (prefixWord ++ tailWord_6593868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6593911 : List Nat := [1, 1, 3, 1, 1, 2, 4, 1, 2, 3, 4]
def baseStart_6593911 : Nat := 118140960795 + 6593911 * 2 ^ 59
def prefixEnd_6593911 : Nat := 4983230072969 + 3 ^ 40 * 6593911 * 2
def baseEnd_6593911 : Nat := 3385845735969056026587661

theorem tailTrace_6593911 : CollatzResearch.WordTrace tailWord_6593911 prefixEnd_6593911 3385845735969056026587661 := by
  unfold tailWord_6593911
  simp only [CollatzResearch.WordTrace]
  refine ⟨240499692014394072186501587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160333128009596048124334391 240499692014394072186501587)
  ·
    refine ⟨360749538021591108279752381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240499692014394072186501587 360749538021591108279752381)
    ·
      refine ⟨135281076758096665604907143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 360749538021591108279752381 135281076758096665604907143)
      ·
        refine ⟨202921615137144998407360715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135281076758096665604907143 202921615137144998407360715)
        ·
          refine ⟨304382422705717497611041073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202921615137144998407360715 304382422705717497611041073)
          ·
            refine ⟨228286817029288123208280805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 304382422705717497611041073 228286817029288123208280805)
            ·
              refine ⟨42803778192991523101552651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 228286817029288123208280805 42803778192991523101552651)
              ·
                refine ⟨64205667289487284652328977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42803778192991523101552651 64205667289487284652328977)
                ·
                  refine ⟨48154250467115463489246733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64205667289487284652328977 48154250467115463489246733)
                  ·
                    refine ⟨18057843925168298808467525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48154250467115463489246733 18057843925168298808467525)
                    ·
                      refine ⟨3385845735969056026587661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18057843925168298808467525 3385845735969056026587661)
                      ·
                        rfl

theorem cell23_6593911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 1, 2, 3, 4].length) (baseStart_6593911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6593911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6593911 prefixEnd_6593911 := by exact prefixLift 6593911
  have htrace : WordTrace (prefixWord ++ tailWord_6593911) baseStart_6593911 baseEnd_6593911 := by
    simpa [prefixWord, tailWord_6593911, baseEnd_6593911] using wordTrace_append hprefix tailTrace_6593911
  have hstable : (prefixWord ++ tailWord_6593911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6593911).length < 2 ^ (prefixWord ++ tailWord_6593911).sum := by decide
  have hdescent : baseEnd_6593911 < baseStart_6593911 := by decide
  rcases family_descends (prefixWord ++ tailWord_6593911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6593931 : List Nat := [1, 1, 1, 1, 4, 3, 1, 1, 4, 1, 5]
def baseStart_6593931 : Nat := 118140960795 + 6593931 * 2 ^ 59
def prefixEnd_6593931 : Nat := 4983230072969 + 3 ^ 40 * 6593931 * 2
def baseEnd_6593931 : Nat := 3385856005582145948337569

theorem tailTrace_6593931 : CollatzResearch.WordTrace tailWord_6593931 prefixEnd_6593931 3385856005582145948337569 := by
  unfold tailWord_6593931
  simp only [CollatzResearch.WordTrace]
  refine ⟨240500421474321615602229647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160333614316214410401486431 240500421474321615602229647)
  ·
    refine ⟨360750632211482423403344471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240500421474321615602229647 360750632211482423403344471)
    ·
      refine ⟨541125948317223635105016707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360750632211482423403344471 541125948317223635105016707)
      ·
        refine ⟨811688922475835452657525061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 541125948317223635105016707 811688922475835452657525061)
        ·
          refine ⟨152191672964219147373285949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 811688922475835452657525061 152191672964219147373285949)
          ·
            refine ⟨57071877361582180264982231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 152191672964219147373285949 57071877361582180264982231)
            ·
              refine ⟨85607816042373270397473347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57071877361582180264982231 85607816042373270397473347)
              ·
                refine ⟨128411724063559905596210021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85607816042373270397473347 128411724063559905596210021)
                ·
                  refine ⟨24077198261917482299289379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 128411724063559905596210021 24077198261917482299289379)
                  ·
                    refine ⟨36115797392876223448934069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24077198261917482299289379 36115797392876223448934069)
                    ·
                      refine ⟨3385856005582145948337569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36115797392876223448934069 3385856005582145948337569)
                      ·
                        rfl

theorem cell23_6593931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 4, 1, 5].length) (baseStart_6593931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6593931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6593931 prefixEnd_6593931 := by exact prefixLift 6593931
  have htrace : WordTrace (prefixWord ++ tailWord_6593931) baseStart_6593931 baseEnd_6593931 := by
    simpa [prefixWord, tailWord_6593931, baseEnd_6593931] using wordTrace_append hprefix tailTrace_6593931
  have hstable : (prefixWord ++ tailWord_6593931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6593931).length < 2 ^ (prefixWord ++ tailWord_6593931).sum := by decide
  have hdescent : baseEnd_6593931 < baseStart_6593931 := by decide
  rcases family_descends (prefixWord ++ tailWord_6593931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6593945 : List Nat := [1, 2, 1, 2, 1, 6, 1, 2, 1, 4, 2]
def baseStart_6593945 : Nat := 118140960795 + 6593945 * 2 ^ 59
def prefixEnd_6593945 : Nat := 4983230072969 + 3 ^ 40 * 6593945 * 2
def baseEnd_6593945 : Nat := 3385863194311308893562505

theorem tailTrace_6593945 : CollatzResearch.WordTrace tailWord_6593945 prefixEnd_6593945 3385863194311308893562505 := by
  unfold tailWord_6593945
  simp only [CollatzResearch.WordTrace]
  refine ⟨240500932096270895993239289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160333954730847263995492859 240500932096270895993239289)
  ·
    refine ⟨180375699072203171994929467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240500932096270895993239289 180375699072203171994929467)
    ·
      refine ⟨270563548608304757992394201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180375699072203171994929467 270563548608304757992394201)
      ·
        refine ⟨202922661456228568494295651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270563548608304757992394201 202922661456228568494295651)
        ·
          refine ⟨304383992184342852741443477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202922661456228568494295651 304383992184342852741443477)
          ·
            refine ⟨14267999633641071222255163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 304383992184342852741443477 14267999633641071222255163)
            ·
              refine ⟨21401999450461606833382745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14267999633641071222255163 21401999450461606833382745)
              ·
                refine ⟨16051499587846205125037059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21401999450461606833382745 16051499587846205125037059)
                ·
                  refine ⟨24077249381769307687555589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16051499587846205125037059 24077249381769307687555589)
                  ·
                    refine ⟨4514484259081745191416673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24077249381769307687555589 4514484259081745191416673)
                    ·
                      refine ⟨3385863194311308893562505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4514484259081745191416673 3385863194311308893562505)
                      ·
                        rfl

theorem cell23_6593945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 2, 1, 4, 2].length) (baseStart_6593945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6593945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6593945 prefixEnd_6593945 := by exact prefixLift 6593945
  have htrace : WordTrace (prefixWord ++ tailWord_6593945) baseStart_6593945 baseEnd_6593945 := by
    simpa [prefixWord, tailWord_6593945, baseEnd_6593945] using wordTrace_append hprefix tailTrace_6593945
  have hstable : (prefixWord ++ tailWord_6593945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6593945).length < 2 ^ (prefixWord ++ tailWord_6593945).sum := by decide
  have hdescent : baseEnd_6593945 < baseStart_6593945 := by decide
  rcases family_descends (prefixWord ++ tailWord_6593945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6593949 : List Nat := [1, 4, 2, 1, 3, 2, 3, 1, 1, 3, 2]
def baseStart_6593949 : Nat := 118140960795 + 6593949 * 2 ^ 59
def prefixEnd_6593949 : Nat := 4983230072969 + 3 ^ 40 * 6593949 * 2
def baseEnd_6593949 : Nat := 3385865248233926877912487

theorem tailTrace_6593949 : CollatzResearch.WordTrace tailWord_6593949 prefixEnd_6593949 3385865248233926877912487 := by
  unfold tailWord_6593949
  simp only [CollatzResearch.WordTrace]
  refine ⟨240501077988256404676384901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160334051992170936450923267 240501077988256404676384901)
  ·
    refine ⟨45093952122798075876822169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 240501077988256404676384901 45093952122798075876822169)
    ·
      refine ⟨33820464092098556907616627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45093952122798075876822169 33820464092098556907616627)
      ·
        refine ⟨50730696138147835361424941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33820464092098556907616627 50730696138147835361424941)
        ·
          refine ⟨19024011051805438260534353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50730696138147835361424941 19024011051805438260534353)
          ·
            refine ⟨14268008288854078695400765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19024011051805438260534353 14268008288854078695400765)
            ·
              refine ⟨5350503108320279510775287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14268008288854078695400765 5350503108320279510775287)
              ·
                refine ⟨8025754662480419266162931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5350503108320279510775287 8025754662480419266162931)
                ·
                  refine ⟨12038631993720628899244397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8025754662480419266162931 12038631993720628899244397)
                  ·
                    refine ⟨4514486997645235837216649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12038631993720628899244397 4514486997645235837216649)
                    ·
                      refine ⟨3385865248233926877912487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4514486997645235837216649 3385865248233926877912487)
                      ·
                        rfl

theorem cell23_6593949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 3, 1, 1, 3, 2].length) (baseStart_6593949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6593949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6593949 prefixEnd_6593949 := by exact prefixLift 6593949
  have htrace : WordTrace (prefixWord ++ tailWord_6593949) baseStart_6593949 baseEnd_6593949 := by
    simpa [prefixWord, tailWord_6593949, baseEnd_6593949] using wordTrace_append hprefix tailTrace_6593949
  have hstable : (prefixWord ++ tailWord_6593949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6593949).length < 2 ^ (prefixWord ++ tailWord_6593949).sum := by decide
  have hdescent : baseEnd_6593949 < baseStart_6593949 := by decide
  rcases family_descends (prefixWord ++ tailWord_6593949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6593965 : List Nat := [1, 5, 2, 2, 1, 1, 1, 1, 2, 4, 3]
def baseStart_6593965 : Nat := 118140960795 + 6593965 * 2 ^ 59
def prefixEnd_6593965 : Nat := 4983230072969 + 3 ^ 40 * 6593965 * 2
def baseEnd_6593965 : Nat := 3385873463924398815312413

theorem tailTrace_6593965 : CollatzResearch.WordTrace tailWord_6593965 prefixEnd_6593965 3385873463924398815312413 := by
  unfold tailWord_6593965
  simp only [CollatzResearch.WordTrace]
  refine ⟨240501661556198439408967349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160334441037465626272644899 240501661556198439408967349)
  ·
    refine ⟨22547030770893603694590689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 240501661556198439408967349 22547030770893603694590689)
    ·
      refine ⟨16910273078170202770943017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22547030770893603694590689 16910273078170202770943017)
      ·
        refine ⟨12682704808627652078207263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16910273078170202770943017 12682704808627652078207263)
        ·
          refine ⟨19024057212941478117310895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12682704808627652078207263 19024057212941478117310895)
          ·
            refine ⟨28536085819412217175966343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19024057212941478117310895 28536085819412217175966343)
            ·
              refine ⟨42804128729118325763949515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28536085819412217175966343 42804128729118325763949515)
              ·
                refine ⟨64206193093677488645924273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42804128729118325763949515 64206193093677488645924273)
                ·
                  refine ⟨48154644820258116484443205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64206193093677488645924273 48154644820258116484443205)
                  ·
                    refine ⟨9028995903798396840833101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48154644820258116484443205 9028995903798396840833101)
                    ·
                      refine ⟨3385873463924398815312413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9028995903798396840833101 3385873463924398815312413)
                      ·
                        rfl

theorem cell23_6593965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_6593965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6593965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6593965 prefixEnd_6593965 := by exact prefixLift 6593965
  have htrace : WordTrace (prefixWord ++ tailWord_6593965) baseStart_6593965 baseEnd_6593965 := by
    simpa [prefixWord, tailWord_6593965, baseEnd_6593965] using wordTrace_append hprefix tailTrace_6593965
  have hstable : (prefixWord ++ tailWord_6593965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6593965).length < 2 ^ (prefixWord ++ tailWord_6593965).sum := by decide
  have hdescent : baseEnd_6593965 < baseStart_6593965 := by decide
  rcases family_descends (prefixWord ++ tailWord_6593965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6594045 : List Nat := [1, 4, 1, 1, 1, 4, 2, 2, 3, 4]
def baseStart_6594045 : Nat := 118140960795 + 6594045 * 2 ^ 59
def prefixEnd_6594045 : Nat := 4983230072969 + 3 ^ 40 * 6594045 * 2
def baseEnd_6594045 : Nat := 1128638180792252834104015

theorem tailTrace_6594045 : CollatzResearch.WordTrace tailWord_6594045 prefixEnd_6594045 1128638180792252834104015 := by
  unfold tailWord_6594045
  simp only [CollatzResearch.WordTrace]
  refine ⟨240504579395908613071879589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160336386263939075381253059 240504579395908613071879589)
  ·
    refine ⟨45094608636732864950977423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 240504579395908613071879589 45094608636732864950977423)
    ·
      refine ⟨67641912955099297426466135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45094608636732864950977423 67641912955099297426466135)
      ·
        refine ⟨101462869432648946139699203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67641912955099297426466135 101462869432648946139699203)
        ·
          refine ⟨152194304148973419209548805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101462869432648946139699203 152194304148973419209548805)
          ·
            refine ⟨28536432027932516101790401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 152194304148973419209548805 28536432027932516101790401)
            ·
              refine ⟨21402324020949387076342801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28536432027932516101790401 21402324020949387076342801)
              ·
                refine ⟨16051743015712040307257101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21402324020949387076342801 16051743015712040307257101)
                ·
                  refine ⟨6019403630892015115221413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16051743015712040307257101 6019403630892015115221413)
                  ·
                    refine ⟨1128638180792252834104015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6019403630892015115221413 1128638180792252834104015)
                    ·
                      rfl

theorem cell23_6594045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 2, 3, 4].length) (baseStart_6594045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6594045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6594045 prefixEnd_6594045 := by exact prefixLift 6594045
  have htrace : WordTrace (prefixWord ++ tailWord_6594045) baseStart_6594045 baseEnd_6594045 := by
    simpa [prefixWord, tailWord_6594045, baseEnd_6594045] using wordTrace_append hprefix tailTrace_6594045
  have hstable : (prefixWord ++ tailWord_6594045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6594045).length < 2 ^ (prefixWord ++ tailWord_6594045).sum := by decide
  have hdescent : baseEnd_6594045 < baseStart_6594045 := by decide
  rcases family_descends (prefixWord ++ tailWord_6594045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6594055 : List Nat := [1, 1, 4, 3, 2, 1, 2, 1, 1, 4, 3]
def baseStart_6594055 : Nat := 118140960795 + 6594055 * 2 ^ 59
def prefixEnd_6594055 : Nat := 4983230072969 + 3 ^ 40 * 6594055 * 2
def baseEnd_6594055 : Nat := 3385919677183303463186999

theorem tailTrace_6594055 : CollatzResearch.WordTrace tailWord_6594055 prefixEnd_6594055 3385919677183303463186999 := by
  unfold tailWord_6594055
  simp only [CollatzResearch.WordTrace]
  refine ⟨240504944125872384779743619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160336629417248256519829079 240504944125872384779743619)
  ·
    refine ⟨360757416188808577169615429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240504944125872384779743619 360757416188808577169615429)
    ·
      refine ⟨67642015535401608219302893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 360757416188808577169615429 67642015535401608219302893)
      ·
        refine ⟨25365755825775603082238585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67642015535401608219302893 25365755825775603082238585)
        ·
          refine ⟨19024316869331702311678939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25365755825775603082238585 19024316869331702311678939)
          ·
            refine ⟨28536475303997553467518409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19024316869331702311678939 28536475303997553467518409)
            ·
              refine ⟨21402356477998165100638807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28536475303997553467518409 21402356477998165100638807)
              ·
                refine ⟨32103534716997247650958211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21402356477998165100638807 32103534716997247650958211)
                ·
                  refine ⟨48155302075495871476437317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32103534716997247650958211 48155302075495871476437317)
                  ·
                    refine ⟨9029119139155475901831997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48155302075495871476437317 9029119139155475901831997)
                    ·
                      refine ⟨3385919677183303463186999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9029119139155475901831997 3385919677183303463186999)
                      ·
                        rfl

theorem cell23_6594055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_6594055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6594055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6594055 prefixEnd_6594055 := by exact prefixLift 6594055
  have htrace : WordTrace (prefixWord ++ tailWord_6594055) baseStart_6594055 baseEnd_6594055 := by
    simpa [prefixWord, tailWord_6594055, baseEnd_6594055] using wordTrace_append hprefix tailTrace_6594055
  have hstable : (prefixWord ++ tailWord_6594055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6594055).length < 2 ^ (prefixWord ++ tailWord_6594055).sum := by decide
  have hdescent : baseEnd_6594055 < baseStart_6594055 := by decide
  rcases family_descends (prefixWord ++ tailWord_6594055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6594058 : List Nat := [3, 1, 2, 2, 2, 2, 1, 2, 8]
def baseStart_6594058 : Nat := 118140960795 + 6594058 * 2 ^ 59
def prefixEnd_6594058 : Nat := 4983230072969 + 3 ^ 40 * 6594058 * 2
def baseEnd_6594058 : Nat := 376213468625029661272165

theorem tailTrace_6594058 : CollatzResearch.WordTrace tailWord_6594058 prefixEnd_6594058 376213468625029661272165 := by
  unfold tailWord_6594058
  simp only [CollatzResearch.WordTrace]
  refine ⟨60126263386215379073025707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160336702363241010861401885 60126263386215379073025707)
  ·
    refine ⟨90189395079323068609538561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60126263386215379073025707 90189395079323068609538561)
    ·
      refine ⟨67642046309492301457153921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90189395079323068609538561 67642046309492301457153921)
      ·
        refine ⟨50731534732119226092865441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67642046309492301457153921 50731534732119226092865441)
        ·
          refine ⟨38048651049089419569649081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50731534732119226092865441 38048651049089419569649081)
          ·
            refine ⟨28536488286817064677236811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38048651049089419569649081 28536488286817064677236811)
            ·
              refine ⟨42804732430225597015855217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28536488286817064677236811 42804732430225597015855217)
              ·
                refine ⟨32103549322669197761891413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42804732430225597015855217 32103549322669197761891413)
                ·
                  refine ⟨376213468625029661272165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32103549322669197761891413 376213468625029661272165)
                  ·
                    rfl

theorem cell23_6594058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 2, 8].length) (baseStart_6594058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6594058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6594058 prefixEnd_6594058 := by exact prefixLift 6594058
  have htrace : WordTrace (prefixWord ++ tailWord_6594058) baseStart_6594058 baseEnd_6594058 := by
    simpa [prefixWord, tailWord_6594058, baseEnd_6594058] using wordTrace_append hprefix tailTrace_6594058
  have hstable : (prefixWord ++ tailWord_6594058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6594058).length < 2 ^ (prefixWord ++ tailWord_6594058).sum := by decide
  have hdescent : baseEnd_6594058 < baseStart_6594058 := by decide
  rcases family_descends (prefixWord ++ tailWord_6594058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6594072 : List Nat := [2, 1, 2, 3, 4, 1, 1, 2, 2, 2, 3]
def baseStart_6594072 : Nat := 118140960795 + 6594072 * 2 ^ 59
def prefixEnd_6594072 : Nat := 4983230072969 + 3 ^ 40 * 6594072 * 2
def baseEnd_6594072 : Nat := 3385928406354429896674421

theorem tailTrace_6594072 : CollatzResearch.WordTrace tailWord_6594072 prefixEnd_6594072 3385928406354429896674421 := by
  unfold tailWord_6594072
  simp only [CollatzResearch.WordTrace]
  refine ⟨120252782083405398341556235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160337042777873864455408313 120252782083405398341556235)
  ·
    refine ⟨180379173125108097512334353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120252782083405398341556235 180379173125108097512334353)
    ·
      refine ⟨135284379843831073134250765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180379173125108097512334353 135284379843831073134250765)
      ·
        refine ⟨50731642441436652425344037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135284379843831073134250765 50731642441436652425344037)
        ·
          refine ⟨9512182957769372329752007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50731642441436652425344037 9512182957769372329752007)
          ·
            refine ⟨14268274436654058494628011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9512182957769372329752007 14268274436654058494628011)
            ·
              refine ⟨21402411654981087741942017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14268274436654058494628011 21402411654981087741942017)
              ·
                refine ⟨16051808741235815806456513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21402411654981087741942017 16051808741235815806456513)
                ·
                  refine ⟨12038856555926861854842385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16051808741235815806456513 12038856555926861854842385)
                  ·
                    refine ⟨9029142416945146391131789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12038856555926861854842385 9029142416945146391131789)
                    ·
                      refine ⟨3385928406354429896674421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9029142416945146391131789 3385928406354429896674421)
                      ·
                        rfl

theorem cell23_6594072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 2, 2, 2, 3].length) (baseStart_6594072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6594072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6594072 prefixEnd_6594072 := by exact prefixLift 6594072
  have htrace : WordTrace (prefixWord ++ tailWord_6594072) baseStart_6594072 baseEnd_6594072 := by
    simpa [prefixWord, tailWord_6594072, baseEnd_6594072] using wordTrace_append hprefix tailTrace_6594072
  have hstable : (prefixWord ++ tailWord_6594072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6594072).length < 2 ^ (prefixWord ++ tailWord_6594072).sum := by decide
  have hdescent : baseEnd_6594072 < baseStart_6594072 := by decide
  rcases family_descends (prefixWord ++ tailWord_6594072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6594105 : List Nat := [1, 2, 1, 5, 1, 3, 1, 1, 3, 5]
def baseStart_6594105 : Nat := 118140960795 + 6594105 * 2 ^ 59
def prefixEnd_6594105 : Nat := 4983230072969 + 3 ^ 40 * 6594105 * 2
def baseEnd_6594105 : Nat := 1128648450405342755853923

theorem tailTrace_6594105 : CollatzResearch.WordTrace tailWord_6594105 prefixEnd_6594105 1128648450405342755853923 := by
  unfold tailWord_6594105
  simp only [CollatzResearch.WordTrace]
  refine ⟨240506767775691243319063769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160337845183794162212709179 240506767775691243319063769)
  ·
    refine ⟨180380075831768432489297827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240506767775691243319063769 180380075831768432489297827)
    ·
      refine ⟨270570113747652648733946741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180380075831768432489297827 270570113747652648733946741)
      ·
        refine ⟨25365948163842435818807507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 270570113747652648733946741 25365948163842435818807507)
        ·
          refine ⟨38048922245763653728211261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25365948163842435818807507 38048922245763653728211261)
          ·
            refine ⟨14268345842161370148079223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38048922245763653728211261 14268345842161370148079223)
            ·
              refine ⟨21402518763242055222118835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14268345842161370148079223 21402518763242055222118835)
              ·
                refine ⟨32103778144863082833178253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21402518763242055222118835 32103778144863082833178253)
                ·
                  refine ⟨12038916804323656062441845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32103778144863082833178253 12038916804323656062441845)
                  ·
                    refine ⟨1128648450405342755853923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12038916804323656062441845 1128648450405342755853923)
                    ·
                      rfl

theorem cell23_6594105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 1, 3, 5].length) (baseStart_6594105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6594105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6594105 prefixEnd_6594105 := by exact prefixLift 6594105
  have htrace : WordTrace (prefixWord ++ tailWord_6594105) baseStart_6594105 baseEnd_6594105 := by
    simpa [prefixWord, tailWord_6594105, baseEnd_6594105] using wordTrace_append hprefix tailTrace_6594105
  have hstable : (prefixWord ++ tailWord_6594105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6594105).length < 2 ^ (prefixWord ++ tailWord_6594105).sum := by decide
  have hdescent : baseEnd_6594105 < baseStart_6594105 := by decide
  rcases family_descends (prefixWord ++ tailWord_6594105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6594122 : List Nat := [3, 1, 2, 1, 1, 3, 5, 1, 1, 5]
def baseStart_6594122 : Nat := 118140960795 + 6594122 * 2 ^ 59
def prefixEnd_6594122 : Nat := 4983230072969 + 3 ^ 40 * 6594122 * 2
def baseEnd_6594122 : Nat := 1128651360129051567016397

theorem tailTrace_6594122 : CollatzResearch.WordTrace tailWord_6594122 prefixEnd_6594122 1128651360129051567016397 := by
  unfold tailWord_6594122
  simp only [CollatzResearch.WordTrace]
  refine ⟨60126846954157413805608155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160338258544419770148288413 60126846954157413805608155)
  ·
    refine ⟨90190270431236120708412233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60126846954157413805608155 90190270431236120708412233)
    ·
      refine ⟨67642702823427090531309175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90190270431236120708412233 67642702823427090531309175)
      ·
        refine ⟨101464054235140635796963763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67642702823427090531309175 101464054235140635796963763)
        ·
          refine ⟨152196081352710953695445645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101464054235140635796963763 152196081352710953695445645)
          ·
            refine ⟨57073530507266607635792117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 152196081352710953695445645 57073530507266607635792117)
            ·
              refine ⟨5350643485056244465855511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57073530507266607635792117 5350643485056244465855511)
              ·
                refine ⟨8025965227584366698783267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5350643485056244465855511 8025965227584366698783267)
                ·
                  refine ⟨12038947841376550048174901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8025965227584366698783267 12038947841376550048174901)
                  ·
                    refine ⟨1128651360129051567016397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12038947841376550048174901 1128651360129051567016397)
                    ·
                      rfl

theorem cell23_6594122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 5, 1, 1, 5].length) (baseStart_6594122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6594122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6594122 prefixEnd_6594122 := by exact prefixLift 6594122
  have htrace : WordTrace (prefixWord ++ tailWord_6594122) baseStart_6594122 baseEnd_6594122 := by
    simpa [prefixWord, tailWord_6594122, baseEnd_6594122] using wordTrace_append hprefix tailTrace_6594122
  have hstable : (prefixWord ++ tailWord_6594122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6594122).length < 2 ^ (prefixWord ++ tailWord_6594122).sum := by decide
  have hdescent : baseEnd_6594122 < baseStart_6594122 := by decide
  rcases family_descends (prefixWord ++ tailWord_6594122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6594138 : List Nat := [3, 1, 1, 2, 1, 1, 1, 3, 3, 1, 6]
def baseStart_6594138 : Nat := 118140960795 + 6594138 * 2 ^ 59
def prefixEnd_6594138 : Nat := 4983230072969 + 3 ^ 40 * 6594138 * 2
def baseEnd_6594138 : Nat := 3385962296077626638449117

theorem tailTrace_6594138 : CollatzResearch.WordTrace tailWord_6594138 prefixEnd_6594138 3385962296077626638449117 := by
  unfold tailWord_6594138
  simp only [CollatzResearch.WordTrace]
  refine ⟨60126992846142922488753767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160338647589714459970010045 60126992846142922488753767)
  ·
    refine ⟨90190489269214383733130651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60126992846142922488753767 90190489269214383733130651)
    ·
      refine ⟨135285733903821575599695977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90190489269214383733130651 135285733903821575599695977)
      ·
        refine ⟨101464300427866181699771983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135285733903821575599695977 101464300427866181699771983)
        ·
          refine ⟨152196450641799272549657975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101464300427866181699771983 152196450641799272549657975)
          ·
            refine ⟨228294675962698908824486963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152196450641799272549657975 228294675962698908824486963)
            ·
              refine ⟨342442013944048363236730445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228294675962698908824486963 342442013944048363236730445)
              ·
                refine ⟨128415755229018136213773917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 342442013944048363236730445 128415755229018136213773917)
                ·
                  refine ⟨48155908210881801080165219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 128415755229018136213773917 48155908210881801080165219)
                  ·
                    refine ⟨72233862316322701620247829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48155908210881801080165219 72233862316322701620247829)
                    ·
                      refine ⟨3385962296077626638449117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72233862316322701620247829 3385962296077626638449117)
                      ·
                        rfl

theorem cell23_6594138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 3, 1, 6].length) (baseStart_6594138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6594138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6594138 prefixEnd_6594138 := by exact prefixLift 6594138
  have htrace : WordTrace (prefixWord ++ tailWord_6594138) baseStart_6594138 baseEnd_6594138 := by
    simpa [prefixWord, tailWord_6594138, baseEnd_6594138] using wordTrace_append hprefix tailTrace_6594138
  have hstable : (prefixWord ++ tailWord_6594138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6594138).length < 2 ^ (prefixWord ++ tailWord_6594138).sum := by decide
  have hdescent : baseEnd_6594138 < baseStart_6594138 := by decide
  rcases family_descends (prefixWord ++ tailWord_6594138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6594145 : List Nat := [1, 2, 3, 1, 1, 3, 1, 1, 5, 2, 3]
def baseStart_6594145 : Nat := 118140960795 + 6594145 * 2 ^ 59
def prefixEnd_6594145 : Nat := 4983230072969 + 3 ^ 40 * 6594145 * 2
def baseEnd_6594145 : Nat := 3385965890442208111061585

theorem tailTrace_6594145 : CollatzResearch.WordTrace tailWord_6594145 prefixEnd_6594145 3385965890442208111061585 := by
  unfold tailWord_6594145
  simp only [CollatzResearch.WordTrace]
  refine ⟨240508226695546330150519889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160338817797030886767013259 240508226695546330150519889)
  ·
    refine ⟨180381170021659747612889917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240508226695546330150519889 180381170021659747612889917)
    ·
      refine ⟨67642938758122405354833719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180381170021659747612889917 67642938758122405354833719)
      ·
        refine ⟨101464408137183608032250579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67642938758122405354833719 101464408137183608032250579)
        ·
          refine ⟨152196612205775412048375869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101464408137183608032250579 152196612205775412048375869)
          ·
            refine ⟨57073729577165779518140951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 152196612205775412048375869 57073729577165779518140951)
            ·
              refine ⟨85610594365748669277211427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57073729577165779518140951 85610594365748669277211427)
              ·
                refine ⟨128415891548623003915817141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85610594365748669277211427 128415891548623003915817141)
                ·
                  refine ⟨12038989832683406617107857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 128415891548623003915817141 12038989832683406617107857)
                  ·
                    refine ⟨9029242374512554962830893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12038989832683406617107857 9029242374512554962830893)
                    ·
                      refine ⟨3385965890442208111061585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9029242374512554962830893 3385965890442208111061585)
                      ·
                        rfl

theorem cell23_6594145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 5, 2, 3].length) (baseStart_6594145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6594145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6594145 prefixEnd_6594145 := by exact prefixLift 6594145
  have htrace : WordTrace (prefixWord ++ tailWord_6594145) baseStart_6594145 baseEnd_6594145 := by
    simpa [prefixWord, tailWord_6594145, baseEnd_6594145] using wordTrace_append hprefix tailTrace_6594145
  have hstable : (prefixWord ++ tailWord_6594145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6594145).length < 2 ^ (prefixWord ++ tailWord_6594145).sum := by decide
  have hdescent : baseEnd_6594145 < baseStart_6594145 := by decide
  rcases family_descends (prefixWord ++ tailWord_6594145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6594152 : List Nat := [2, 1, 4, 3, 1, 2, 2, 1, 1, 6]
def baseStart_6594152 : Nat := 118140960795 + 6594152 * 2 ^ 59
def prefixEnd_6594152 : Nat := 4983230072969 + 3 ^ 40 * 6594152 * 2
def baseEnd_6594152 : Nat := 1128656494935596527891351

theorem tailTrace_6594152 : CollatzResearch.WordTrace tailWord_6594152 prefixEnd_6594152 1128656494935596527891351 := by
  unfold tailWord_6594152
  simp only [CollatzResearch.WordTrace]
  refine ⟨120254241003260485173012355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160338988004347313564016473 120254241003260485173012355)
  ·
    refine ⟨180381361504890727759518533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120254241003260485173012355 180381361504890727759518533)
    ·
      refine ⟨33821505282167011454909725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 180381361504890727759518533 33821505282167011454909725)
      ·
        refine ⟨12683064480812629295591147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33821505282167011454909725 12683064480812629295591147)
        ·
          refine ⟨19024596721218943943386721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12683064480812629295591147 19024596721218943943386721)
          ·
            refine ⟨14268447540914207957540041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19024596721218943943386721 14268447540914207957540041)
            ·
              refine ⟨10701335655685655968155031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14268447540914207957540041 10701335655685655968155031)
              ·
                refine ⟨16052003483528483952232547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10701335655685655968155031 16052003483528483952232547)
                ·
                  refine ⟨24078005225292725928348821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16052003483528483952232547 24078005225292725928348821)
                  ·
                    refine ⟨1128656494935596527891351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24078005225292725928348821 1128656494935596527891351)
                    ·
                      rfl

theorem cell23_6594152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 1, 1, 6].length) (baseStart_6594152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6594152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6594152 prefixEnd_6594152 := by exact prefixLift 6594152
  have htrace : WordTrace (prefixWord ++ tailWord_6594152) baseStart_6594152 baseEnd_6594152 := by
    simpa [prefixWord, tailWord_6594152, baseEnd_6594152] using wordTrace_append hprefix tailTrace_6594152
  have hstable : (prefixWord ++ tailWord_6594152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6594152).length < 2 ^ (prefixWord ++ tailWord_6594152).sum := by decide
  have hdescent : baseEnd_6594152 < baseStart_6594152 := by decide
  rcases family_descends (prefixWord ++ tailWord_6594152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6594162 : List Nat := [3, 2, 1, 2, 3, 1, 2, 1, 3, 2, 3]
def baseStart_6594162 : Nat := 118140960795 + 6594162 * 2 ^ 59
def prefixEnd_6594162 : Nat := 4983230072969 + 3 ^ 40 * 6594162 * 2
def baseEnd_6594162 : Nat := 3385974619613334544549007

theorem tailTrace_6594162 : CollatzResearch.WordTrace tailWord_6594162 prefixEnd_6594162 3385974619613334544549007 := by
  unfold tailWord_6594162
  simp only [CollatzResearch.WordTrace]
  refine ⟨60127211684121185513472185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160339231157656494702592493 60127211684121185513472185)
  ·
    refine ⟨45095408763090889135104139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60127211684121185513472185 45095408763090889135104139)
    ·
      refine ⟨67643113144636333702656209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45095408763090889135104139 67643113144636333702656209)
      ·
        refine ⟨50732334858477250276992157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67643113144636333702656209 50732334858477250276992157)
        ·
          refine ⟨19024625571928968853872059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50732334858477250276992157 19024625571928968853872059)
          ·
            refine ⟨28536938357893453280808089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19024625571928968853872059 28536938357893453280808089)
            ·
              refine ⟨21402703768420089960606067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28536938357893453280808089 21402703768420089960606067)
              ·
                refine ⟨32104055652630134940909101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21402703768420089960606067 32104055652630134940909101)
                ·
                  refine ⟨12039020869736300602840913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32104055652630134940909101 12039020869736300602840913)
                  ·
                    refine ⟨9029265652302225452130685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12039020869736300602840913 9029265652302225452130685)
                    ·
                      refine ⟨3385974619613334544549007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9029265652302225452130685 3385974619613334544549007)
                      ·
                        rfl

theorem cell23_6594162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 1, 3, 2, 3].length) (baseStart_6594162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6594162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6594162 prefixEnd_6594162 := by exact prefixLift 6594162
  have htrace : WordTrace (prefixWord ++ tailWord_6594162) baseStart_6594162 baseEnd_6594162 := by
    simpa [prefixWord, tailWord_6594162, baseEnd_6594162] using wordTrace_append hprefix tailTrace_6594162
  have hstable : (prefixWord ++ tailWord_6594162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6594162).length < 2 ^ (prefixWord ++ tailWord_6594162).sum := by decide
  have hdescent : baseEnd_6594162 < baseStart_6594162 := by decide
  rcases family_descends (prefixWord ++ tailWord_6594162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6594176 : List Nat := [2, 1, 1, 2, 1, 4, 4, 3, 1, 2, 2]
def baseStart_6594176 : Nat := 118140960795 + 6594176 * 2 ^ 59
def prefixEnd_6594176 : Nat := 4983230072969 + 3 ^ 40 * 6594176 * 2
def baseEnd_6594176 : Nat := 3385981808342497489773943

theorem tailTrace_6594176 : CollatzResearch.WordTrace tailWord_6594176 prefixEnd_6594176 3385981808342497489773943 := by
  unfold tailWord_6594176
  simp only [CollatzResearch.WordTrace]
  refine ⟨120254678679217011222449191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160339571572289348296598921 120254678679217011222449191)
  ·
    refine ⟨180382018018825516833673787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120254678679217011222449191 180382018018825516833673787)
    ·
      refine ⟨270573027028238275250510681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180382018018825516833673787 270573027028238275250510681)
      ·
        refine ⟨202929770271178706437883011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270573027028238275250510681 202929770271178706437883011)
        ·
          refine ⟨304394655406768059656824517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202929770271178706437883011 304394655406768059656824517)
          ·
            refine ⟨57073997888769011185654597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 304394655406768059656824517 57073997888769011185654597)
            ·
              refine ⟨10701374604144189597310237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57073997888769011185654597 10701374604144189597310237)
              ·
                refine ⟨4013015476554071098991339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10701374604144189597310237 4013015476554071098991339)
                ·
                  refine ⟨6019523214831106648487009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4013015476554071098991339 6019523214831106648487009)
                  ·
                    refine ⟨4514642411123329986365257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6019523214831106648487009 4514642411123329986365257)
                    ·
                      refine ⟨3385981808342497489773943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4514642411123329986365257 3385981808342497489773943)
                      ·
                        rfl

theorem cell23_6594176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 3, 1, 2, 2].length) (baseStart_6594176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6594176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6594176 prefixEnd_6594176 := by exact prefixLift 6594176
  have htrace : WordTrace (prefixWord ++ tailWord_6594176) baseStart_6594176 baseEnd_6594176 := by
    simpa [prefixWord, tailWord_6594176, baseEnd_6594176] using wordTrace_append hprefix tailTrace_6594176
  have hstable : (prefixWord ++ tailWord_6594176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6594176).length < 2 ^ (prefixWord ++ tailWord_6594176).sum := by decide
  have hdescent : baseEnd_6594176 < baseStart_6594176 := by decide
  rcases family_descends (prefixWord ++ tailWord_6594176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6594209 : List Nat := [1, 2, 3, 3, 2, 3, 1, 1, 1, 3, 3]
def baseStart_6594209 : Nat := 118140960795 + 6594209 * 2 ^ 59
def prefixEnd_6594209 : Nat := 4983230072969 + 3 ^ 40 * 6594209 * 2
def baseEnd_6594209 : Nat := 3385998753204095860661291

theorem tailTrace_6594209 : CollatzResearch.WordTrace tailWord_6594209 prefixEnd_6594209 3385998753204095860661291 := by
  unfold tailWord_6594209
  simp only [CollatzResearch.WordTrace]
  refine ⟨240510560967314469080849681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160340373978209646053899787 240510560967314469080849681)
  ·
    refine ⟨180382920725485851810637261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240510560967314469080849681 180382920725485851810637261)
    ·
      refine ⟨67643595272057194428988973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180382920725485851810637261 67643595272057194428988973)
      ·
        refine ⟨25366348227021447910870865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67643595272057194428988973 25366348227021447910870865)
        ·
          refine ⟨19024761170266085933153149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25366348227021447910870865 19024761170266085933153149)
          ·
            refine ⟨7134285438849782224932431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19024761170266085933153149 7134285438849782224932431)
            ·
              refine ⟨10701428158274673337398647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7134285438849782224932431 10701428158274673337398647)
              ·
                refine ⟨16052142237412010006097971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10701428158274673337398647 16052142237412010006097971)
                ·
                  refine ⟨24078213356118015009146957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16052142237412010006097971 24078213356118015009146957)
                  ·
                    refine ⟨9029330008544255628430109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24078213356118015009146957 9029330008544255628430109)
                    ·
                      refine ⟨3385998753204095860661291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9029330008544255628430109 3385998753204095860661291)
                      ·
                        rfl

theorem cell23_6594209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_6594209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6594209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6594209 prefixEnd_6594209 := by exact prefixLift 6594209
  have htrace : WordTrace (prefixWord ++ tailWord_6594209) baseStart_6594209 baseEnd_6594209 := by
    simpa [prefixWord, tailWord_6594209, baseEnd_6594209] using wordTrace_append hprefix tailTrace_6594209
  have hstable : (prefixWord ++ tailWord_6594209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6594209).length < 2 ^ (prefixWord ++ tailWord_6594209).sum := by decide
  have hdescent : baseEnd_6594209 < baseStart_6594209 := by decide
  rcases family_descends (prefixWord ++ tailWord_6594209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6594232 : List Nat := [2, 1, 2, 1, 2, 1, 1, 6, 1, 4, 2]
def baseStart_6594232 : Nat := 118140960795 + 6594232 * 2 ^ 59
def prefixEnd_6594232 : Nat := 4983230072969 + 3 ^ 40 * 6594232 * 2
def baseEnd_6594232 : Nat := 3386010563259149270673685

theorem tailTrace_6594232 : CollatzResearch.WordTrace tailWord_6594232 prefixEnd_6594232 3386010563259149270673685 := by
  unfold tailWord_6594232
  simp only [CollatzResearch.WordTrace]
  refine ⟨120255699923115572004468475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160340933230820762672624633 120255699923115572004468475)
  ·
    refine ⟨180383549884673358006702713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120255699923115572004468475 180383549884673358006702713)
    ·
      refine ⟨135287662413505018505027035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180383549884673358006702713 135287662413505018505027035)
      ·
        refine ⟨202931493620257527757540553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135287662413505018505027035 202931493620257527757540553)
        ·
          refine ⟨152198620215193145818155415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202931493620257527757540553 152198620215193145818155415)
          ·
            refine ⟨228297930322789718727233123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152198620215193145818155415 228297930322789718727233123)
            ·
              refine ⟨342446895484184578090849685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228297930322789718727233123 342446895484184578090849685)
              ·
                refine ⟨16052198225821152098008579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 342446895484184578090849685 16052198225821152098008579)
                ·
                  refine ⟨24078297338731728147012869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16052198225821152098008579 24078297338731728147012869)
                  ·
                    refine ⟨4514680751012199027564913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24078297338731728147012869 4514680751012199027564913)
                    ·
                      refine ⟨3386010563259149270673685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4514680751012199027564913 3386010563259149270673685)
                      ·
                        rfl

theorem cell23_6594232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 6, 1, 4, 2].length) (baseStart_6594232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6594232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6594232 prefixEnd_6594232 := by exact prefixLift 6594232
  have htrace : WordTrace (prefixWord ++ tailWord_6594232) baseStart_6594232 baseEnd_6594232 := by
    simpa [prefixWord, tailWord_6594232, baseEnd_6594232] using wordTrace_append hprefix tailTrace_6594232
  have hstable : (prefixWord ++ tailWord_6594232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6594232).length < 2 ^ (prefixWord ++ tailWord_6594232).sum := by decide
  have hdescent : baseEnd_6594232 < baseStart_6594232 := by decide
  rcases family_descends (prefixWord ++ tailWord_6594232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6594266 : List Nat := [3, 1, 1, 2, 2, 4, 1, 3, 2, 2, 2]
def baseStart_6594266 : Nat := 118140960795 + 6594266 * 2 ^ 59
def prefixEnd_6594266 : Nat := 4983230072969 + 3 ^ 40 * 6594266 * 2
def baseEnd_6594266 : Nat := 3386028021601402137648529

theorem tailTrace_6594266 : CollatzResearch.WordTrace tailWord_6594266 prefixEnd_6594266 3386028021601402137648529 := by
  unfold tailWord_6594266
  simp only [CollatzResearch.WordTrace]
  refine ⟨60128159982026991953918663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160341759952071978543783101 60128159982026991953918663)
  ·
    refine ⟨90192239973040487930877995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60128159982026991953918663 90192239973040487930877995)
    ·
      refine ⟨135288359959560731896316993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90192239973040487930877995 135288359959560731896316993)
      ·
        refine ⟨101466269969670548922237745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135288359959560731896316993 101466269969670548922237745)
        ·
          refine ⟨76099702477252911691678309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101466269969670548922237745 76099702477252911691678309)
          ·
            refine ⟨14268694214484920942189683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76099702477252911691678309 14268694214484920942189683)
            ·
              refine ⟨21403041321727381413284525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14268694214484920942189683 21403041321727381413284525)
              ·
                refine ⟨8026140495647768029981697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21403041321727381413284525 8026140495647768029981697)
                ·
                  refine ⟨6019605371735826022486273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8026140495647768029981697 6019605371735826022486273)
                  ·
                    refine ⟨4514704028801869516864705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6019605371735826022486273 4514704028801869516864705)
                    ·
                      refine ⟨3386028021601402137648529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4514704028801869516864705 3386028021601402137648529)
                      ·
                        rfl

theorem cell23_6594266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 3, 2, 2, 2].length) (baseStart_6594266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6594266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6594266 prefixEnd_6594266 := by exact prefixLift 6594266
  have htrace : WordTrace (prefixWord ++ tailWord_6594266) baseStart_6594266 baseEnd_6594266 := by
    simpa [prefixWord, tailWord_6594266, baseEnd_6594266] using wordTrace_append hprefix tailTrace_6594266
  have hstable : (prefixWord ++ tailWord_6594266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6594266).length < 2 ^ (prefixWord ++ tailWord_6594266).sum := by decide
  have hdescent : baseEnd_6594266 < baseStart_6594266 := by decide
  rcases family_descends (prefixWord ++ tailWord_6594266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6594295 : List Nat := [1, 1, 3, 1, 1, 1, 5, 2, 1, 2, 5]
def baseStart_6594295 : Nat := 118140960795 + 6594295 * 2 ^ 59
def prefixEnd_6594295 : Nat := 4983230072969 + 3 ^ 40 * 6594295 * 2
def baseEnd_6594295 : Nat := 3386042912540382524185895

theorem tailTrace_6594295 : CollatzResearch.WordTrace tailWord_6594295 prefixEnd_6594295 3386042912540382524185895 := by
  unfold tailWord_6594295
  simp only [CollatzResearch.WordTrace]
  refine ⟨240513697645002905768480339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160342465096668603845653559 240513697645002905768480339)
  ·
    refine ⟨360770546467504358652720509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240513697645002905768480339 360770546467504358652720509)
    ·
      refine ⟨135288954925314134494770191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 360770546467504358652720509 135288954925314134494770191)
      ·
        refine ⟨202933432387971201742155287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135288954925314134494770191 202933432387971201742155287)
        ·
          refine ⟨304400148581956802613232931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202933432387971201742155287 304400148581956802613232931)
          ·
            refine ⟨456600222872935203919849397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 304400148581956802613232931 456600222872935203919849397)
            ·
              refine ⟨42806270894337675367485881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 456600222872935203919849397 42806270894337675367485881)
              ·
                refine ⟨32104703170753256525614411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42806270894337675367485881 32104703170753256525614411)
                ·
                  refine ⟨48157054756129884788421617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32104703170753256525614411 48157054756129884788421617)
                  ·
                    refine ⟨36117791067097413591316213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48157054756129884788421617 36117791067097413591316213)
                    ·
                      refine ⟨3386042912540382524185895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36117791067097413591316213 3386042912540382524185895)
                      ·
                        rfl

theorem cell23_6594295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 2, 1, 2, 5].length) (baseStart_6594295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6594295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6594295 prefixEnd_6594295 := by exact prefixLift 6594295
  have htrace : WordTrace (prefixWord ++ tailWord_6594295) baseStart_6594295 baseEnd_6594295 := by
    simpa [prefixWord, tailWord_6594295, baseEnd_6594295] using wordTrace_append hprefix tailTrace_6594295
  have hstable : (prefixWord ++ tailWord_6594295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6594295).length < 2 ^ (prefixWord ++ tailWord_6594295).sum := by decide
  have hdescent : baseEnd_6594295 < baseStart_6594295 := by decide
  rcases family_descends (prefixWord ++ tailWord_6594295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6594310 : List Nat := [6, 2, 2, 1, 1, 1, 1, 1, 2, 6]
def baseStart_6594310 : Nat := 118140960795 + 6594310 * 2 ^ 59
def prefixEnd_6594310 : Nat := 4983230072969 + 3 ^ 40 * 6594310 * 2
def baseEnd_6594310 : Nat := 1128683538250066655166109

theorem tailTrace_6594310 : CollatzResearch.WordTrace tailWord_6594310 prefixEnd_6594310 1128683538250066655166109 := by
  unfold tailWord_6594310
  simp only [CollatzResearch.WordTrace]
  refine ⟨7516070148123392604071137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 160342829826632375553517589 7516070148123392604071137)
  ·
    refine ⟨5637052611092544453053353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7516070148123392604071137 5637052611092544453053353)
    ·
      refine ⟨4227789458319408339790015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5637052611092544453053353 4227789458319408339790015)
      ·
        refine ⟨6341684187479112509685023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4227789458319408339790015 6341684187479112509685023)
        ·
          refine ⟨9512526281218668764527535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6341684187479112509685023 9512526281218668764527535)
          ·
            refine ⟨14268789421828003146791303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9512526281218668764527535 14268789421828003146791303)
            ·
              refine ⟨21403184132742004720186955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14268789421828003146791303 21403184132742004720186955)
              ·
                refine ⟨32104776199113007080280433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21403184132742004720186955 32104776199113007080280433)
                ·
                  refine ⟨24078582149334755310210325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32104776199113007080280433 24078582149334755310210325)
                  ·
                    refine ⟨1128683538250066655166109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24078582149334755310210325 1128683538250066655166109)
                    ·
                      rfl

theorem cell23_6594310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_6594310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6594310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6594310 prefixEnd_6594310 := by exact prefixLift 6594310
  have htrace : WordTrace (prefixWord ++ tailWord_6594310) baseStart_6594310 baseEnd_6594310 := by
    simpa [prefixWord, tailWord_6594310, baseEnd_6594310] using wordTrace_append hprefix tailTrace_6594310
  have hstable : (prefixWord ++ tailWord_6594310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6594310).length < 2 ^ (prefixWord ++ tailWord_6594310).sum := by decide
  have hdescent : baseEnd_6594310 < baseStart_6594310 := by decide
  rcases family_descends (prefixWord ++ tailWord_6594310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6594317 : List Nat := [1, 7, 2, 1, 1, 1, 2, 1, 1, 4, 2]
def baseStart_6594317 : Nat := 118140960795 + 6594317 * 2 ^ 59
def prefixEnd_6594317 : Nat := 4983230072969 + 3 ^ 40 * 6594317 * 2
def baseEnd_6594317 : Nat := 3386054209114781438110795

theorem tailTrace_6594317 : CollatzResearch.WordTrace tailWord_6594317 prefixEnd_6594317 3386054209114781438110795 := by
  unfold tailWord_6594317
  simp only [CollatzResearch.WordTrace]
  refine ⟨240514500050923203525781205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160343000033948802350520803 240514500050923203525781205)
  ·
    refine ⟨5637058594943512582635497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 240514500050923203525781205 5637058594943512582635497)
    ·
      refine ⟨4227793946207634436976623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5637058594943512582635497 4227793946207634436976623)
      ·
        refine ⟨6341690919311451655464935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4227793946207634436976623 6341690919311451655464935)
        ·
          refine ⟨9512536378967177483197403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6341690919311451655464935 9512536378967177483197403)
          ·
            refine ⟨14268804568450766224796105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9512536378967177483197403 14268804568450766224796105)
            ·
              refine ⟨10701603426338074668597079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14268804568450766224796105 10701603426338074668597079)
              ·
                refine ⟨16052405139507112002895619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10701603426338074668597079 16052405139507112002895619)
                ·
                  refine ⟨24078607709260668004343429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16052405139507112002895619 24078607709260668004343429)
                  ·
                    refine ⟨4514738945486375250814393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24078607709260668004343429 4514738945486375250814393)
                    ·
                      refine ⟨3386054209114781438110795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4514738945486375250814393 3386054209114781438110795)
                      ·
                        rfl

theorem cell23_6594317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_6594317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6594317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6594317 prefixEnd_6594317 := by exact prefixLift 6594317
  have htrace : WordTrace (prefixWord ++ tailWord_6594317) baseStart_6594317 baseEnd_6594317 := by
    simpa [prefixWord, tailWord_6594317, baseEnd_6594317] using wordTrace_append hprefix tailTrace_6594317
  have hstable : (prefixWord ++ tailWord_6594317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6594317).length < 2 ^ (prefixWord ++ tailWord_6594317).sum := by decide
  have hdescent : baseEnd_6594317 < baseStart_6594317 := by decide
  rcases family_descends (prefixWord ++ tailWord_6594317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6594356 : List Nat := [2, 5, 1, 1, 2, 1, 1, 2, 2, 4, 2]
def baseStart_6594356 : Nat := 118140960795 + 6594356 * 2 ^ 59
def prefixEnd_6594356 : Nat := 4983230072969 + 3 ^ 40 * 6594356 * 2
def baseEnd_6594356 : Nat := 3386074234860306785523115

theorem tailTrace_6594356 : CollatzResearch.WordTrace tailWord_6594356 prefixEnd_6594356 3386074234860306785523115 := by
  unfold tailWord_6594356
  simp only [CollatzResearch.WordTrace]
  refine ⟨120257961248890956593225461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160343948331854608790967281 120257961248890956593225461)
  ·
    refine ⟨11274183867083527180614887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 120257961248890956593225461 11274183867083527180614887)
    ·
      refine ⟨16911275800625290770922331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11274183867083527180614887 16911275800625290770922331)
      ·
        refine ⟨25366913700937936156383497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16911275800625290770922331 25366913700937936156383497)
        ·
          refine ⟨19025185275703452117287623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25366913700937936156383497 19025185275703452117287623)
          ·
            refine ⟨28537777913555178175931435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19025185275703452117287623 28537777913555178175931435)
            ·
              refine ⟨42806666870332767263897153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28537777913555178175931435 42806666870332767263897153)
              ·
                refine ⟨32105000152749575447922865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42806666870332767263897153 32105000152749575447922865)
                ·
                  refine ⟨24078750114562181585942149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32105000152749575447922865 24078750114562181585942149)
                  ·
                    refine ⟨4514765646480409047364153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24078750114562181585942149 4514765646480409047364153)
                    ·
                      refine ⟨3386074234860306785523115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4514765646480409047364153 3386074234860306785523115)
                      ·
                        rfl

theorem cell23_6594356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 2, 2, 4, 2].length) (baseStart_6594356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6594356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6594356 prefixEnd_6594356 := by exact prefixLift 6594356
  have htrace : WordTrace (prefixWord ++ tailWord_6594356) baseStart_6594356 baseEnd_6594356 := by
    simpa [prefixWord, tailWord_6594356, baseEnd_6594356] using wordTrace_append hprefix tailTrace_6594356
  have hstable : (prefixWord ++ tailWord_6594356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6594356).length < 2 ^ (prefixWord ++ tailWord_6594356).sum := by decide
  have hdescent : baseEnd_6594356 < baseStart_6594356 := by decide
  rcases family_descends (prefixWord ++ tailWord_6594356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6594362 : List Nat := [3, 1, 1, 1, 5, 2, 1, 1, 8]
def baseStart_6594362 : Nat := 118140960795 + 6594362 * 2 ^ 59
def prefixEnd_6594362 : Nat := 4983230072969 + 3 ^ 40 * 6594362 * 2
def baseEnd_6594362 : Nat := 376230812860470418005343

theorem tailTrace_6594362 : CollatzResearch.WordTrace tailWord_6594362 prefixEnd_6594362 376230812860470418005343 := by
  unfold tailWord_6594362
  simp only [CollatzResearch.WordTrace]
  refine ⟨60129035333940044052792335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160344094223840117474112893 60129035333940044052792335)
  ·
    refine ⟨90193553000910066079188503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60129035333940044052792335 90193553000910066079188503)
    ·
      refine ⟨135290329501365099118782755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90193553000910066079188503 135290329501365099118782755)
      ·
        refine ⟨202935494252047648678174133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135290329501365099118782755 202935494252047648678174133)
        ·
          refine ⟨19025202586129467063578825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 202935494252047648678174133 19025202586129467063578825)
          ·
            refine ⟨14268901939597100297684119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19025202586129467063578825 14268901939597100297684119)
            ·
              refine ⟨21403352909395650446526179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14268901939597100297684119 21403352909395650446526179)
              ·
                refine ⟨32105029364093475669789269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21403352909395650446526179 32105029364093475669789269)
                ·
                  refine ⟨376230812860470418005343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32105029364093475669789269 376230812860470418005343)
                  ·
                    rfl

theorem cell23_6594362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 1, 8].length) (baseStart_6594362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6594362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6594362 prefixEnd_6594362 := by exact prefixLift 6594362
  have htrace : WordTrace (prefixWord ++ tailWord_6594362) baseStart_6594362 baseEnd_6594362 := by
    simpa [prefixWord, tailWord_6594362, baseEnd_6594362] using wordTrace_append hprefix tailTrace_6594362
  have hstable : (prefixWord ++ tailWord_6594362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6594362).length < 2 ^ (prefixWord ++ tailWord_6594362).sum := by decide
  have hdescent : baseEnd_6594362 < baseStart_6594362 := by decide
  rcases family_descends (prefixWord ++ tailWord_6594362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6594366 : List Nat := [4, 2, 1, 2, 2, 2, 2, 1, 3, 4]
def baseStart_6594366 : Nat := 118140960795 + 6594366 * 2 ^ 59
def prefixEnd_6594366 : Nat := 4983230072969 + 3 ^ 40 * 6594366 * 2
def baseEnd_6594366 : Nat := 1128693123222283915466023

theorem tailTrace_6594366 : CollatzResearch.WordTrace tailWord_6594366 prefixEnd_6594366 1128693123222283915466023 := by
  unfold tailWord_6594366
  simp only [CollatzResearch.WordTrace]
  refine ⟨30064535903468210611789369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160344191485163789929543301 30064535903468210611789369)
  ·
    refine ⟨22548401927601157958842027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30064535903468210611789369 22548401927601157958842027)
    ·
      refine ⟨33822602891401736938263041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22548401927601157958842027 33822602891401736938263041)
      ·
        refine ⟨25366952168551302703697281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33822602891401736938263041 25366952168551302703697281)
        ·
          refine ⟨19025214126413477027772961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25366952168551302703697281 19025214126413477027772961)
          ·
            refine ⟨14268910594810107770829721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19025214126413477027772961 14268910594810107770829721)
            ·
              refine ⟨10701682946107580828122291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14268910594810107770829721 10701682946107580828122291)
              ·
                refine ⟨16052524419161371242183437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10701682946107580828122291 16052524419161371242183437)
                ·
                  refine ⟨6019696657185514215818789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16052524419161371242183437 6019696657185514215818789)
                  ·
                    refine ⟨1128693123222283915466023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6019696657185514215818789 1128693123222283915466023)
                    ·
                      rfl

theorem cell23_6594366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 1, 3, 4].length) (baseStart_6594366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6594366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6594366 prefixEnd_6594366 := by exact prefixLift 6594366
  have htrace : WordTrace (prefixWord ++ tailWord_6594366) baseStart_6594366 baseEnd_6594366 := by
    simpa [prefixWord, tailWord_6594366, baseEnd_6594366] using wordTrace_append hprefix tailTrace_6594366
  have hstable : (prefixWord ++ tailWord_6594366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6594366).length < 2 ^ (prefixWord ++ tailWord_6594366).sum := by decide
  have hdescent : baseEnd_6594366 < baseStart_6594366 := by decide
  rcases family_descends (prefixWord ++ tailWord_6594366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6594399 : List Nat := [1, 1, 2, 3, 1, 4, 2, 1, 1, 5, 2]
def baseStart_6594399 : Nat := 118140960795 + 6594399 * 2 ^ 59
def prefixEnd_6594399 : Nat := 4983230072969 + 3 ^ 40 * 6594399 * 2
def baseEnd_6594399 : Nat := 3386096314528450117285417

theorem tailTrace_6594399 : CollatzResearch.WordTrace tailWord_6594399 prefixEnd_6594399 3386096314528450117285417 := by
  unfold tailWord_6594399
  simp only [CollatzResearch.WordTrace]
  refine ⟨240517490836626131530266251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160344993891084087686844167 240517490836626131530266251)
  ·
    refine ⟨360776236254939197295399377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240517490836626131530266251 360776236254939197295399377)
    ·
      refine ⟨270582177191204397971549533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 360776236254939197295399377 270582177191204397971549533)
      ·
        refine ⟨101468316446701649239331075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 270582177191204397971549533 101468316446701649239331075)
        ·
          refine ⟨152202474670052473858996613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101468316446701649239331075 152202474670052473858996613)
          ·
            refine ⟨28537964000634838848561865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 152202474670052473858996613 28537964000634838848561865)
            ·
              refine ⟨21403473000476129136421399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28537964000634838848561865 21403473000476129136421399)
              ·
                refine ⟨32105209500714193704632099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21403473000476129136421399 32105209500714193704632099)
                ·
                  refine ⟨48157814251071290556948149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32105209500714193704632099 48157814251071290556948149)
                  ·
                    refine ⟨4514795086037933489713889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48157814251071290556948149 4514795086037933489713889)
                    ·
                      refine ⟨3386096314528450117285417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4514795086037933489713889 3386096314528450117285417)
                      ·
                        rfl

theorem cell23_6594399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 1, 1, 5, 2].length) (baseStart_6594399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6594399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6594399 prefixEnd_6594399 := by exact prefixLift 6594399
  have htrace : WordTrace (prefixWord ++ tailWord_6594399) baseStart_6594399 baseEnd_6594399 := by
    simpa [prefixWord, tailWord_6594399, baseEnd_6594399] using wordTrace_append hprefix tailTrace_6594399
  have hstable : (prefixWord ++ tailWord_6594399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6594399).length < 2 ^ (prefixWord ++ tailWord_6594399).sum := by decide
  have hdescent : baseEnd_6594399 < baseStart_6594399 := by decide
  rcases family_descends (prefixWord ++ tailWord_6594399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6594432 : List Nat := [2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 5]
def baseStart_6594432 : Nat := 118140960795 + 6594432 * 2 ^ 59
def prefixEnd_6594432 : Nat := 4983230072969 + 3 ^ 40 * 6594432 * 2
def baseEnd_6594432 : Nat := 3386113259390048488172765

theorem tailTrace_6594432 : CollatzResearch.WordTrace tailWord_6594432 prefixEnd_6594432 3386113259390048488172765 := by
  unfold tailWord_6594432
  simp only [CollatzResearch.WordTrace]
  refine ⟨120259347222753289083108775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160345796297004385444145033 120259347222753289083108775)
  ·
    refine ⟨180389020834129933624663163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120259347222753289083108775 180389020834129933624663163)
    ·
      refine ⟨270583531251194900436994745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180389020834129933624663163 270583531251194900436994745)
      ·
        refine ⟨202937648438396175327746059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270583531251194900436994745 202937648438396175327746059)
        ·
          refine ⟨304406472657594262991619089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202937648438396175327746059 304406472657594262991619089)
          ·
            refine ⟨228304854493195697243714317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 304406472657594262991619089 228304854493195697243714317)
            ·
              refine ⟨85614320434948386466392869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 228304854493195697243714317 85614320434948386466392869)
              ·
                refine ⟨16052685081552822462448663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85614320434948386466392869 16052685081552822462448663)
                ·
                  refine ⟨24079027622329233693672995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16052685081552822462448663 24079027622329233693672995)
                  ·
                    refine ⟨36118541433493850540509493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24079027622329233693672995 36118541433493850540509493)
                    ·
                      refine ⟨3386113259390048488172765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36118541433493850540509493 3386113259390048488172765)
                      ·
                        rfl

theorem cell23_6594432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 5].length) (baseStart_6594432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6594432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6594432 prefixEnd_6594432 := by exact prefixLift 6594432
  have htrace : WordTrace (prefixWord ++ tailWord_6594432) baseStart_6594432 baseEnd_6594432 := by
    simpa [prefixWord, tailWord_6594432, baseEnd_6594432] using wordTrace_append hprefix tailTrace_6594432
  have hstable : (prefixWord ++ tailWord_6594432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6594432).length < 2 ^ (prefixWord ++ tailWord_6594432).sum := by decide
  have hdescent : baseEnd_6594432 < baseStart_6594432 := by decide
  rcases family_descends (prefixWord ++ tailWord_6594432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6594456 : List Nat := [2, 1, 2, 6, 1, 1, 1, 2, 1, 6]
def baseStart_6594456 : Nat := 118140960795 + 6594456 * 2 ^ 59
def prefixEnd_6594456 : Nat := 4983230072969 + 3 ^ 40 * 6594456 * 2
def baseEnd_6594456 : Nat := 1128708527641918798090885

theorem tailTrace_6594456 : CollatzResearch.WordTrace tailWord_6594456 prefixEnd_6594456 1128708527641918798090885 := by
  unfold tailWord_6594456
  simp only [CollatzResearch.WordTrace]
  refine ⟨120259784898709815132545611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160346379864946420176727481 120259784898709815132545611)
  ·
    refine ⟨180389677348064722698818417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120259784898709815132545611 180389677348064722698818417)
    ·
      refine ⟨135292258011048542024113813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180389677348064722698818417 135292258011048542024113813)
      ·
        refine ⟨6341824594267900407380335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 135292258011048542024113813 6341824594267900407380335)
        ·
          refine ⟨9512736891401850611070503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6341824594267900407380335 9512736891401850611070503)
          ·
            refine ⟨14269105337102775916605755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9512736891401850611070503 14269105337102775916605755)
            ·
              refine ⟨21403658005654163874908633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14269105337102775916605755 21403658005654163874908633)
              ·
                refine ⟨16052743504240622906181475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21403658005654163874908633 16052743504240622906181475)
                ·
                  refine ⟨24079115256360934359272213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16052743504240622906181475 24079115256360934359272213)
                  ·
                    refine ⟨1128708527641918798090885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24079115256360934359272213 1128708527641918798090885)
                    ·
                      rfl

theorem cell23_6594456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 2, 1, 6].length) (baseStart_6594456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6594456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6594456 prefixEnd_6594456 := by exact prefixLift 6594456
  have htrace : WordTrace (prefixWord ++ tailWord_6594456) baseStart_6594456 baseEnd_6594456 := by
    simpa [prefixWord, tailWord_6594456, baseEnd_6594456] using wordTrace_append hprefix tailTrace_6594456
  have hstable : (prefixWord ++ tailWord_6594456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6594456).length < 2 ^ (prefixWord ++ tailWord_6594456).sum := by decide
  have hdescent : baseEnd_6594456 < baseStart_6594456 := by decide
  rcases family_descends (prefixWord ++ tailWord_6594456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6594463 : List Nat := [1, 1, 2, 5, 3, 1, 3, 1, 1, 1, 4]
def baseStart_6594463 : Nat := 118140960795 + 6594463 * 2 ^ 59
def prefixEnd_6594463 : Nat := 4983230072969 + 3 ^ 40 * 6594463 * 2
def baseEnd_6594463 : Nat := 3386129177290337866885123

theorem tailTrace_6594463 : CollatzResearch.WordTrace tailWord_6594463 prefixEnd_6594463 3386129177290337866885123 := by
  unfold tailWord_6594463
  simp only [CollatzResearch.WordTrace]
  refine ⟨240519825108394270460596043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160346550072262846973730695 240519825108394270460596043)
  ·
    refine ⟨360779737662591405690894065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240519825108394270460596043 360779737662591405690894065)
    ·
      refine ⟨270584803246943554268170549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 360779737662591405690894065 270584803246943554268170549)
      ·
        refine ⟨25367325304400958212640989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 270584803246943554268170549 25367325304400958212640989)
        ·
          refine ⟨9512746989150359329740371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25367325304400958212640989 9512746989150359329740371)
          ·
            refine ⟨14269120483725538994610557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9512746989150359329740371 14269120483725538994610557)
            ·
              refine ⟨5350920181397077122978959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14269120483725538994610557 5350920181397077122978959)
              ·
                refine ⟨8026380272095615684468439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5350920181397077122978959 8026380272095615684468439)
                ·
                  refine ⟨12039570408143423526702659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8026380272095615684468439 12039570408143423526702659)
                  ·
                    refine ⟨18059355612215135290053989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12039570408143423526702659 18059355612215135290053989)
                    ·
                      refine ⟨3386129177290337866885123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18059355612215135290053989 3386129177290337866885123)
                      ·
                        rfl

theorem cell23_6594463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 3, 1, 1, 1, 4].length) (baseStart_6594463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6594463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6594463 prefixEnd_6594463 := by exact prefixLift 6594463
  have htrace : WordTrace (prefixWord ++ tailWord_6594463) baseStart_6594463 baseEnd_6594463 := by
    simpa [prefixWord, tailWord_6594463, baseEnd_6594463] using wordTrace_append hprefix tailTrace_6594463
  have hstable : (prefixWord ++ tailWord_6594463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6594463).length < 2 ^ (prefixWord ++ tailWord_6594463).sum := by decide
  have hdescent : baseEnd_6594463 < baseStart_6594463 := by decide
  rcases family_descends (prefixWord ++ tailWord_6594463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6594496 : List Nat := [2, 1, 1, 2, 3, 2, 1, 5, 2, 1, 3]
def baseStart_6594496 : Nat := 118140960795 + 6594496 * 2 ^ 59
def prefixEnd_6594496 : Nat := 4983230072969 + 3 ^ 40 * 6594496 * 2
def baseEnd_6594496 : Nat := 3386146122151936237772471

theorem tailTrace_6594496 : CollatzResearch.WordTrace tailWord_6594496 prefixEnd_6594496 3386146122151936237772471 := by
  unfold tailWord_6594496
  simp only [CollatzResearch.WordTrace]
  refine ⟨120260514358637358548273671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160347352478183144731031561 120260514358637358548273671)
  ·
    refine ⟨180390771537956037822410507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120260514358637358548273671 180390771537956037822410507)
    ·
      refine ⟨270586157306934056733615761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180390771537956037822410507 270586157306934056733615761)
      ·
        refine ⟨202939617980200542550211821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270586157306934056733615761 202939617980200542550211821)
        ·
          refine ⟨76102356742575203456329433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 202939617980200542550211821 76102356742575203456329433)
          ·
            refine ⟨57076767556931402592247075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76102356742575203456329433 57076767556931402592247075)
            ·
              refine ⟨85615151335397103888370613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57076767556931402592247075 85615151335397103888370613)
              ·
                refine ⟨8026420437693478489534745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85615151335397103888370613 8026420437693478489534745)
                ·
                  refine ⟨6019815328270108867151059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8026420437693478489534745 6019815328270108867151059)
                  ·
                    refine ⟨9029722992405163300726589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6019815328270108867151059 9029722992405163300726589)
                    ·
                      refine ⟨3386146122151936237772471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9029722992405163300726589 3386146122151936237772471)
                      ·
                        rfl

theorem cell23_6594496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 5, 2, 1, 3].length) (baseStart_6594496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6594496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6594496 prefixEnd_6594496 := by exact prefixLift 6594496
  have htrace : WordTrace (prefixWord ++ tailWord_6594496) baseStart_6594496 baseEnd_6594496 := by
    simpa [prefixWord, tailWord_6594496, baseEnd_6594496] using wordTrace_append hprefix tailTrace_6594496
  have hstable : (prefixWord ++ tailWord_6594496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6594496).length < 2 ^ (prefixWord ++ tailWord_6594496).sum := by decide
  have hdescent : baseEnd_6594496 < baseStart_6594496 := by decide
  rcases family_descends (prefixWord ++ tailWord_6594496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6594506 : List Nat := [3, 1, 2, 1, 2, 1, 4, 1, 3, 3, 2]
def baseStart_6594506 : Nat := 118140960795 + 6594506 * 2 ^ 59
def prefixEnd_6594506 : Nat := 4983230072969 + 3 ^ 40 * 6594506 * 2
def baseEnd_6594506 : Nat := 3386151256958481198647425

theorem tailTrace_6594506 : CollatzResearch.WordTrace tailWord_6594506 prefixEnd_6594506 3386151256958481198647425 := by
  unfold tailWord_6594506
  simp only [CollatzResearch.WordTrace]
  refine ⟨60130348361809622201102843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160347595631492325869607581 60130348361809622201102843)
  ·
    refine ⟨90195522542714433301654265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60130348361809622201102843 90195522542714433301654265)
    ·
      refine ⟨67646641907035824976240699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90195522542714433301654265 67646641907035824976240699)
      ·
        refine ⟨101469962860553737464361049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67646641907035824976240699 101469962860553737464361049)
        ·
          refine ⟨76102472145415303098270787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101469962860553737464361049 76102472145415303098270787)
          ·
            refine ⟨114153708218122954647406181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76102472145415303098270787 114153708218122954647406181)
            ·
              refine ⟨21403820290898053996388659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 114153708218122954647406181 21403820290898053996388659)
              ·
                refine ⟨32105730436347080994582989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21403820290898053996388659 32105730436347080994582989)
                ·
                  refine ⟨12039648913630155372968621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32105730436347080994582989 12039648913630155372968621)
                  ·
                    refine ⟨4514868342611308264863233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12039648913630155372968621 4514868342611308264863233)
                    ·
                      refine ⟨3386151256958481198647425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4514868342611308264863233 3386151256958481198647425)
                      ·
                        rfl

theorem cell23_6594506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 1, 3, 3, 2].length) (baseStart_6594506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6594506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6594506 prefixEnd_6594506 := by exact prefixLift 6594506
  have htrace : WordTrace (prefixWord ++ tailWord_6594506) baseStart_6594506 baseEnd_6594506 := by
    simpa [prefixWord, tailWord_6594506, baseEnd_6594506] using wordTrace_append hprefix tailTrace_6594506
  have hstable : (prefixWord ++ tailWord_6594506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6594506).length < 2 ^ (prefixWord ++ tailWord_6594506).sum := by decide
  have hdescent : baseEnd_6594506 < baseStart_6594506 := by decide
  rcases family_descends (prefixWord ++ tailWord_6594506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6594524 : List Nat := [2, 2, 6, 1, 2, 1, 1, 2, 2, 4]
def baseStart_6594524 : Nat := 118140960795 + 6594524 * 2 ^ 59
def prefixEnd_6594524 : Nat := 4983230072969 + 3 ^ 40 * 6594524 * 2
def baseEnd_6594524 : Nat := 1128720166536754042740781

theorem tailTrace_6594524 : CollatzResearch.WordTrace tailWord_6594524 prefixEnd_6594524 1128720166536754042740781 := by
  unfold tailWord_6594524
  simp only [CollatzResearch.WordTrace]
  refine ⟨120261024980586638939283313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160348033307448851919044417 120261024980586638939283313)
  ·
    refine ⟨90195768735439979204462485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120261024980586638939283313 90195768735439979204462485)
    ·
      refine ⟨4227926659473749025209179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 90195768735439979204462485 4227926659473749025209179)
      ·
        refine ⟨6341889989210623537813769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4227926659473749025209179 6341889989210623537813769)
        ·
          refine ⟨4756417491907967653360327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6341889989210623537813769 4756417491907967653360327)
          ·
            refine ⟨7134626237861951480040491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4756417491907967653360327 7134626237861951480040491)
            ·
              refine ⟨10701939356792927220060737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7134626237861951480040491 10701939356792927220060737)
              ·
                refine ⟨8026454517594695415045553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10701939356792927220060737 8026454517594695415045553)
                ·
                  refine ⟨6019840888196021561284165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8026454517594695415045553 6019840888196021561284165)
                  ·
                    refine ⟨1128720166536754042740781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6019840888196021561284165 1128720166536754042740781)
                    ·
                      rfl

theorem cell23_6594524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_6594524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6594524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6594524 prefixEnd_6594524 := by exact prefixLift 6594524
  have htrace : WordTrace (prefixWord ++ tailWord_6594524) baseStart_6594524 baseEnd_6594524 := by
    simpa [prefixWord, tailWord_6594524, baseEnd_6594524] using wordTrace_append hprefix tailTrace_6594524
  have hstable : (prefixWord ++ tailWord_6594524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6594524).length < 2 ^ (prefixWord ++ tailWord_6594524).sum := by decide
  have hdescent : baseEnd_6594524 < baseStart_6594524 := by decide
  rcases family_descends (prefixWord ++ tailWord_6594524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6594530 : List Nat := [3, 3, 3, 1, 2, 1, 1, 1, 4, 1, 3]
def baseStart_6594530 : Nat := 118140960795 + 6594530 * 2 ^ 59
def prefixEnd_6594530 : Nat := 4983230072969 + 3 ^ 40 * 6594530 * 2
def baseEnd_6594530 : Nat := 3386163580494189104747315

theorem tailTrace_6594530 : CollatzResearch.WordTrace tailWord_6594530 prefixEnd_6594530 3386163580494189104747315 := by
  unfold tailWord_6594530
  simp only [CollatzResearch.WordTrace]
  refine ⟨60130567199787885225821261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160348179199434360602190029 60130567199787885225821261)
  ·
    refine ⟨22548962699920456959682973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60130567199787885225821261 22548962699920456959682973)
    ·
      refine ⟨8455861012470171359881115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22548962699920456959682973 8455861012470171359881115)
      ·
        refine ⟨12683791518705257039821673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8455861012470171359881115 12683791518705257039821673)
        ·
          refine ⟨9512843639028942779866255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12683791518705257039821673 9512843639028942779866255)
          ·
            refine ⟨14269265458543414169799383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9512843639028942779866255 14269265458543414169799383)
            ·
              refine ⟨21403898187815121254699075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14269265458543414169799383 21403898187815121254699075)
              ·
                refine ⟨32105847281722681882048613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21403898187815121254699075 32105847281722681882048613)
                ·
                  refine ⟨6019846365323002852884115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32105847281722681882048613 6019846365323002852884115)
                  ·
                    refine ⟨9029769547984504279326173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6019846365323002852884115 9029769547984504279326173)
                    ·
                      refine ⟨3386163580494189104747315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9029769547984504279326173 3386163580494189104747315)
                      ·
                        rfl

theorem cell23_6594530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_6594530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6594530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6594530 prefixEnd_6594530 := by exact prefixLift 6594530
  have htrace : WordTrace (prefixWord ++ tailWord_6594530) baseStart_6594530 baseEnd_6594530 := by
    simpa [prefixWord, tailWord_6594530, baseEnd_6594530] using wordTrace_append hprefix tailTrace_6594530
  have hstable : (prefixWord ++ tailWord_6594530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6594530).length < 2 ^ (prefixWord ++ tailWord_6594530).sum := by decide
  have hdescent : baseEnd_6594530 < baseStart_6594530 := by decide
  rcases family_descends (prefixWord ++ tailWord_6594530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6594553 : List Nat := [1, 2, 1, 3, 1, 6, 1, 1, 1, 4, 2]
def baseStart_6594553 : Nat := 118140960795 + 6594553 * 2 ^ 59
def prefixEnd_6594553 : Nat := 4983230072969 + 3 ^ 40 * 6594553 * 2
def baseEnd_6594553 : Nat := 3386175390549242514759709

theorem tailTrace_6594553 : CollatzResearch.WordTrace tailWord_6594553 prefixEnd_6594553 3386175390549242514759709 := by
  unfold tailWord_6594553
  simp only [CollatzResearch.WordTrace]
  refine ⟨240523107678068215831372313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160348738452045477220914875 240523107678068215831372313)
  ·
    refine ⟨180392330758551161873529235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240523107678068215831372313 180392330758551161873529235)
    ·
      refine ⟨270588496137826742810293853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180392330758551161873529235 270588496137826742810293853)
      ·
        refine ⟨101470686051685028553860195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 270588496137826742810293853 101470686051685028553860195)
        ·
          refine ⟨152206029077527542830790293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101470686051685028553860195 152206029077527542830790293)
          ·
            refine ⟨7134657613009103570193295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 152206029077527542830790293 7134657613009103570193295)
            ·
              refine ⟨10701986419513655355289943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7134657613009103570193295 10701986419513655355289943)
              ·
                refine ⟨16052979629270483032934915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10701986419513655355289943 16052979629270483032934915)
                ·
                  refine ⟨24079469443905724549402373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16052979629270483032934915 24079469443905724549402373)
                  ·
                    refine ⟨4514900520732323353012945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24079469443905724549402373 4514900520732323353012945)
                    ·
                      refine ⟨3386175390549242514759709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4514900520732323353012945 3386175390549242514759709)
                      ·
                        rfl

theorem cell23_6594553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 1, 1, 4, 2].length) (baseStart_6594553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6594553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6594553 prefixEnd_6594553 := by exact prefixLift 6594553
  have htrace : WordTrace (prefixWord ++ tailWord_6594553) baseStart_6594553 baseEnd_6594553 := by
    simpa [prefixWord, tailWord_6594553, baseEnd_6594553] using wordTrace_append hprefix tailTrace_6594553
  have hstable : (prefixWord ++ tailWord_6594553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6594553).length < 2 ^ (prefixWord ++ tailWord_6594553).sum := by decide
  have hdescent : baseEnd_6594553 < baseStart_6594553 := by decide
  rcases family_descends (prefixWord ++ tailWord_6594553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6594593 : List Nat := [1, 2, 3, 2, 5, 1, 1, 1, 7]
def baseStart_6594593 : Nat := 118140960795 + 6594593 * 2 ^ 59
def prefixEnd_6594593 : Nat := 4983230072969 + 3 ^ 40 * 6594593 * 2
def baseEnd_6594593 : Nat := 376243992197269150917725

theorem tailTrace_6594593 : CollatzResearch.WordTrace tailWord_6594593 prefixEnd_6594593 376243992197269150917725 := by
  unfold tailWord_6594593
  simp only [CollatzResearch.WordTrace]
  refine ⟨240524566597923302662828433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160349711065282201775218955 240524566597923302662828433)
  ·
    refine ⟨180393424948442476997121325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240524566597923302662828433 180393424948442476997121325)
    ·
      refine ⟨67647534355665928873920497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180393424948442476997121325 67647534355665928873920497)
      ·
        refine ⟨50735650766749446655440373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67647534355665928873920497 50735650766749446655440373)
        ·
          refine ⟨4756467259382760623947535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50735650766749446655440373 4756467259382760623947535)
          ·
            refine ⟨7134700889074140935921303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4756467259382760623947535 7134700889074140935921303)
            ·
              refine ⟨10702051333611211403881955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7134700889074140935921303 10702051333611211403881955)
              ·
                refine ⟨16053077000416817105822933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10702051333611211403881955 16053077000416817105822933)
                ·
                  refine ⟨376243992197269150917725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16053077000416817105822933 376243992197269150917725)
                  ·
                    rfl

theorem cell23_6594593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 1, 7].length) (baseStart_6594593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6594593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6594593 prefixEnd_6594593 := by exact prefixLift 6594593
  have htrace : WordTrace (prefixWord ++ tailWord_6594593) baseStart_6594593 baseEnd_6594593 := by
    simpa [prefixWord, tailWord_6594593, baseEnd_6594593] using wordTrace_append hprefix tailTrace_6594593
  have hstable : (prefixWord ++ tailWord_6594593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6594593).length < 2 ^ (prefixWord ++ tailWord_6594593).sum := by decide
  have hdescent : baseEnd_6594593 < baseStart_6594593 := by decide
  rcases family_descends (prefixWord ++ tailWord_6594593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6594746 : List Nat := [3, 1, 1, 1, 2, 2, 2, 4, 1, 2, 4]
def baseStart_6594746 : Nat := 118140960795 + 6594746 * 2 ^ 59
def prefixEnd_6594746 : Nat := 4983230072969 + 3 ^ 40 * 6594746 * 2
def baseEnd_6594746 : Nat := 3386274492315560259646321

theorem tailTrace_6594746 : CollatzResearch.WordTrace tailWord_6594746 prefixEnd_6594746 3386274492315560259646321 := by
  unfold tailWord_6594746
  simp only [CollatzResearch.WordTrace]
  refine ⟨60132536741592252448287023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160353431310912673195432061 60132536741592252448287023)
  ·
    refine ⟨90198805112388378672430535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60132536741592252448287023 90198805112388378672430535)
    ·
      refine ⟨135298207668582568008645803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90198805112388378672430535 135298207668582568008645803)
      ·
        refine ⟨202947311502873852012968705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135298207668582568008645803 202947311502873852012968705)
        ·
          refine ⟨152210483627155389009726529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202947311502873852012968705 152210483627155389009726529)
          ·
            refine ⟨114157862720366541757294897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152210483627155389009726529 114157862720366541757294897)
            ·
              refine ⟨85618397040274906317971173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114157862720366541757294897 85618397040274906317971173)
              ·
                refine ⟨16053449445051544934619595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85618397040274906317971173 16053449445051544934619595)
                ·
                  refine ⟨24080174167577317401929393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16053449445051544934619595 24080174167577317401929393)
                  ·
                    refine ⟨18060130625682988051447045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24080174167577317401929393 18060130625682988051447045)
                    ·
                      refine ⟨3386274492315560259646321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18060130625682988051447045 3386274492315560259646321)
                      ·
                        rfl

theorem cell23_6594746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 4, 1, 2, 4].length) (baseStart_6594746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6594746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6594746 prefixEnd_6594746 := by exact prefixLift 6594746
  have htrace : WordTrace (prefixWord ++ tailWord_6594746) baseStart_6594746 baseEnd_6594746 := by
    simpa [prefixWord, tailWord_6594746, baseEnd_6594746] using wordTrace_append hprefix tailTrace_6594746
  have hstable : (prefixWord ++ tailWord_6594746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6594746).length < 2 ^ (prefixWord ++ tailWord_6594746).sum := by decide
  have hdescent : baseEnd_6594746 < baseStart_6594746 := by decide
  rcases family_descends (prefixWord ++ tailWord_6594746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6594754 : List Nat := [3, 5, 1, 1, 1, 2, 1, 2, 2, 3, 2]
def baseStart_6594754 : Nat := 118140960795 + 6594754 * 2 ^ 59
def prefixEnd_6594754 : Nat := 4983230072969 + 3 ^ 40 * 6594754 * 2
def baseEnd_6594754 : Nat := 3386278600160796228346285

theorem tailTrace_6594754 : CollatzResearch.WordTrace tailWord_6594754 prefixEnd_6594754 3386278600160796228346285 := by
  unfold tailWord_6594754
  simp only [CollatzResearch.WordTrace]
  refine ⟨60132609687585006789859829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160353625833560018106292877 60132609687585006789859829)
  ·
    refine ⟨5637432158211094386549359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60132609687585006789859829 5637432158211094386549359)
    ·
      refine ⟨8456148237316641579824039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5637432158211094386549359 8456148237316641579824039)
      ·
        refine ⟨12684222355974962369736059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8456148237316641579824039 12684222355974962369736059)
        ·
          refine ⟨19026333533962443554604089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12684222355974962369736059 19026333533962443554604089)
          ·
            refine ⟨14269750150471832665953067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19026333533962443554604089 14269750150471832665953067)
            ·
              refine ⟨21404625225707748998929601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14269750150471832665953067 21404625225707748998929601)
              ·
                refine ⟨16053468919280811749197201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21404625225707748998929601 16053468919280811749197201)
                ·
                  refine ⟨12040101689460608811897901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16053468919280811749197201 12040101689460608811897901)
                  ·
                    refine ⟨4515038133547728304461713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12040101689460608811897901 4515038133547728304461713)
                    ·
                      refine ⟨3386278600160796228346285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4515038133547728304461713 3386278600160796228346285)
                      ·
                        rfl

theorem cell23_6594754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_6594754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6594754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6594754 prefixEnd_6594754 := by exact prefixLift 6594754
  have htrace : WordTrace (prefixWord ++ tailWord_6594754) baseStart_6594754 baseEnd_6594754 := by
    simpa [prefixWord, tailWord_6594754, baseEnd_6594754] using wordTrace_append hprefix tailTrace_6594754
  have hstable : (prefixWord ++ tailWord_6594754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6594754).length < 2 ^ (prefixWord ++ tailWord_6594754).sum := by decide
  have hdescent : baseEnd_6594754 < baseStart_6594754 := by decide
  rcases family_descends (prefixWord ++ tailWord_6594754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6594756 : List Nat := [2, 3, 3, 1, 2, 1, 11]
def baseStart_6594756 : Nat := 118140960795 + 6594756 * 2 ^ 59
def prefixEnd_6594756 : Nat := 4983230072969 + 3 ^ 40 * 6594756 * 2
def baseEnd_6594756 : Nat := 41805921322495126179275

theorem tailTrace_6594756 : CollatzResearch.WordTrace tailWord_6594756 prefixEnd_6594756 41805921322495126179275 := by
  unfold tailWord_6594756
  simp only [CollatzResearch.WordTrace]
  refine ⟨120265255848166390750506061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160353674464221854334008081 120265255848166390750506061)
  ·
    refine ⟨45099470943062396531439773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120265255848166390750506061 45099470943062396531439773)
    ·
      refine ⟨16912301603648398699289915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45099470943062396531439773 16912301603648398699289915)
      ·
        refine ⟨25368452405472598048934873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16912301603648398699289915 25368452405472598048934873)
        ·
          refine ⟨19026339304104448536701155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25368452405472598048934873 19026339304104448536701155)
          ·
            refine ⟨28539508956156672805051733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19026339304104448536701155 28539508956156672805051733)
            ·
              refine ⟨41805921322495126179275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 28539508956156672805051733 41805921322495126179275)
              ·
                rfl

theorem cell23_6594756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 11].length) (baseStart_6594756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6594756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6594756 prefixEnd_6594756 := by exact prefixLift 6594756
  have htrace : WordTrace (prefixWord ++ tailWord_6594756) baseStart_6594756 baseEnd_6594756 := by
    simpa [prefixWord, tailWord_6594756, baseEnd_6594756] using wordTrace_append hprefix tailTrace_6594756
  have hstable : (prefixWord ++ tailWord_6594756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6594756).length < 2 ^ (prefixWord ++ tailWord_6594756).sum := by decide
  have hdescent : baseEnd_6594756 < baseStart_6594756 := by decide
  rcases family_descends (prefixWord ++ tailWord_6594756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6594773 : List Nat := [1, 3, 2, 4, 2, 1, 2, 8]
def baseStart_6594773 : Nat := 118140960795 + 6594773 * 2 ^ 59
def prefixEnd_6594773 : Nat := 4983230072969 + 3 ^ 40 * 6594773 * 2
def baseEnd_6594773 : Nat := 125418087270119690889211

theorem tailTrace_6594773 : CollatzResearch.WordTrace tailWord_6594773 prefixEnd_6594773 125418087270119690889211 := by
  unfold tailWord_6594773
  simp only [CollatzResearch.WordTrace]
  refine ⟨240531131737271193404380973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160354087824847462269587315 240531131737271193404380973)
  ·
    refine ⟨90199174401476697526642865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 240531131737271193404380973 90199174401476697526642865)
    ·
      refine ⟨67649380801107523144982149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90199174401476697526642865 67649380801107523144982149)
      ·
        refine ⟨12684258900207660589684153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67649380801107523144982149 12684258900207660589684153)
        ·
          refine ⟨9513194175155745442263115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12684258900207660589684153 9513194175155745442263115)
          ·
            refine ⟨14269791262733618163394673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9513194175155745442263115 14269791262733618163394673)
            ·
              refine ⟨10702343447050213622546005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14269791262733618163394673 10702343447050213622546005)
              ·
                refine ⟨125418087270119690889211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10702343447050213622546005 125418087270119690889211)
                ·
                  rfl

theorem cell23_6594773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 8].length) (baseStart_6594773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6594773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6594773 prefixEnd_6594773 := by exact prefixLift 6594773
  have htrace : WordTrace (prefixWord ++ tailWord_6594773) baseStart_6594773 baseEnd_6594773 := by
    simpa [prefixWord, tailWord_6594773, baseEnd_6594773] using wordTrace_append hprefix tailTrace_6594773
  have hstable : (prefixWord ++ tailWord_6594773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6594773).length < 2 ^ (prefixWord ++ tailWord_6594773).sum := by decide
  have hdescent : baseEnd_6594773 < baseStart_6594773 := by decide
  rcases family_descends (prefixWord ++ tailWord_6594773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6594793 : List Nat := [1, 2, 1, 1, 1, 2, 2, 5, 3, 3, 2]
def baseStart_6594793 : Nat := 118140960795 + 6594793 * 2 ^ 59
def prefixEnd_6594793 : Nat := 4983230072969 + 3 ^ 40 * 6594793 * 2
def baseEnd_6594793 : Nat := 3386298625906321575758605

theorem tailTrace_6594793 : CollatzResearch.WordTrace tailWord_6594793 prefixEnd_6594793 3386298625906321575758605 := by
  unfold tailWord_6594793
  simp only [CollatzResearch.WordTrace]
  refine ⟨240531861197198736820109033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160354574131465824546739355 240531861197198736820109033)
  ·
    refine ⟨180398895897899052615081775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240531861197198736820109033 180398895897899052615081775)
    ·
      refine ⟨270598343846848578922622663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180398895897899052615081775 270598343846848578922622663)
      ·
        refine ⟨405897515770272868383933995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270598343846848578922622663 405897515770272868383933995)
        ·
          refine ⟨608846273655409302575900993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 405897515770272868383933995 608846273655409302575900993)
          ·
            refine ⟨456634705241556976931925745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 608846273655409302575900993 456634705241556976931925745)
            ·
              refine ⟨342476028931167732698944309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 456634705241556976931925745 342476028931167732698944309)
              ·
                refine ⟨32107127712296974940526029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 342476028931167732698944309 32107127712296974940526029)
                ·
                  refine ⟨12040172892111365602697261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32107127712296974940526029 12040172892111365602697261)
                  ·
                    refine ⟨4515064834541762101011473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12040172892111365602697261 4515064834541762101011473)
                    ·
                      refine ⟨3386298625906321575758605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4515064834541762101011473 3386298625906321575758605)
                      ·
                        rfl

theorem cell23_6594793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 5, 3, 3, 2].length) (baseStart_6594793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6594793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6594793 prefixEnd_6594793 := by exact prefixLift 6594793
  have htrace : WordTrace (prefixWord ++ tailWord_6594793) baseStart_6594793 baseEnd_6594793 := by
    simpa [prefixWord, tailWord_6594793, baseEnd_6594793] using wordTrace_append hprefix tailTrace_6594793
  have hstable : (prefixWord ++ tailWord_6594793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6594793).length < 2 ^ (prefixWord ++ tailWord_6594793).sum := by decide
  have hdescent : baseEnd_6594793 < baseStart_6594793 := by decide
  rcases family_descends (prefixWord ++ tailWord_6594793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6594818 : List Nat := [3, 4, 1, 1, 2, 3, 2, 2, 1, 2, 2]
def baseStart_6594818 : Nat := 118140960795 + 6594818 * 2 ^ 59
def prefixEnd_6594818 : Nat := 4983230072969 + 3 ^ 40 * 6594818 * 2
def baseEnd_6594818 : Nat := 3386311462922683977945991

theorem tailTrace_6594818 : CollatzResearch.WordTrace tailWord_6594818 prefixEnd_6594818 3386311462922683977945991 := by
  unfold tailWord_6594818
  simp only [CollatzResearch.WordTrace]
  refine ⟨60133193255527041522442277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160355182014738777393179405 60133193255527041522442277)
  ·
    refine ⟨11274973735411320285457927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60133193255527041522442277 11274973735411320285457927)
    ·
      refine ⟨16912460603116980428186891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11274973735411320285457927 16912460603116980428186891)
      ·
        refine ⟨25368690904675470642280337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16912460603116980428186891 25368690904675470642280337)
        ·
          refine ⟨19026518178506602981710253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25368690904675470642280337 19026518178506602981710253)
          ·
            refine ⟨7134944316939976118141345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19026518178506602981710253 7134944316939976118141345)
            ·
              refine ⟨5351208237704982088606009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7134944316939976118141345 5351208237704982088606009)
              ·
                refine ⟨4013406178278736566454507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5351208237704982088606009 4013406178278736566454507)
                ·
                  refine ⟨6020109267418104849681761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4013406178278736566454507 6020109267418104849681761)
                  ·
                    refine ⟨4515081950563578637261321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6020109267418104849681761 4515081950563578637261321)
                    ·
                      refine ⟨3386311462922683977945991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4515081950563578637261321 3386311462922683977945991)
                      ·
                        rfl

theorem cell23_6594818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 2, 2, 1, 2, 2].length) (baseStart_6594818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6594818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6594818 prefixEnd_6594818 := by exact prefixLift 6594818
  have htrace : WordTrace (prefixWord ++ tailWord_6594818) baseStart_6594818 baseEnd_6594818 := by
    simpa [prefixWord, tailWord_6594818, baseEnd_6594818] using wordTrace_append hprefix tailTrace_6594818
  have hstable : (prefixWord ++ tailWord_6594818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6594818).length < 2 ^ (prefixWord ++ tailWord_6594818).sum := by decide
  have hdescent : baseEnd_6594818 < baseStart_6594818 := by decide
  rcases family_descends (prefixWord ++ tailWord_6594818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6594826 : List Nat := [3, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5]
def baseStart_6594826 : Nat := 118140960795 + 6594826 * 2 ^ 59
def prefixEnd_6594826 : Nat := 4983230072969 + 3 ^ 40 * 6594826 * 2
def baseEnd_6594826 : Nat := 3386315570767919946645953

theorem tailTrace_6594826 : CollatzResearch.WordTrace tailWord_6594826 prefixEnd_6594826 3386315570767919946645953 := by
  unfold tailWord_6594826
  simp only [CollatzResearch.WordTrace]
  refine ⟨60133266201519795864015083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160355376537386122304040221 60133266201519795864015083)
  ·
    refine ⟨90199899302279693796022625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60133266201519795864015083 90199899302279693796022625)
    ·
      refine ⟨67649924476709770347016969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90199899302279693796022625 67649924476709770347016969)
      ·
        refine ⟨50737443357532327760262727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67649924476709770347016969 50737443357532327760262727)
        ·
          refine ⟨76106165036298491640394091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50737443357532327760262727 76106165036298491640394091)
          ·
            refine ⟨114159247554447737460591137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76106165036298491640394091 114159247554447737460591137)
            ·
              refine ⟨85619435665835803095443353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114159247554447737460591137 85619435665835803095443353)
              ·
                refine ⟨64214576749376852321582515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85619435665835803095443353 64214576749376852321582515)
                ·
                  refine ⟨96321865124065278482373773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64214576749376852321582515 96321865124065278482373773)
                  ·
                    refine ⟨36120699421524479430890165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 96321865124065278482373773 36120699421524479430890165)
                    ·
                      refine ⟨3386315570767919946645953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36120699421524479430890165 3386315570767919946645953)
                      ·
                        rfl

theorem cell23_6594826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_6594826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6594826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6594826 prefixEnd_6594826 := by exact prefixLift 6594826
  have htrace : WordTrace (prefixWord ++ tailWord_6594826) baseStart_6594826 baseEnd_6594826 := by
    simpa [prefixWord, tailWord_6594826, baseEnd_6594826] using wordTrace_append hprefix tailTrace_6594826
  have hstable : (prefixWord ++ tailWord_6594826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6594826).length < 2 ^ (prefixWord ++ tailWord_6594826).sum := by decide
  have hdescent : baseEnd_6594826 < baseStart_6594826 := by decide
  rcases family_descends (prefixWord ++ tailWord_6594826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6594840 : List Nat := [2, 1, 2, 3, 1, 2, 4, 1, 1, 4, 2]
def baseStart_6594840 : Nat := 118140960795 + 6594840 * 2 ^ 59
def prefixEnd_6594840 : Nat := 4983230072969 + 3 ^ 40 * 6594840 * 2
def baseEnd_6594840 : Nat := 3386322759497082891870889

theorem tailTrace_6594840 : CollatzResearch.WordTrace tailWord_6594840 prefixEnd_6594840 3386322759497082891870889 := by
  unfold tailWord_6594840
  simp only [CollatzResearch.WordTrace]
  refine ⟨120266787714014231923534987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160355716952018975898046649 120266787714014231923534987)
  ·
    refine ⟨180400181571021347885302481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120266787714014231923534987 180400181571021347885302481)
    ·
      refine ⟨135300136178266010913976861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180400181571021347885302481 135300136178266010913976861)
      ·
        refine ⟨50737551066849754092741323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135300136178266010913976861 50737551066849754092741323)
        ·
          refine ⟨76106326600274631139111985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50737551066849754092741323 76106326600274631139111985)
          ·
            refine ⟨57079744950205973354333989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76106326600274631139111985 57079744950205973354333989)
            ·
              refine ⟨10702452178163620003937623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57079744950205973354333989 10702452178163620003937623)
              ·
                refine ⟨16053678267245430005906435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10702452178163620003937623 16053678267245430005906435)
                ·
                  refine ⟨24080517400868145008859653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16053678267245430005906435 24080517400868145008859653)
                  ·
                    refine ⟨4515097012662777189161185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24080517400868145008859653 4515097012662777189161185)
                    ·
                      refine ⟨3386322759497082891870889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4515097012662777189161185 3386322759497082891870889)
                      ·
                        rfl

theorem cell23_6594840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 1, 1, 4, 2].length) (baseStart_6594840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6594840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6594840 prefixEnd_6594840 := by exact prefixLift 6594840
  have htrace : WordTrace (prefixWord ++ tailWord_6594840) baseStart_6594840 baseEnd_6594840 := by
    simpa [prefixWord, tailWord_6594840, baseEnd_6594840] using wordTrace_append hprefix tailTrace_6594840
  have hstable : (prefixWord ++ tailWord_6594840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6594840).length < 2 ^ (prefixWord ++ tailWord_6594840).sum := by decide
  have hdescent : baseEnd_6594840 < baseStart_6594840 := by decide
  rcases family_descends (prefixWord ++ tailWord_6594840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6594863 : List Nat := [1, 1, 2, 1, 2, 1, 5, 5, 5]
def baseStart_6594863 : Nat := 118140960795 + 6594863 * 2 ^ 59
def prefixEnd_6594863 : Nat := 4983230072969 + 3 ^ 40 * 6594863 * 2
def baseEnd_6594863 : Nat := 376259396616904033542587

theorem tailTrace_6594863 : CollatzResearch.WordTrace tailWord_6594863 prefixEnd_6594863 376259396616904033542587 := by
  unfold tailWord_6594863
  simp only [CollatzResearch.WordTrace]
  refine ⟨240534414306945138775157243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160356276204630092516771495 240534414306945138775157243)
  ·
    refine ⟨360801621460417708162735865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240534414306945138775157243 360801621460417708162735865)
    ·
      refine ⟨270601216095313281122051899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 360801621460417708162735865 270601216095313281122051899)
      ·
        refine ⟨405901824142969921683077849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270601216095313281122051899 405901824142969921683077849)
        ·
          refine ⟨304426368107227441262308387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 405901824142969921683077849 304426368107227441262308387)
          ·
            refine ⟨456639552160841161893462581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 304426368107227441262308387 456639552160841161893462581)
            ·
              refine ⟨42809958015078858927512117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 456639552160841161893462581 42809958015078858927512117)
              ·
                refine ⟨4013433563913643024454261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42809958015078858927512117 4013433563913643024454261)
                ·
                  refine ⟨376259396616904033542587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4013433563913643024454261 376259396616904033542587)
                  ·
                    rfl

theorem cell23_6594863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 5, 5].length) (baseStart_6594863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6594863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6594863 prefixEnd_6594863 := by exact prefixLift 6594863
  have htrace : WordTrace (prefixWord ++ tailWord_6594863) baseStart_6594863 baseEnd_6594863 := by
    simpa [prefixWord, tailWord_6594863, baseEnd_6594863] using wordTrace_append hprefix tailTrace_6594863
  have hstable : (prefixWord ++ tailWord_6594863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6594863).length < 2 ^ (prefixWord ++ tailWord_6594863).sum := by decide
  have hdescent : baseEnd_6594863 < baseStart_6594863 := by decide
  rcases family_descends (prefixWord ++ tailWord_6594863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6594874 : List Nat := [3, 1, 1, 1, 4, 4, 1, 2, 2, 2, 2]
def baseStart_6594874 : Nat := 118140960795 + 6594874 * 2 ^ 59
def prefixEnd_6594874 : Nat := 4983230072969 + 3 ^ 40 * 6594874 * 2
def baseEnd_6594874 : Nat := 3386340217839335758845733

theorem tailTrace_6594874 : CollatzResearch.WordTrace tailWord_6594874 prefixEnd_6594874 3386340217839335758845733 := by
  unfold tailWord_6594874
  simp only [CollatzResearch.WordTrace]
  refine ⟨60133703877476321913451919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160356543673270191769205117 60133703877476321913451919)
  ·
    refine ⟨90200555816214482870177879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60133703877476321913451919 90200555816214482870177879)
    ·
      refine ⟨135300833724321724305266819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90200555816214482870177879 135300833724321724305266819)
      ·
        refine ⟨202951250586482586457900229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135300833724321724305266819 202951250586482586457900229)
        ·
          refine ⟨38053359484965484960856293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 202951250586482586457900229 38053359484965484960856293)
          ·
            refine ⟨7135004903431028430160555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38053359484965484960856293 7135004903431028430160555)
            ·
              refine ⟨10702507355146542645240833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7135004903431028430160555 10702507355146542645240833)
              ·
                refine ⟨8026880516359906983930625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10702507355146542645240833 8026880516359906983930625)
                ·
                  refine ⟨6020160387269930237947969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8026880516359906983930625 6020160387269930237947969)
                  ·
                    refine ⟨4515120290452447678460977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6020160387269930237947969 4515120290452447678460977)
                    ·
                      refine ⟨3386340217839335758845733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4515120290452447678460977 3386340217839335758845733)
                      ·
                        rfl

theorem cell23_6594874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 2, 2, 2, 2].length) (baseStart_6594874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6594874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6594874 prefixEnd_6594874 := by exact prefixLift 6594874
  have htrace : WordTrace (prefixWord ++ tailWord_6594874) baseStart_6594874 baseEnd_6594874 := by
    simpa [prefixWord, tailWord_6594874, baseEnd_6594874] using wordTrace_append hprefix tailTrace_6594874
  have hstable : (prefixWord ++ tailWord_6594874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6594874).length < 2 ^ (prefixWord ++ tailWord_6594874).sum := by decide
  have hdescent : baseEnd_6594874 < baseStart_6594874 := by decide
  rcases family_descends (prefixWord ++ tailWord_6594874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6594883 : List Nat := [1, 1, 1, 3, 1, 3, 2, 1, 1, 7, 2]
def baseStart_6594883 : Nat := 118140960795 + 6594883 * 2 ^ 59
def prefixEnd_6594883 : Nat := 4983230072969 + 3 ^ 40 * 6594883 * 2
def baseEnd_6594883 : Nat := 3386344839165226223633191

theorem tailTrace_6594883 : CollatzResearch.WordTrace tailWord_6594883 prefixEnd_6594883 3386344839165226223633191 := by
  unfold tailWord_6594883
  simp only [CollatzResearch.WordTrace]
  refine ⟨240535143766872682190885303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160356762511248454793923535 240535143766872682190885303)
  ·
    refine ⟨360802715650309023286327955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240535143766872682190885303 360802715650309023286327955)
    ·
      refine ⟨541204073475463534929491933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360802715650309023286327955 541204073475463534929491933)
      ·
        refine ⟨202951527553298825598559475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 541204073475463534929491933 202951527553298825598559475)
        ·
          refine ⟨304427291329948238397839213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202951527553298825598559475 304427291329948238397839213)
          ·
            refine ⟨114160234248730589399189705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 304427291329948238397839213 114160234248730589399189705)
            ·
              refine ⟨85620175686547942049392279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114160234248730589399189705 85620175686547942049392279)
              ·
                refine ⟨128430263529821913074088419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85620175686547942049392279 128430263529821913074088419)
                ·
                  refine ⟨192645395294732869611132629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 128430263529821913074088419 192645395294732869611132629)
                  ·
                    refine ⟨4515126452220301631510921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 192645395294732869611132629 4515126452220301631510921)
                    ·
                      refine ⟨3386344839165226223633191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4515126452220301631510921 3386344839165226223633191)
                      ·
                        rfl

theorem cell23_6594883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 7, 2].length) (baseStart_6594883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6594883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6594883 prefixEnd_6594883 := by exact prefixLift 6594883
  have htrace : WordTrace (prefixWord ++ tailWord_6594883) baseStart_6594883 baseEnd_6594883 := by
    simpa [prefixWord, tailWord_6594883, baseEnd_6594883] using wordTrace_append hprefix tailTrace_6594883
  have hstable : (prefixWord ++ tailWord_6594883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6594883).length < 2 ^ (prefixWord ++ tailWord_6594883).sum := by decide
  have hdescent : baseEnd_6594883 < baseStart_6594883 := by decide
  rcases family_descends (prefixWord ++ tailWord_6594883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6594906 : List Nat := [3, 1, 1, 2, 1, 2, 1, 1, 1, 10]
def baseStart_6594906 : Nat := 118140960795 + 6594906 * 2 ^ 59
def prefixEnd_6594906 : Nat := 4983230072969 + 3 ^ 40 * 6594906 * 2
def baseEnd_6594906 : Nat := 1128785549740093211215195

theorem tailTrace_6594906 : CollatzResearch.WordTrace tailWord_6594906 prefixEnd_6594906 1128785549740093211215195 := by
  unfold tailWord_6594906
  simp only [CollatzResearch.WordTrace]
  refine ⟨60133995661447339279743143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160357321763859571412648381 60133995661447339279743143)
  ·
    refine ⟨90200993492171008919614715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60133995661447339279743143 90200993492171008919614715)
    ·
      refine ⟨135301490238256513379422073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90200993492171008919614715 135301490238256513379422073)
      ·
        refine ⟨101476117678692385034566555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135301490238256513379422073 101476117678692385034566555)
        ·
          refine ⟨152214176518038577551849833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101476117678692385034566555 152214176518038577551849833)
          ·
            refine ⟨114160632388528933163887375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152214176518038577551849833 114160632388528933163887375)
            ·
              refine ⟨171240948582793399745831063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114160632388528933163887375 171240948582793399745831063)
              ·
                refine ⟨256861422874190099618746595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171240948582793399745831063 256861422874190099618746595)
                ·
                  refine ⟨385292134311285149428119893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 256861422874190099618746595 385292134311285149428119893)
                  ·
                    refine ⟨1128785549740093211215195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 385292134311285149428119893 1128785549740093211215195)
                    ·
                      rfl

theorem cell23_6594906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 1, 10].length) (baseStart_6594906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6594906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6594906 prefixEnd_6594906 := by exact prefixLift 6594906
  have htrace : WordTrace (prefixWord ++ tailWord_6594906) baseStart_6594906 baseEnd_6594906 := by
    simpa [prefixWord, tailWord_6594906, baseEnd_6594906] using wordTrace_append hprefix tailTrace_6594906
  have hstable : (prefixWord ++ tailWord_6594906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6594906).length < 2 ^ (prefixWord ++ tailWord_6594906).sum := by decide
  have hdescent : baseEnd_6594906 < baseStart_6594906 := by decide
  rcases family_descends (prefixWord ++ tailWord_6594906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6594930 : List Nat := [3, 2, 1, 2, 1, 4, 1, 2, 2, 1, 4]
def baseStart_6594930 : Nat := 118140960795 + 6594930 * 2 ^ 59
def prefixEnd_6594930 : Nat := 4983230072969 + 3 ^ 40 * 6594930 * 2
def baseEnd_6594930 : Nat := 3386368972755987539745475

theorem tailTrace_6594930 : CollatzResearch.WordTrace tailWord_6594930 prefixEnd_6594930 3386368972755987539745475 := by
  unfold tailWord_6594930
  simp only [CollatzResearch.WordTrace]
  refine ⟨60134214499425602304461561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160357905331801606145230829 60134214499425602304461561)
  ·
    refine ⟨45100660874569201728346171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60134214499425602304461561 45100660874569201728346171)
    ·
      refine ⟨67650991311853802592519257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45100660874569201728346171 67650991311853802592519257)
      ·
        refine ⟨50738243483890351944389443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67650991311853802592519257 50738243483890351944389443)
        ·
          refine ⟨76107365225835527916584165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50738243483890351944389443 76107365225835527916584165)
          ·
            refine ⟨14270130979844161484359531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76107365225835527916584165 14270130979844161484359531)
            ·
              refine ⟨21405196469766242226539297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14270130979844161484359531 21405196469766242226539297)
              ·
                refine ⟨16053897352324681669904473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21405196469766242226539297 16053897352324681669904473)
                ·
                  refine ⟨12040423014243511252428355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16053897352324681669904473 12040423014243511252428355)
                  ·
                    refine ⟨18060634521365266878642533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12040423014243511252428355 18060634521365266878642533)
                    ·
                      refine ⟨3386368972755987539745475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18060634521365266878642533 3386368972755987539745475)
                      ·
                        rfl

theorem cell23_6594930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_6594930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6594930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6594930 prefixEnd_6594930 := by exact prefixLift 6594930
  have htrace : WordTrace (prefixWord ++ tailWord_6594930) baseStart_6594930 baseEnd_6594930 := by
    simpa [prefixWord, tailWord_6594930, baseEnd_6594930] using wordTrace_append hprefix tailTrace_6594930
  have hstable : (prefixWord ++ tailWord_6594930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6594930).length < 2 ^ (prefixWord ++ tailWord_6594930).sum := by decide
  have hdescent : baseEnd_6594930 < baseStart_6594930 := by decide
  rcases family_descends (prefixWord ++ tailWord_6594930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6595037 : List Nat := [1, 4, 3, 1, 1, 1, 3, 3, 1, 1, 4]
def baseStart_6595037 : Nat := 118140960795 + 6595037 * 2 ^ 59
def prefixEnd_6595037 : Nat := 4983230072969 + 3 ^ 40 * 6595037 * 2
def baseEnd_6595037 : Nat := 3386423915186018621107483

theorem tailTrace_6595037 : CollatzResearch.WordTrace tailWord_6595037 prefixEnd_6595037 3386423915186018621107483 := by
  unfold tailWord_6595037
  simp only [CollatzResearch.WordTrace]
  refine ⟨240540760608314766491991365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160360507072209844327994243 240540760608314766491991365)
  ·
    refine ⟨45101392614059018717248381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 240540760608314766491991365 45101392614059018717248381)
    ·
      refine ⟨16913022230272132018968143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45101392614059018717248381 16913022230272132018968143)
      ·
        refine ⟨25369533345408198028452215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16913022230272132018968143 25369533345408198028452215)
        ·
          refine ⟨38054300018112297042678323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25369533345408198028452215 38054300018112297042678323)
          ·
            refine ⟨57081450027168445564017485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38054300018112297042678323 57081450027168445564017485)
            ·
              refine ⟨21405543760188167086506557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57081450027168445564017485 21405543760188167086506557)
              ·
                refine ⟨8027078910070562657439959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21405543760188167086506557 8027078910070562657439959)
                ·
                  refine ⟨12040618365105843986159939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8027078910070562657439959 12040618365105843986159939)
                  ·
                    refine ⟨18060927547658765979239909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12040618365105843986159939 18060927547658765979239909)
                    ·
                      refine ⟨3386423915186018621107483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18060927547658765979239909 3386423915186018621107483)
                      ·
                        rfl

theorem cell23_6595037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_6595037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6595037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6595037 prefixEnd_6595037 := by exact prefixLift 6595037
  have htrace : WordTrace (prefixWord ++ tailWord_6595037) baseStart_6595037 baseEnd_6595037 := by
    simpa [prefixWord, tailWord_6595037, baseEnd_6595037] using wordTrace_append hprefix tailTrace_6595037
  have hstable : (prefixWord ++ tailWord_6595037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6595037).length < 2 ^ (prefixWord ++ tailWord_6595037).sum := by decide
  have hdescent : baseEnd_6595037 < baseStart_6595037 := by decide
  rcases family_descends (prefixWord ++ tailWord_6595037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6595054 : List Nat := [4, 1, 2, 1, 2, 2, 1, 3, 3, 2, 2]
def baseStart_6595054 : Nat := 118140960795 + 6595054 * 2 ^ 59
def prefixEnd_6595054 : Nat := 4983230072969 + 3 ^ 40 * 6595054 * 2
def baseEnd_6595054 : Nat := 3386432644357145054594905

theorem tailTrace_6595054 : CollatzResearch.WordTrace tailWord_6595054 prefixEnd_6595054 3386432644357145054594905 := by
  unfold tailWord_6595054
  simp only [CollatzResearch.WordTrace]
  refine ⟨30067672581156647299420027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160360920432835452263573477 30067672581156647299420027)
  ·
    refine ⟨45101508871734970949130041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30067672581156647299420027 45101508871734970949130041)
    ·
      refine ⟨33826131653801228211847531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45101508871734970949130041 33826131653801228211847531)
      ·
        refine ⟨50739197480701842317771297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33826131653801228211847531 50739197480701842317771297)
        ·
          refine ⟨38054398110526381738328473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50739197480701842317771297 38054398110526381738328473)
          ·
            refine ⟨28540798582894786303746355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38054398110526381738328473 28540798582894786303746355)
            ·
              refine ⟨42811197874342179455619533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28540798582894786303746355 42811197874342179455619533)
              ·
                refine ⟨16054199202878317295857325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42811197874342179455619533 16054199202878317295857325)
                ·
                  refine ⟨6020324701079368985946497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16054199202878317295857325 6020324701079368985946497)
                  ·
                    refine ⟨4515243525809526739459873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6020324701079368985946497 4515243525809526739459873)
                    ·
                      refine ⟨3386432644357145054594905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4515243525809526739459873 3386432644357145054594905)
                      ·
                        rfl

theorem cell23_6595054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 3, 3, 2, 2].length) (baseStart_6595054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6595054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6595054 prefixEnd_6595054 := by exact prefixLift 6595054
  have htrace : WordTrace (prefixWord ++ tailWord_6595054) baseStart_6595054 baseEnd_6595054 := by
    simpa [prefixWord, tailWord_6595054, baseEnd_6595054] using wordTrace_append hprefix tailTrace_6595054
  have hstable : (prefixWord ++ tailWord_6595054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6595054).length < 2 ^ (prefixWord ++ tailWord_6595054).sum := by decide
  have hdescent : baseEnd_6595054 < baseStart_6595054 := by decide
  rcases family_descends (prefixWord ++ tailWord_6595054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6595127 : List Nat := [1, 1, 3, 1, 2, 3, 2, 3, 1, 4, 2]
def baseStart_6595127 : Nat := 118140960795 + 6595127 * 2 ^ 59
def prefixEnd_6595127 : Nat := 4983230072969 + 3 ^ 40 * 6595127 * 2
def baseEnd_6595127 : Nat := 3386470128444923268982069

theorem tailTrace_6595127 : CollatzResearch.WordTrace tailWord_6595127 prefixEnd_6595127 3386470128444923268982069 := by
  unfold tailWord_6595127
  simp only [CollatzResearch.WordTrace]
  refine ⟨240544043177988711862767635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160362695451992474575178423 240544043177988711862767635)
  ·
    refine ⟨360816064766983067794151453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240544043177988711862767635 360816064766983067794151453)
    ·
      refine ⟨135306024287618650422806795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 360816064766983067794151453 135306024287618650422806795)
      ·
        refine ⟨202959036431427975634210193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135306024287618650422806795 202959036431427975634210193)
        ·
          refine ⟨152219277323570981725657645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202959036431427975634210193 152219277323570981725657645)
          ·
            refine ⟨57082228996339118147121617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 152219277323570981725657645 57082228996339118147121617)
            ·
              refine ⟨42811671747254338610341213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57082228996339118147121617 42811671747254338610341213)
              ·
                refine ⟨16054376905220376978877955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42811671747254338610341213 16054376905220376978877955)
                ·
                  refine ⟨24081565357830565468316933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16054376905220376978877955 24081565357830565468316933)
                  ·
                    refine ⟨4515293504593231025309425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24081565357830565468316933 4515293504593231025309425)
                    ·
                      refine ⟨3386470128444923268982069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4515293504593231025309425 3386470128444923268982069)
                      ·
                        rfl

theorem cell23_6595127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 3, 1, 4, 2].length) (baseStart_6595127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6595127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6595127 prefixEnd_6595127 := by exact prefixLift 6595127
  have htrace : WordTrace (prefixWord ++ tailWord_6595127) baseStart_6595127 baseEnd_6595127 := by
    simpa [prefixWord, tailWord_6595127, baseEnd_6595127] using wordTrace_append hprefix tailTrace_6595127
  have hstable : (prefixWord ++ tailWord_6595127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6595127).length < 2 ^ (prefixWord ++ tailWord_6595127).sum := by decide
  have hdescent : baseEnd_6595127 < baseStart_6595127 := by decide
  rcases family_descends (prefixWord ++ tailWord_6595127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6595130 : List Nat := [3, 1, 1, 1, 3, 3, 1, 2, 2, 1, 5]
def baseStart_6595130 : Nat := 118140960795 + 6595130 * 2 ^ 59
def prefixEnd_6595130 : Nat := 4983230072969 + 3 ^ 40 * 6595130 * 2
def baseEnd_6595130 : Nat := 3386471668886886757244555

theorem tailTrace_6595130 : CollatzResearch.WordTrace tailWord_6595130 prefixEnd_6595130 3386471668886886757244555 := by
  unfold tailWord_6595130
  simp only [CollatzResearch.WordTrace]
  refine ⟨60136038149244460843781711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160362768397985228916751229 60136038149244460843781711)
  ·
    refine ⟨90204057223866691265672567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60136038149244460843781711 90204057223866691265672567)
    ·
      refine ⟨135306085835800036898508851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90204057223866691265672567 135306085835800036898508851)
      ·
        refine ⟨202959128753700055347763277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135306085835800036898508851 202959128753700055347763277)
        ·
          refine ⟨76109673282637520755411229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 202959128753700055347763277 76109673282637520755411229)
          ·
            refine ⟨28541127480989070283279211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76109673282637520755411229 28541127480989070283279211)
            ·
              refine ⟨42811691221483605424918817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28541127480989070283279211 42811691221483605424918817)
              ·
                refine ⟨32108768416112704068689113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42811691221483605424918817 32108768416112704068689113)
                ·
                  refine ⟨24081576312084528051516835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32108768416112704068689113 24081576312084528051516835)
                  ·
                    refine ⟨36122364468126792077275253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24081576312084528051516835 36122364468126792077275253)
                    ·
                      refine ⟨3386471668886886757244555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36122364468126792077275253 3386471668886886757244555)
                      ·
                        rfl

theorem cell23_6595130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 2, 2, 1, 5].length) (baseStart_6595130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6595130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6595130 prefixEnd_6595130 := by exact prefixLift 6595130
  have htrace : WordTrace (prefixWord ++ tailWord_6595130) baseStart_6595130 baseEnd_6595130 := by
    simpa [prefixWord, tailWord_6595130, baseEnd_6595130] using wordTrace_append hprefix tailTrace_6595130
  have hstable : (prefixWord ++ tailWord_6595130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6595130).length < 2 ^ (prefixWord ++ tailWord_6595130).sum := by decide
  have hdescent : baseEnd_6595130 < baseStart_6595130 := by decide
  rcases family_descends (prefixWord ++ tailWord_6595130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6595180 : List Nat := [2, 2, 1, 1, 3, 1, 2, 2, 4, 5]
def baseStart_6595180 : Nat := 118140960795 + 6595180 * 2 ^ 59
def prefixEnd_6595180 : Nat := 4983230072969 + 3 ^ 40 * 6595180 * 2
def baseEnd_6595180 : Nat := 1128832447639870520539775

theorem tailTrace_6595180 : CollatzResearch.WordTrace tailWord_6595180 prefixEnd_6595180 1128832447639870520539775 := by
  unfold tailWord_6595180
  simp only [CollatzResearch.WordTrace]
  refine ⟨120272988123398350957223497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160363984164531134609631329 120272988123398350957223497)
  ·
    refine ⟨90204741092548763217917623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120272988123398350957223497 90204741092548763217917623)
    ·
      refine ⟨135307111638823144826876435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90204741092548763217917623 135307111638823144826876435)
      ·
        refine ⟨202960667458234717240314653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135307111638823144826876435 202960667458234717240314653)
        ·
          refine ⟨76110250296838018965117995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 202960667458234717240314653 76110250296838018965117995)
          ·
            refine ⟨114165375445257028447676993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76110250296838018965117995 114165375445257028447676993)
            ·
              refine ⟨85624031583942771335757745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114165375445257028447676993 85624031583942771335757745)
              ·
                refine ⟨64218023687957078501818309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85624031583942771335757745 64218023687957078501818309)
                ·
                  refine ⟨12040879441491952219090933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64218023687957078501818309 12040879441491952219090933)
                  ·
                    refine ⟨1128832447639870520539775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12040879441491952219090933 1128832447639870520539775)
                    ·
                      rfl

theorem cell23_6595180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 5].length) (baseStart_6595180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6595180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6595180 prefixEnd_6595180 := by exact prefixLift 6595180
  have htrace : WordTrace (prefixWord ++ tailWord_6595180) baseStart_6595180 baseEnd_6595180 := by
    simpa [prefixWord, tailWord_6595180, baseEnd_6595180] using wordTrace_append hprefix tailTrace_6595180
  have hstable : (prefixWord ++ tailWord_6595180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6595180).length < 2 ^ (prefixWord ++ tailWord_6595180).sum := by decide
  have hdescent : baseEnd_6595180 < baseStart_6595180 := by decide
  rcases family_descends (prefixWord ++ tailWord_6595180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6595197 : List Nat := [1, 4, 1, 1, 5, 1, 1, 1, 1, 7]
def baseStart_6595197 : Nat := 118140960795 + 6595197 * 2 ^ 59
def prefixEnd_6595197 : Nat := 4983230072969 + 3 ^ 40 * 6595197 * 2
def baseEnd_6595197 : Nat := 1128835357363579331702249

theorem tailTrace_6595197 : CollatzResearch.WordTrace tailWord_6595197 prefixEnd_6595197 1128835357363579331702249 := by
  unfold tailWord_6595197
  simp only [CollatzResearch.WordTrace]
  refine ⟨240546596287735113817815845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160364397525156742545210563 240546596287735113817815845)
  ·
    refine ⟨45102486803950333840840471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 240546596287735113817815845 45102486803950333840840471)
    ·
      refine ⟨67653730205925500761260707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45102486803950333840840471 67653730205925500761260707)
      ·
        refine ⟨101480595308888251141891061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67653730205925500761260707 101480595308888251141891061)
        ·
          refine ⟨9513805810208273544552287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 101480595308888251141891061 9513805810208273544552287)
          ·
            refine ⟨14270708715312410316828431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9513805810208273544552287 14270708715312410316828431)
            ·
              refine ⟨21406063072968615475242647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14270708715312410316828431 21406063072968615475242647)
              ·
                refine ⟨32109094609452923212863971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21406063072968615475242647 32109094609452923212863971)
                ·
                  refine ⟨48163641914179384819295957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32109094609452923212863971 48163641914179384819295957)
                  ·
                    refine ⟨1128835357363579331702249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48163641914179384819295957 1128835357363579331702249)
                    ·
                      rfl

theorem cell23_6595197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 1, 1, 7].length) (baseStart_6595197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6595197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6595197 prefixEnd_6595197 := by exact prefixLift 6595197
  have htrace : WordTrace (prefixWord ++ tailWord_6595197) baseStart_6595197 baseEnd_6595197 := by
    simpa [prefixWord, tailWord_6595197, baseEnd_6595197] using wordTrace_append hprefix tailTrace_6595197
  have hstable : (prefixWord ++ tailWord_6595197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6595197).length < 2 ^ (prefixWord ++ tailWord_6595197).sum := by decide
  have hdescent : baseEnd_6595197 < baseStart_6595197 := by decide
  rcases family_descends (prefixWord ++ tailWord_6595197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6595261 : List Nat := [1, 4, 1, 2, 1, 3, 3, 3, 1, 4]
def baseStart_6595261 : Nat := 118140960795 + 6595261 * 2 ^ 59
def prefixEnd_6595261 : Nat := 4983230072969 + 3 ^ 40 * 6595261 * 2
def baseEnd_6595261 : Nat := 1128846311617541914902151

theorem tailTrace_6595261 : CollatzResearch.WordTrace tailWord_6595261 prefixEnd_6595261 1128846311617541914902151 := by
  unfold tailWord_6595261
  simp only [CollatzResearch.WordTrace]
  refine ⟨240548930559503252748145637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160365953706335501832097091 240548930559503252748145637)
  ·
    refine ⟨45102924479906859890277307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 240548930559503252748145637 45102924479906859890277307)
    ·
      refine ⟨67654386719860289835415961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45102924479906859890277307 67654386719860289835415961)
      ·
        refine ⟨50740790039895217376561971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67654386719860289835415961 50740790039895217376561971)
        ·
          refine ⟨76111185059842826064842957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50740790039895217376561971 76111185059842826064842957)
          ·
            refine ⟨28541694397441059774316109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76111185059842826064842957 28541694397441059774316109)
            ·
              refine ⟨10703135399040397415368541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28541694397441059774316109 10703135399040397415368541)
              ·
                refine ⟨4013675774640149030763203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10703135399040397415368541 4013675774640149030763203)
                ·
                  refine ⟨6020513661960223546144805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4013675774640149030763203 6020513661960223546144805)
                  ·
                    refine ⟨1128846311617541914902151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6020513661960223546144805 1128846311617541914902151)
                    ·
                      rfl

theorem cell23_6595261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 3, 1, 4].length) (baseStart_6595261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6595261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6595261 prefixEnd_6595261 := by exact prefixLift 6595261
  have htrace : WordTrace (prefixWord ++ tailWord_6595261) baseStart_6595261 baseEnd_6595261 := by
    simpa [prefixWord, tailWord_6595261, baseEnd_6595261] using wordTrace_append hprefix tailTrace_6595261
  have hstable : (prefixWord ++ tailWord_6595261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6595261).length < 2 ^ (prefixWord ++ tailWord_6595261).sum := by decide
  have hdescent : baseEnd_6595261 < baseStart_6595261 := by decide
  rcases family_descends (prefixWord ++ tailWord_6595261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6595278 : List Nat := [4, 1, 1, 1, 3, 3, 3, 2, 1, 4]
def baseStart_6595278 : Nat := 118140960795 + 6595278 * 2 ^ 59
def prefixEnd_6595278 : Nat := 4983230072969 + 3 ^ 40 * 6595278 * 2
def baseEnd_6595278 : Nat := 1128849221341250726064625

theorem tailTrace_6595278 : CollatzResearch.WordTrace tailWord_6595278 prefixEnd_6595278 1128849221341250726064625 := by
  unfold tailWord_6595278
  simp only [CollatzResearch.WordTrace]
  refine ⟨30068693825055208081439311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160366367066961109767676325 30068693825055208081439311)
  ·
    refine ⟨45103040737582812122158967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30068693825055208081439311 45103040737582812122158967)
    ·
      refine ⟨67654561106374218183238451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45103040737582812122158967 67654561106374218183238451)
      ·
        refine ⟨101481841659561327274857677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67654561106374218183238451 101481841659561327274857677)
        ·
          refine ⟨38055690622335497728071629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101481841659561327274857677 38055690622335497728071629)
          ·
            refine ⟨14270883983375811648026861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38055690622335497728071629 14270883983375811648026861)
            ·
              refine ⟨5351581493765929368010073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14270883983375811648026861 5351581493765929368010073)
              ·
                refine ⟨4013686120324447026007555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5351581493765929368010073 4013686120324447026007555)
                ·
                  refine ⟨6020529180486670539011333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4013686120324447026007555 6020529180486670539011333)
                  ·
                    refine ⟨1128849221341250726064625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6020529180486670539011333 1128849221341250726064625)
                    ·
                      rfl

theorem cell23_6595278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 3, 2, 1, 4].length) (baseStart_6595278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6595278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6595278 prefixEnd_6595278 := by exact prefixLift 6595278
  have htrace : WordTrace (prefixWord ++ tailWord_6595278) baseStart_6595278 baseEnd_6595278 := by
    simpa [prefixWord, tailWord_6595278, baseEnd_6595278] using wordTrace_append hprefix tailTrace_6595278
  have hstable : (prefixWord ++ tailWord_6595278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6595278).length < 2 ^ (prefixWord ++ tailWord_6595278).sum := by decide
  have hdescent : baseEnd_6595278 < baseStart_6595278 := by decide
  rcases family_descends (prefixWord ++ tailWord_6595278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6595304 : List Nat := [2, 1, 4, 1, 4, 1, 1, 1, 3, 5]
def baseStart_6595304 : Nat := 118140960795 + 6595304 * 2 ^ 59
def prefixEnd_6595304 : Nat := 4983230072969 + 3 ^ 40 * 6595304 * 2
def baseEnd_6595304 : Nat := 1128853671506923025489585

theorem tailTrace_6595304 : CollatzResearch.WordTrace tailWord_6595304 prefixEnd_6595304 1128853671506923025489585 := by
  unfold tailWord_6595304
  simp only [CollatzResearch.WordTrace]
  refine ⟨120275249449173735545980483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160366999265564980727973977 120275249449173735545980483)
  ·
    refine ⟨180412874173760603318970725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120275249449173735545980483 180412874173760603318970725)
    ·
      refine ⟨33827413907580113122307011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 180412874173760603318970725 33827413907580113122307011)
      ·
        refine ⟨50741120861370169683460517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33827413907580113122307011 50741120861370169683460517)
        ·
          refine ⟨9513960161506906815648847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50741120861370169683460517 9513960161506906815648847)
          ·
            refine ⟨14270940242260360223473271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9513960161506906815648847 14270940242260360223473271)
            ·
              refine ⟨21406410363390540335209907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14270940242260360223473271 21406410363390540335209907)
              ·
                refine ⟨32109615545085810502814861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21406410363390540335209907 32109615545085810502814861)
                ·
                  refine ⟨12041105829407178938555573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32109615545085810502814861 12041105829407178938555573)
                  ·
                    refine ⟨1128853671506923025489585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12041105829407178938555573 1128853671506923025489585)
                    ·
                      rfl

theorem cell23_6595304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 1, 3, 5].length) (baseStart_6595304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6595304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6595304 prefixEnd_6595304 := by exact prefixLift 6595304
  have htrace : WordTrace (prefixWord ++ tailWord_6595304) baseStart_6595304 baseEnd_6595304 := by
    simpa [prefixWord, tailWord_6595304, baseEnd_6595304] using wordTrace_append hprefix tailTrace_6595304
  have hstable : (prefixWord ++ tailWord_6595304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6595304).length < 2 ^ (prefixWord ++ tailWord_6595304).sum := by decide
  have hdescent : baseEnd_6595304 < baseStart_6595304 := by decide
  rcases family_descends (prefixWord ++ tailWord_6595304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6595311 : List Nat := [1, 1, 2, 1, 5, 3, 2, 1, 2, 3, 2]
def baseStart_6595311 : Nat := 118140960795 + 6595311 * 2 ^ 59
def prefixEnd_6595311 : Nat := 4983230072969 + 3 ^ 40 * 6595311 * 2
def baseEnd_6595311 : Nat := 3386564608885350549081223

theorem tailTrace_6595311 : CollatzResearch.WordTrace tailWord_6595311 prefixEnd_6595311 3386564608885350549081223 := by
  unfold tailWord_6595311
  simp only [CollatzResearch.WordTrace]
  refine ⟨240550754209322111287465787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160367169472881407524977191 240550754209322111287465787)
  ·
    refine ⟨360826131313983166931198681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240550754209322111287465787 360826131313983166931198681)
    ·
      refine ⟨270619598485487375198399011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 360826131313983166931198681 270619598485487375198399011)
      ·
        refine ⟨405929397728231062797598517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270619598485487375198399011 405929397728231062797598517)
        ·
          refine ⟨38055881037021662137274861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 405929397728231062797598517 38055881037021662137274861)
          ·
            refine ⟨14270955388883123301478073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38055881037021662137274861 14270955388883123301478073)
            ·
              refine ⟨10703216541662342476108555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14270955388883123301478073 10703216541662342476108555)
              ·
                refine ⟨16054824812493513714162833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10703216541662342476108555 16054824812493513714162833)
                ·
                  refine ⟨12041118609370135285622125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16054824812493513714162833 12041118609370135285622125)
                  ·
                    refine ⟨4515419478513800732108297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12041118609370135285622125 4515419478513800732108297)
                    ·
                      refine ⟨3386564608885350549081223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4515419478513800732108297 3386564608885350549081223)
                      ·
                        rfl

theorem cell23_6595311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 1, 2, 3, 2].length) (baseStart_6595311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6595311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6595311 prefixEnd_6595311 := by exact prefixLift 6595311
  have htrace : WordTrace (prefixWord ++ tailWord_6595311) baseStart_6595311 baseEnd_6595311 := by
    simpa [prefixWord, tailWord_6595311, baseEnd_6595311] using wordTrace_append hprefix tailTrace_6595311
  have hstable : (prefixWord ++ tailWord_6595311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6595311).length < 2 ^ (prefixWord ++ tailWord_6595311).sum := by decide
  have hdescent : baseEnd_6595311 < baseStart_6595311 := by decide
  rcases family_descends (prefixWord ++ tailWord_6595311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6595318 : List Nat := [5, 1, 1, 1, 1, 2, 2, 5, 1, 1, 3]
def baseStart_6595318 : Nat := 118140960795 + 6595318 * 2 ^ 59
def prefixEnd_6595318 : Nat := 4983230072969 + 3 ^ 40 * 6595318 * 2
def baseEnd_6595318 : Nat := 3386568203249932021693691

theorem tailTrace_6595318 : CollatzResearch.WordTrace tailWord_6595318 prefixEnd_6595318 3386568203249932021693691 := by
  unfold tailWord_6595318
  simp only [CollatzResearch.WordTrace]
  refine ⟨15034438095018546967685663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 160367339680197834321980405 15034438095018546967685663)
  ·
    refine ⟨22551657142527820451528495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15034438095018546967685663 22551657142527820451528495)
    ·
      refine ⟨33827485713791730677292743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22551657142527820451528495 33827485713791730677292743)
      ·
        refine ⟨50741228570687596015939115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33827485713791730677292743 50741228570687596015939115)
        ·
          refine ⟨76111842856031394023908673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50741228570687596015939115 76111842856031394023908673)
          ·
            refine ⟨57083882142023545517931505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76111842856031394023908673 57083882142023545517931505)
            ·
              refine ⟨42812911606517659138448629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57083882142023545517931505 42812911606517659138448629)
              ·
                refine ⟨4013710463111030544229559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42812911606517659138448629 4013710463111030544229559)
                ·
                  refine ⟨6020565694666545816344339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4013710463111030544229559 6020565694666545816344339)
                  ·
                    refine ⟨9030848541999818724516509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6020565694666545816344339 9030848541999818724516509)
                    ·
                      refine ⟨3386568203249932021693691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9030848541999818724516509 3386568203249932021693691)
                      ·
                        rfl

theorem cell23_6595318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 5, 1, 1, 3].length) (baseStart_6595318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6595318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6595318 prefixEnd_6595318 := by exact prefixLift 6595318
  have htrace : WordTrace (prefixWord ++ tailWord_6595318) baseStart_6595318 baseEnd_6595318 := by
    simpa [prefixWord, tailWord_6595318, baseEnd_6595318] using wordTrace_append hprefix tailTrace_6595318
  have hstable : (prefixWord ++ tailWord_6595318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6595318).length < 2 ^ (prefixWord ++ tailWord_6595318).sum := by decide
  have hdescent : baseEnd_6595318 < baseStart_6595318 := by decide
  rcases family_descends (prefixWord ++ tailWord_6595318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6595335 : List Nat := [1, 1, 4, 4, 1, 1, 4, 2, 1, 1, 3]
def baseStart_6595335 : Nat := 118140960795 + 6595335 * 2 ^ 59
def prefixEnd_6595335 : Nat := 4983230072969 + 3 ^ 40 * 6595335 * 2
def baseEnd_6595335 : Nat := 3386576932421058455181113

theorem tailTrace_6595335 : CollatzResearch.WordTrace tailWord_6595335 prefixEnd_6595335 3386576932421058455181113 := by
  unfold tailWord_6595335
  simp only [CollatzResearch.WordTrace]
  refine ⟨240551629561235163386339459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160367753040823442257559639 240551629561235163386339459)
  ·
    refine ⟨360827444341852745079509189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240551629561235163386339459 360827444341852745079509189)
    ·
      refine ⟨67655145814097389702407973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 360827444341852745079509189 67655145814097389702407973)
      ·
        refine ⟨12685339840143260569201495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67655145814097389702407973 12685339840143260569201495)
        ·
          refine ⟨19028009760214890853802243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12685339840143260569201495 19028009760214890853802243)
          ·
            refine ⟨28542014640322336280703365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19028009760214890853802243 28542014640322336280703365)
            ·
              refine ⟨5351627745060438052631881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28542014640322336280703365 5351627745060438052631881)
              ·
                refine ⟨4013720808795328539473911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5351627745060438052631881 4013720808795328539473911)
                ·
                  refine ⟨6020581213192992809210867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4013720808795328539473911 6020581213192992809210867)
                  ·
                    refine ⟨9030871819789489213816301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6020581213192992809210867 9030871819789489213816301)
                    ·
                      refine ⟨3386576932421058455181113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9030871819789489213816301 3386576932421058455181113)
                      ·
                        rfl

theorem cell23_6595335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_6595335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6595335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6595335 prefixEnd_6595335 := by exact prefixLift 6595335
  have htrace : WordTrace (prefixWord ++ tailWord_6595335) baseStart_6595335 baseEnd_6595335 := by
    simpa [prefixWord, tailWord_6595335, baseEnd_6595335] using wordTrace_append hprefix tailTrace_6595335
  have hstable : (prefixWord ++ tailWord_6595335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6595335).length < 2 ^ (prefixWord ++ tailWord_6595335).sum := by decide
  have hdescent : baseEnd_6595335 < baseStart_6595335 := by decide
  rcases family_descends (prefixWord ++ tailWord_6595335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6595354 : List Nat := [3, 1, 1, 3, 2, 1, 4, 1, 1, 2, 4]
def baseStart_6595354 : Nat := 118140960795 + 6595354 * 2 ^ 59
def prefixEnd_6595354 : Nat := 4983230072969 + 3 ^ 40 * 6595354 * 2
def baseEnd_6595354 : Nat := 3386586688553493880843525

theorem tailTrace_6595354 : CollatzResearch.WordTrace tailWord_6595354 prefixEnd_6595354 3386586688553493880843525 := by
  unfold tailWord_6595354
  simp only [CollatzResearch.WordTrace]
  refine ⟨60138080637041582407820279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160368215032110886420854077 60138080637041582407820279)
  ·
    refine ⟨90207120955562373611730419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60138080637041582407820279 90207120955562373611730419)
    ·
      refine ⟨135310681433343560417595629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90207120955562373611730419 135310681433343560417595629)
      ·
        refine ⟨50741505537503835156598361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135310681433343560417595629 50741505537503835156598361)
        ·
          refine ⟨38056129153127876367448771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50741505537503835156598361 38056129153127876367448771)
          ·
            refine ⟨57084193729691814551173157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38056129153127876367448771 57084193729691814551173157)
            ·
              refine ⟨10703286324317215228344967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57084193729691814551173157 10703286324317215228344967)
              ·
                refine ⟨16054929486475822842517451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10703286324317215228344967 16054929486475822842517451)
                ·
                  refine ⟨24082394229713734263776177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16054929486475822842517451 24082394229713734263776177)
                  ·
                    refine ⟨18061795672285300697832133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24082394229713734263776177 18061795672285300697832133)
                    ·
                      refine ⟨3386586688553493880843525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18061795672285300697832133 3386586688553493880843525)
                      ·
                        rfl

theorem cell23_6595354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 1, 1, 2, 4].length) (baseStart_6595354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6595354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6595354 prefixEnd_6595354 := by exact prefixLift 6595354
  have htrace : WordTrace (prefixWord ++ tailWord_6595354) baseStart_6595354 baseEnd_6595354 := by
    simpa [prefixWord, tailWord_6595354, baseEnd_6595354] using wordTrace_append hprefix tailTrace_6595354
  have hstable : (prefixWord ++ tailWord_6595354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6595354).length < 2 ^ (prefixWord ++ tailWord_6595354).sum := by decide
  have hdescent : baseEnd_6595354 < baseStart_6595354 := by decide
  rcases family_descends (prefixWord ++ tailWord_6595354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6595391 : List Nat := [1, 1, 2, 2, 5, 2, 1, 1, 4, 1, 3]
def baseStart_6595391 : Nat := 118140960795 + 6595391 * 2 ^ 59
def prefixEnd_6595391 : Nat := 4983230072969 + 3 ^ 40 * 6595391 * 2
def baseEnd_6595391 : Nat := 3386605687337710236080855

theorem tailTrace_6595391 : CollatzResearch.WordTrace tailWord_6595391 prefixEnd_6595391 3386605687337710236080855 := by
  unfold tailWord_6595391
  simp only [CollatzResearch.WordTrace]
  refine ⟨240553672049032284950378027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160369114699354856633585351 240553672049032284950378027)
  ·
    refine ⟨360830508073548427425567041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240553672049032284950378027 360830508073548427425567041)
    ·
      refine ⟨270622881055161320569175281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 360830508073548427425567041 270622881055161320569175281)
      ·
        refine ⟨202967160791370990426881461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270622881055161320569175281 202967160791370990426881461)
        ·
          refine ⟨19028171324191030352520137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 202967160791370990426881461 19028171324191030352520137)
          ·
            refine ⟨14271128493143272764390103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19028171324191030352520137 14271128493143272764390103)
            ·
              refine ⟨21406692739714909146585155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14271128493143272764390103 21406692739714909146585155)
              ·
                refine ⟨32110039109572363719877733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21406692739714909146585155 32110039109572363719877733)
                ·
                  refine ⟨6020632333044818197477075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32110039109572363719877733 6020632333044818197477075)
                  ·
                    refine ⟨9030948499567227296215613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6020632333044818197477075 9030948499567227296215613)
                    ·
                      refine ⟨3386605687337710236080855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9030948499567227296215613 3386605687337710236080855)
                      ·
                        rfl

theorem cell23_6595391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 1, 4, 1, 3].length) (baseStart_6595391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6595391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6595391 prefixEnd_6595391 := by exact prefixLift 6595391
  have htrace : WordTrace (prefixWord ++ tailWord_6595391) baseStart_6595391 baseEnd_6595391 := by
    simpa [prefixWord, tailWord_6595391, baseEnd_6595391] using wordTrace_append hprefix tailTrace_6595391
  have hstable : (prefixWord ++ tailWord_6595391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6595391).length < 2 ^ (prefixWord ++ tailWord_6595391).sum := by decide
  have hdescent : baseEnd_6595391 < baseStart_6595391 := by decide
  rcases family_descends (prefixWord ++ tailWord_6595391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6595397 : List Nat := [1, 3, 1, 1, 1, 2, 2, 3, 2, 3, 4]
def baseStart_6595397 : Nat := 118140960795 + 6595397 * 2 ^ 59
def prefixEnd_6595397 : Nat := 4983230072969 + 3 ^ 40 * 6595397 * 2
def baseEnd_6595397 : Nat := 3386608768221637212605827

theorem tailTrace_6595397 : CollatzResearch.WordTrace tailWord_6595397 prefixEnd_6595397 3386608768221637212605827 := by
  unfold tailWord_6595397
  simp only [CollatzResearch.WordTrace]
  refine ⟨240553890887010547975096445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160369260591340365316730963 240553890887010547975096445)
  ·
    refine ⟨90207709082628955490661167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 240553890887010547975096445 90207709082628955490661167)
    ·
      refine ⟨135311563623943433235991751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90207709082628955490661167 135311563623943433235991751)
      ·
        refine ⟨202967345435915149853987627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135311563623943433235991751 202967345435915149853987627)
        ·
          refine ⟨304451018153872724780981441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202967345435915149853987627 304451018153872724780981441)
          ·
            refine ⟨228338263615404543585736081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 304451018153872724780981441 228338263615404543585736081)
            ·
              refine ⟨171253697711553407689302061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228338263615404543585736081 171253697711553407689302061)
              ·
                refine ⟨64220136641832527883488273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 171253697711553407689302061 64220136641832527883488273)
                ·
                  refine ⟨48165102481374395912616205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64220136641832527883488273 48165102481374395912616205)
                  ·
                    refine ⟨18061913430515398467231077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48165102481374395912616205 18061913430515398467231077)
                    ·
                      refine ⟨3386608768221637212605827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18061913430515398467231077 3386608768221637212605827)
                      ·
                        rfl

theorem cell23_6595397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 2, 3, 4].length) (baseStart_6595397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6595397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6595397 prefixEnd_6595397 := by exact prefixLift 6595397
  have htrace : WordTrace (prefixWord ++ tailWord_6595397) baseStart_6595397 baseEnd_6595397 := by
    simpa [prefixWord, tailWord_6595397, baseEnd_6595397] using wordTrace_append hprefix tailTrace_6595397
  have hstable : (prefixWord ++ tailWord_6595397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6595397).length < 2 ^ (prefixWord ++ tailWord_6595397).sum := by decide
  have hdescent : baseEnd_6595397 < baseStart_6595397 := by decide
  rcases family_descends (prefixWord ++ tailWord_6595397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6595405 : List Nat := [1, 6, 1, 2, 3, 1, 1, 1, 1, 2, 4]
def baseStart_6595405 : Nat := 118140960795 + 6595405 * 2 ^ 59
def prefixEnd_6595405 : Nat := 4983230072969 + 3 ^ 40 * 6595405 * 2
def baseEnd_6595405 : Nat := 3386612876066873181305791

theorem tailTrace_6595405 : CollatzResearch.WordTrace tailWord_6595405 prefixEnd_6595405 3386612876066873181305791 := by
  unfold tailWord_6595405
  simp only [CollatzResearch.WordTrace]
  refine ⟨240554182670981565341387669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160369455113987710227591779 240554182670981565341387669)
  ·
    refine ⟨11275977312702260875377547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 240554182670981565341387669 11275977312702260875377547)
    ·
      refine ⟨16913965969053391313066321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11275977312702260875377547 16913965969053391313066321)
      ·
        refine ⟨12685474476790043484799741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16913965969053391313066321 12685474476790043484799741)
        ·
          refine ⟨4757052928796266306799903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12685474476790043484799741 4757052928796266306799903)
          ·
            refine ⟨7135579393194399460199855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4757052928796266306799903 7135579393194399460199855)
            ·
              refine ⟨10703369089791599190299783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7135579393194399460199855 10703369089791599190299783)
              ·
                refine ⟨16055053634687398785449675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10703369089791599190299783 16055053634687398785449675)
                ·
                  refine ⟨24082580452031098178174513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16055053634687398785449675 24082580452031098178174513)
                  ·
                    refine ⟨18061935339023323633630885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24082580452031098178174513 18061935339023323633630885)
                    ·
                      refine ⟨3386612876066873181305791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18061935339023323633630885 3386612876066873181305791)
                      ·
                        rfl

theorem cell23_6595405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_6595405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6595405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6595405 prefixEnd_6595405 := by exact prefixLift 6595405
  have htrace : WordTrace (prefixWord ++ tailWord_6595405) baseStart_6595405 baseEnd_6595405 := by
    simpa [prefixWord, tailWord_6595405, baseEnd_6595405] using wordTrace_append hprefix tailTrace_6595405
  have hstable : (prefixWord ++ tailWord_6595405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6595405).length < 2 ^ (prefixWord ++ tailWord_6595405).sum := by decide
  have hdescent : baseEnd_6595405 < baseStart_6595405 := by decide
  rcases family_descends (prefixWord ++ tailWord_6595405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6595418 : List Nat := [3, 1, 1, 2, 1, 5, 2, 2, 1, 3, 2]
def baseStart_6595418 : Nat := 118140960795 + 6595418 * 2 ^ 59
def prefixEnd_6595418 : Nat := 4983230072969 + 3 ^ 40 * 6595418 * 2
def baseEnd_6595418 : Nat := 3386619551315381630443231

theorem tailTrace_6595418 : CollatzResearch.WordTrace tailWord_6595418 prefixEnd_6595418 3386619551315381630443231 := by
  unfold tailWord_6595418
  simp only [CollatzResearch.WordTrace]
  refine ⟨60138664204983617140402727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160369771213289645707740605 60138664204983617140402727)
  ·
    refine ⟨90207996307475425710604091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60138664204983617140402727 90207996307475425710604091)
    ·
      refine ⟨135311994461213138565906137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90207996307475425710604091 135311994461213138565906137)
      ·
        refine ⟨101483995845909853924429603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135311994461213138565906137 101483995845909853924429603)
        ·
          refine ⟨152225993768864780886644405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101483995845909853924429603 152225993768864780886644405)
          ·
            refine ⟨14271186915831073208122913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 152225993768864780886644405 14271186915831073208122913)
            ·
              refine ⟨10703390186873304906092185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14271186915831073208122913 10703390186873304906092185)
              ·
                refine ⟨8027542640154978679569139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10703390186873304906092185 8027542640154978679569139)
                ·
                  refine ⟨12041313960232468019353709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8027542640154978679569139 12041313960232468019353709)
                  ·
                    refine ⟨4515492735087175507257641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12041313960232468019353709 4515492735087175507257641)
                    ·
                      refine ⟨3386619551315381630443231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4515492735087175507257641 3386619551315381630443231)
                      ·
                        rfl

theorem cell23_6595418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 2, 1, 3, 2].length) (baseStart_6595418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6595418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6595418 prefixEnd_6595418 := by exact prefixLift 6595418
  have htrace : WordTrace (prefixWord ++ tailWord_6595418) baseStart_6595418 baseEnd_6595418 := by
    simpa [prefixWord, tailWord_6595418, baseEnd_6595418] using wordTrace_append hprefix tailTrace_6595418
  have hstable : (prefixWord ++ tailWord_6595418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6595418).length < 2 ^ (prefixWord ++ tailWord_6595418).sum := by decide
  have hdescent : baseEnd_6595418 < baseStart_6595418 := by decide
  rcases family_descends (prefixWord ++ tailWord_6595418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6595465 : List Nat := [1, 2, 1, 1, 5, 2, 4, 1, 2, 2, 2]
def baseStart_6595465 : Nat := 118140960795 + 6595465 * 2 ^ 59
def prefixEnd_6595465 : Nat := 4983230072969 + 3 ^ 40 * 6595465 * 2
def baseEnd_6595465 : Nat := 3386643684906142946555515

theorem tailTrace_6595465 : CollatzResearch.WordTrace tailWord_6595465 prefixEnd_6595465 3386643684906142946555515 := by
  unfold tailWord_6595465
  simp only [CollatzResearch.WordTrace]
  refine ⟨240556371050764195588571849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160370914033842797059047899 240556371050764195588571849)
  ·
    refine ⟨180417278288073146691428887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240556371050764195588571849 180417278288073146691428887)
    ·
      refine ⟨270625917432109720037143331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180417278288073146691428887 270625917432109720037143331)
      ·
        refine ⟨405938876148164580055714997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270625917432109720037143331 405938876148164580055714997)
        ·
          refine ⟨38056769638890429380223281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 405938876148164580055714997 38056769638890429380223281)
          ·
            refine ⟨28542577229167822035167461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38056769638890429380223281 28542577229167822035167461)
            ·
              refine ⟨5351733230468966631593899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28542577229167822035167461 5351733230468966631593899)
              ·
                refine ⟨8027599845703449947390849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5351733230468966631593899 8027599845703449947390849)
                ·
                  refine ⟨6020699884277587460543137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8027599845703449947390849 6020699884277587460543137)
                  ·
                    refine ⟨4515524913208190595407353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6020699884277587460543137 4515524913208190595407353)
                    ·
                      refine ⟨3386643684906142946555515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4515524913208190595407353 3386643684906142946555515)
                      ·
                        rfl

theorem cell23_6595465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 4, 1, 2, 2, 2].length) (baseStart_6595465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6595465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6595465 prefixEnd_6595465 := by exact prefixLift 6595465
  have htrace : WordTrace (prefixWord ++ tailWord_6595465) baseStart_6595465 baseEnd_6595465 := by
    simpa [prefixWord, tailWord_6595465, baseEnd_6595465] using wordTrace_append hprefix tailTrace_6595465
  have hstable : (prefixWord ++ tailWord_6595465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6595465).length < 2 ^ (prefixWord ++ tailWord_6595465).sum := by decide
  have hdescent : baseEnd_6595465 < baseStart_6595465 := by decide
  rcases family_descends (prefixWord ++ tailWord_6595465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6595467 : List Nat := [1, 1, 1, 1, 4, 2, 2, 1, 3, 7]
def baseStart_6595467 : Nat := 118140960795 + 6595467 * 2 ^ 59
def prefixEnd_6595467 : Nat := 4983230072969 + 3 ^ 40 * 6595467 * 2
def baseEnd_6595467 : Nat := 1128881570622483979576835

theorem tailTrace_6595467 : CollatzResearch.WordTrace tailWord_6595467 prefixEnd_6595467 1128881570622483979576835 := by
  unfold tailWord_6595467
  simp only [CollatzResearch.WordTrace]
  refine ⟨240556443996756949930144655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160370962664504633286763103 240556443996756949930144655)
  ·
    refine ⟨360834665995135424895216983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240556443996756949930144655 360834665995135424895216983)
    ·
      refine ⟨541251998992703137342825475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360834665995135424895216983 541251998992703137342825475)
      ·
        refine ⟨811877998489054706014238213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 541251998992703137342825475 811877998489054706014238213)
        ·
          refine ⟨152227124716697757377669665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 811877998489054706014238213 152227124716697757377669665)
          ·
            refine ⟨114170343537523318033252249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152227124716697757377669665 114170343537523318033252249)
            ·
              refine ⟨85627757653142488524939187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114170343537523318033252249 85627757653142488524939187)
              ·
                refine ⟨128441636479713732787408781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85627757653142488524939187 128441636479713732787408781)
                ·
                  refine ⟨48165613679892649795278293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 128441636479713732787408781 48165613679892649795278293)
                  ·
                    refine ⟨1128881570622483979576835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48165613679892649795278293 1128881570622483979576835)
                    ·
                      rfl

theorem cell23_6595467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 3, 7].length) (baseStart_6595467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6595467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6595467 prefixEnd_6595467 := by exact prefixLift 6595467
  have htrace : WordTrace (prefixWord ++ tailWord_6595467) baseStart_6595467 baseEnd_6595467 := by
    simpa [prefixWord, tailWord_6595467, baseEnd_6595467] using wordTrace_append hprefix tailTrace_6595467
  have hstable : (prefixWord ++ tailWord_6595467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6595467).length < 2 ^ (prefixWord ++ tailWord_6595467).sum := by decide
  have hdescent : baseEnd_6595467 < baseStart_6595467 := by decide
  rcases family_descends (prefixWord ++ tailWord_6595467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6595505 : List Nat := [1, 2, 2, 4, 3, 2, 2, 2, 5]
def baseStart_6595505 : Nat := 118140960795 + 6595505 * 2 ^ 59
def prefixEnd_6595505 : Nat := 4983230072969 + 3 ^ 40 * 6595505 * 2
def baseEnd_6595505 : Nat := 376296024903591421117259

theorem tailTrace_6595505 : CollatzResearch.WordTrace tailWord_6595505 prefixEnd_6595505 376296024903591421117259 := by
  unfold tailWord_6595505
  simp only [CollatzResearch.WordTrace]
  refine ⟨240557829970619282420027969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160371886647079521613351979 240557829970619282420027969)
  ·
    refine ⟨180418372477964461815020977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240557829970619282420027969 180418372477964461815020977)
    ·
      refine ⟨135313779358473346361265733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180418372477964461815020977 135313779358473346361265733)
      ·
        refine ⟨25371333629713752442737325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135313779358473346361265733 25371333629713752442737325)
        ·
          refine ⟨9514250111142657166026497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25371333629713752442737325 9514250111142657166026497)
          ·
            refine ⟨7135687583356992874519873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9514250111142657166026497 7135687583356992874519873)
            ·
              refine ⟨5351765687517744655889905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7135687583356992874519873 5351765687517744655889905)
              ·
                refine ⟨4013824265638308491917429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5351765687517744655889905 4013824265638308491917429)
                ·
                  refine ⟨376296024903591421117259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4013824265638308491917429 376296024903591421117259)
                  ·
                    rfl

theorem cell23_6595505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 2, 2, 5].length) (baseStart_6595505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6595505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6595505 prefixEnd_6595505 := by exact prefixLift 6595505
  have htrace : WordTrace (prefixWord ++ tailWord_6595505) baseStart_6595505 baseEnd_6595505 := by
    simpa [prefixWord, tailWord_6595505, baseEnd_6595505] using wordTrace_append hprefix tailTrace_6595505
  have hstable : (prefixWord ++ tailWord_6595505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6595505).length < 2 ^ (prefixWord ++ tailWord_6595505).sum := by decide
  have hdescent : baseEnd_6595505 < baseStart_6595505 := by decide
  rcases family_descends (prefixWord ++ tailWord_6595505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6595531 : List Nat := [1, 1, 1, 1, 3, 6, 1, 2, 3, 4]
def baseStart_6595531 : Nat := 118140960795 + 6595531 * 2 ^ 59
def prefixEnd_6595531 : Nat := 4983230072969 + 3 ^ 40 * 6595531 * 2
def baseEnd_6595531 : Nat := 1128892524876446562776737

theorem tailTrace_6595531 : CollatzResearch.WordTrace tailWord_6595531 prefixEnd_6595531 1128892524876446562776737 := by
  unfold tailWord_6595531
  simp only [CollatzResearch.WordTrace]
  refine ⟨240558778268525088860474447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160372518845683392573649631 240558778268525088860474447)
  ·
    refine ⟨360838167402787633290711671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240558778268525088860474447 360838167402787633290711671)
    ·
      refine ⟨541257251104181449936067507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360838167402787633290711671 541257251104181449936067507)
      ·
        refine ⟨811885876656272174904101261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 541257251104181449936067507 811885876656272174904101261)
        ·
          refine ⟨304457203746102065589037973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 811885876656272174904101261 304457203746102065589037973)
          ·
            refine ⟨14271431425598534324486155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 304457203746102065589037973 14271431425598534324486155)
            ·
              refine ⟨21407147138397801486729233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14271431425598534324486155 21407147138397801486729233)
              ·
                refine ⟨16055360353798351115046925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21407147138397801486729233 16055360353798351115046925)
                ·
                  refine ⟨6020760132674381668142597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16055360353798351115046925 6020760132674381668142597)
                  ·
                    refine ⟨1128892524876446562776737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6020760132674381668142597 1128892524876446562776737)
                    ·
                      rfl

theorem cell23_6595531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 2, 3, 4].length) (baseStart_6595531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6595531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6595531 prefixEnd_6595531 := by exact prefixLift 6595531
  have htrace : WordTrace (prefixWord ++ tailWord_6595531) baseStart_6595531 baseEnd_6595531 := by
    simpa [prefixWord, tailWord_6595531, baseEnd_6595531] using wordTrace_append hprefix tailTrace_6595531
  have hstable : (prefixWord ++ tailWord_6595531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6595531).length < 2 ^ (prefixWord ++ tailWord_6595531).sum := by decide
  have hdescent : baseEnd_6595531 < baseStart_6595531 := by decide
  rcases family_descends (prefixWord ++ tailWord_6595531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6595538 : List Nat := [3, 2, 2, 3, 1, 1, 3, 1, 2, 1, 4]
def baseStart_6595538 : Nat := 118140960795 + 6595538 * 2 ^ 59
def prefixEnd_6595538 : Nat := 4983230072969 + 3 ^ 40 * 6595538 * 2
def baseEnd_6595538 : Nat := 3386681168993921160942679

theorem tailTrace_6595538 : CollatzResearch.WordTrace tailWord_6595538 prefixEnd_6595538 3386681168993921160942679 := by
  unfold tailWord_6595538
  simp only [CollatzResearch.WordTrace]
  refine ⟨60139758394874932263994817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160372689052999819370652845 60139758394874932263994817)
  ·
    refine ⟨45104818796156199197996113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60139758394874932263994817 45104818796156199197996113)
    ·
      refine ⟨33828614097117149398497085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45104818796156199197996113 33828614097117149398497085)
      ·
        refine ⟨12685730286418931024436407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33828614097117149398497085 12685730286418931024436407)
        ·
          refine ⟨19028595429628396536654611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12685730286418931024436407 19028595429628396536654611)
          ·
            refine ⟨28542893144442594804981917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19028595429628396536654611 28542893144442594804981917)
            ·
              refine ⟨10703584929165973051868219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28542893144442594804981917 10703584929165973051868219)
              ·
                refine ⟨16055377393748959577802329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10703584929165973051868219 16055377393748959577802329)
                ·
                  refine ⟨12041533045311719683351747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16055377393748959577802329 12041533045311719683351747)
                  ·
                    refine ⟨18062299567967579525027621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12041533045311719683351747 18062299567967579525027621)
                    ·
                      refine ⟨3386681168993921160942679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18062299567967579525027621 3386681168993921160942679)
                      ·
                        rfl

theorem cell23_6595538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_6595538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6595538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6595538 prefixEnd_6595538 := by exact prefixLift 6595538
  have htrace : WordTrace (prefixWord ++ tailWord_6595538) baseStart_6595538 baseEnd_6595538 := by
    simpa [prefixWord, tailWord_6595538, baseEnd_6595538] using wordTrace_append hprefix tailTrace_6595538
  have hstable : (prefixWord ++ tailWord_6595538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6595538).length < 2 ^ (prefixWord ++ tailWord_6595538).sum := by decide
  have hdescent : baseEnd_6595538 < baseStart_6595538 := by decide
  rcases family_descends (prefixWord ++ tailWord_6595538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6595598 : List Nat := [4, 1, 1, 2, 2, 2, 2, 1, 1, 5, 2]
def baseStart_6595598 : Nat := 118140960795 + 6595598 * 2 ^ 59
def prefixEnd_6595598 : Nat := 4983230072969 + 3 ^ 40 * 6595598 * 2
def baseEnd_6595598 : Nat := 3386711977833190926192403

theorem tailTrace_6595598 : CollatzResearch.WordTrace tailWord_6595598 prefixEnd_6595598 3386711977833190926192403 := by
  unfold tailWord_6595598
  simp only [CollatzResearch.WordTrace]
  refine ⟨30070152744910294912895431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160374147972854906202108965 30070152744910294912895431)
  ·
    refine ⟨45105229117365442369343147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30070152744910294912895431 45105229117365442369343147)
    ·
      refine ⟨67657843676048163554014721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45105229117365442369343147 67657843676048163554014721)
      ·
        refine ⟨50743382757036122665511041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67657843676048163554014721 50743382757036122665511041)
        ·
          refine ⟨38057537067777091999133281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50743382757036122665511041 38057537067777091999133281)
          ·
            refine ⟨28543152800832818999349961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38057537067777091999133281 28543152800832818999349961)
            ·
              refine ⟨21407364600624614249512471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28543152800832818999349961 21407364600624614249512471)
              ·
                refine ⟨32111046900936921374268707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21407364600624614249512471 32111046900936921374268707)
                ·
                  refine ⟨48166570351405382061403061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32111046900936921374268707 48166570351405382061403061)
                  ·
                    refine ⟨4515615970444254568256537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48166570351405382061403061 4515615970444254568256537)
                    ·
                      refine ⟨3386711977833190926192403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4515615970444254568256537 3386711977833190926192403)
                      ·
                        rfl

theorem cell23_6595598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 1, 1, 5, 2].length) (baseStart_6595598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6595598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6595598 prefixEnd_6595598 := by exact prefixLift 6595598
  have htrace : WordTrace (prefixWord ++ tailWord_6595598) baseStart_6595598 baseEnd_6595598 := by
    simpa [prefixWord, tailWord_6595598, baseEnd_6595598] using wordTrace_append hprefix tailTrace_6595598
  have hstable : (prefixWord ++ tailWord_6595598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6595598).length < 2 ^ (prefixWord ++ tailWord_6595598).sum := by decide
  have hdescent : baseEnd_6595598 < baseStart_6595598 := by decide
  rcases family_descends (prefixWord ++ tailWord_6595598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6595621 : List Nat := [1, 3, 1, 2, 2, 2, 1, 3, 4, 4]
def baseStart_6595621 : Nat := 118140960795 + 6595621 * 2 ^ 59
def prefixEnd_6595621 : Nat := 4983230072969 + 3 ^ 40 * 6595621 * 2
def baseEnd_6595621 : Nat := 1128907929296081445401599

theorem tailTrace_6595621 : CollatzResearch.WordTrace tailWord_6595621 prefixEnd_6595621 1128907929296081445401599 := by
  unfold tailWord_6595621
  simp only [CollatzResearch.WordTrace]
  refine ⟨240562060838199034231250717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160374707225466022820833811 240562060838199034231250717)
  ·
    refine ⟨90210772814324637836719019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 240562060838199034231250717 90210772814324637836719019)
    ·
      refine ⟨135316159221486956755078529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90210772814324637836719019 135316159221486956755078529)
      ·
        refine ⟨101487119416115217566308897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135316159221486956755078529 101487119416115217566308897)
        ·
          refine ⟨76115339562086413174731673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101487119416115217566308897 76115339562086413174731673)
          ·
            refine ⟨57086504671564809881048755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76115339562086413174731673 57086504671564809881048755)
            ·
              refine ⟨85629757007347214821573133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57086504671564809881048755 85629757007347214821573133)
              ·
                refine ⟨32111158877755205558089925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85629757007347214821573133 32111158877755205558089925)
                ·
                  refine ⟨6020842289579101042141861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32111158877755205558089925 6020842289579101042141861)
                  ·
                    refine ⟨1128907929296081445401599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6020842289579101042141861 1128907929296081445401599)
                    ·
                      rfl

theorem cell23_6595621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 3, 4, 4].length) (baseStart_6595621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6595621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6595621 prefixEnd_6595621 := by exact prefixLift 6595621
  have htrace : WordTrace (prefixWord ++ tailWord_6595621) baseStart_6595621 baseEnd_6595621 := by
    simpa [prefixWord, tailWord_6595621, baseEnd_6595621] using wordTrace_append hprefix tailTrace_6595621
  have hstable : (prefixWord ++ tailWord_6595621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6595621).length < 2 ^ (prefixWord ++ tailWord_6595621).sum := by decide
  have hdescent : baseEnd_6595621 < baseStart_6595621 := by decide
  rcases family_descends (prefixWord ++ tailWord_6595621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6595641 : List Nat := [1, 2, 1, 5, 2, 1, 2, 1, 1, 1, 6]
def baseStart_6595641 : Nat := 118140960795 + 6595641 * 2 ^ 59
def prefixEnd_6595641 : Nat := 4983230072969 + 3 ^ 40 * 6595641 * 2
def baseEnd_6595641 : Nat := 3386734057501334257954705

theorem tailTrace_6595641 : CollatzResearch.WordTrace tailWord_6595641 prefixEnd_6595641 3386734057501334257954705 := by
  unfold tailWord_6595641
  simp only [CollatzResearch.WordTrace]
  refine ⟨240562790298126577646978777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160375193532084385097985851 240562790298126577646978777)
  ·
    refine ⟨180422092723594933235234083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240562790298126577646978777 180422092723594933235234083)
    ·
      refine ⟨270633139085392399852851125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180422092723594933235234083 270633139085392399852851125)
      ·
        refine ⟨25371856789255537486204793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 270633139085392399852851125 25371856789255537486204793)
        ·
          refine ⟨19028892591941653114653595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25371856789255537486204793 19028892591941653114653595)
          ·
            refine ⟨28543338887912479671980393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19028892591941653114653595 28543338887912479671980393)
            ·
              refine ⟨21407504165934359753985295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28543338887912479671980393 21407504165934359753985295)
              ·
                refine ⟨32111256248901539630977943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21407504165934359753985295 32111256248901539630977943)
                ·
                  refine ⟨48166884373352309446466915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32111256248901539630977943 48166884373352309446466915)
                  ·
                    refine ⟨72250326560028464169700373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48166884373352309446466915 72250326560028464169700373)
                    ·
                      refine ⟨3386734057501334257954705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72250326560028464169700373 3386734057501334257954705)
                      ·
                        rfl

theorem cell23_6595641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_6595641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6595641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6595641 prefixEnd_6595641 := by exact prefixLift 6595641
  have htrace : WordTrace (prefixWord ++ tailWord_6595641) baseStart_6595641 baseEnd_6595641 := by
    simpa [prefixWord, tailWord_6595641, baseEnd_6595641] using wordTrace_append hprefix tailTrace_6595641
  have hstable : (prefixWord ++ tailWord_6595641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6595641).length < 2 ^ (prefixWord ++ tailWord_6595641).sum := by decide
  have hdescent : baseEnd_6595641 < baseStart_6595641 := by decide
  rcases family_descends (prefixWord ++ tailWord_6595641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6595645 : List Nat := [1, 4, 1, 3, 1, 4, 1, 2, 1, 1, 4]
def baseStart_6595645 : Nat := 118140960795 + 6595645 * 2 ^ 59
def prefixEnd_6595645 : Nat := 4983230072969 + 3 ^ 40 * 6595645 * 2
def baseEnd_6595645 : Nat := 3386736111423952242304687

theorem tailTrace_6595645 : CollatzResearch.WordTrace tailWord_6595645 prefixEnd_6595645 3386736111423952242304687 := by
  unfold tailWord_6595645
  simp only [CollatzResearch.WordTrace]
  refine ⟨240562936190112086330124389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160375290793408057553416259 240562936190112086330124389)
  ·
    refine ⟨45105550535646016186898323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 240562936190112086330124389 45105550535646016186898323)
    ·
      refine ⟨67658325803469024280347485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45105550535646016186898323 67658325803469024280347485)
      ·
        refine ⟨25371872176300884105130307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67658325803469024280347485 25371872176300884105130307)
        ·
          refine ⟨38057808264451326157695461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25371872176300884105130307 38057808264451326157695461)
          ·
            refine ⟨7135839049584623654567899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38057808264451326157695461 7135839049584623654567899)
            ·
              refine ⟨10703758574376935481851849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7135839049584623654567899 10703758574376935481851849)
              ·
                refine ⟨8027818930782701611388887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10703758574376935481851849 8027818930782701611388887)
                ·
                  refine ⟨12041728396174052417083331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8027818930782701611388887 12041728396174052417083331)
                  ·
                    refine ⟨18062592594261078625624997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12041728396174052417083331 18062592594261078625624997)
                    ·
                      refine ⟨3386736111423952242304687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18062592594261078625624997 3386736111423952242304687)
                      ·
                        rfl

theorem cell23_6595645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_6595645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6595645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6595645 prefixEnd_6595645 := by exact prefixLift 6595645
  have htrace : WordTrace (prefixWord ++ tailWord_6595645) baseStart_6595645 baseEnd_6595645 := by
    simpa [prefixWord, tailWord_6595645, baseEnd_6595645] using wordTrace_append hprefix tailTrace_6595645
  have hstable : (prefixWord ++ tailWord_6595645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6595645).length < 2 ^ (prefixWord ++ tailWord_6595645).sum := by decide
  have hdescent : baseEnd_6595645 < baseStart_6595645 := by decide
  rcases family_descends (prefixWord ++ tailWord_6595645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6595662 : List Nat := [4, 1, 1, 1, 1, 3, 2, 5, 1, 2, 2]
def baseStart_6595662 : Nat := 118140960795 + 6595662 * 2 ^ 59
def prefixEnd_6595662 : Nat := 4983230072969 + 3 ^ 40 * 6595662 * 2
def baseEnd_6595662 : Nat := 3386744840595078675792109

theorem tailTrace_6595662 : CollatzResearch.WordTrace tailWord_6595662 prefixEnd_6595662 3386744840595078675792109 := by
  unfold tailWord_6595662
  simp only [CollatzResearch.WordTrace]
  refine ⟨30070444528881312279186655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160375704154033665488995493 30070444528881312279186655)
  ·
    refine ⟨45105666793321968418779983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30070444528881312279186655 45105666793321968418779983)
    ·
      refine ⟨67658500189982952628169975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45105666793321968418779983 67658500189982952628169975)
      ·
        refine ⟨101487750284974428942254963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67658500189982952628169975 101487750284974428942254963)
        ·
          refine ⟨152231625427461643413382445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101487750284974428942254963 152231625427461643413382445)
          ·
            refine ⟨57086859535298116280018417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 152231625427461643413382445 57086859535298116280018417)
            ·
              refine ⟨42815144651473587210013813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57086859535298116280018417 42815144651473587210013813)
              ·
                refine ⟨4013919811075648800938795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42815144651473587210013813 4013919811075648800938795)
                ·
                  refine ⟨6020879716613473201408193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4013919811075648800938795 6020879716613473201408193)
                  ·
                    refine ⟨4515659787460104901056145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6020879716613473201408193 4515659787460104901056145)
                    ·
                      refine ⟨3386744840595078675792109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4515659787460104901056145 3386744840595078675792109)
                      ·
                        rfl

theorem cell23_6595662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 5, 1, 2, 2].length) (baseStart_6595662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6595662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6595662 prefixEnd_6595662 := by exact prefixLift 6595662
  have htrace : WordTrace (prefixWord ++ tailWord_6595662) baseStart_6595662 baseEnd_6595662 := by
    simpa [prefixWord, tailWord_6595662, baseEnd_6595662] using wordTrace_append hprefix tailTrace_6595662
  have hstable : (prefixWord ++ tailWord_6595662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6595662).length < 2 ^ (prefixWord ++ tailWord_6595662).sum := by decide
  have hdescent : baseEnd_6595662 < baseStart_6595662 := by decide
  rcases family_descends (prefixWord ++ tailWord_6595662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6595664 : List Nat := [2, 1, 1, 1, 1, 3, 1, 2, 4, 7]
def baseStart_6595664 : Nat := 118140960795 + 6595664 * 2 ^ 59
def prefixEnd_6595664 : Nat := 4983230072969 + 3 ^ 40 * 6595664 * 2
def baseEnd_6595664 : Nat := 1128915289185462555989033

theorem tailTrace_6595664 : CollatzResearch.WordTrace tailWord_6595664 prefixEnd_6595664 1128915289185462555989033 := by
  unfold tailWord_6595664
  simp only [CollatzResearch.WordTrace]
  refine ⟨120281814588521626287533023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160375752784695501716710697 120281814588521626287533023)
  ·
    refine ⟨180422721882782439431299535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120281814588521626287533023 180422721882782439431299535)
    ·
      refine ⟨270634082824173659146949303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180422721882782439431299535 270634082824173659146949303)
      ·
        refine ⟨405951124236260488720423955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270634082824173659146949303 405951124236260488720423955)
        ·
          refine ⟨608926686354390733080635933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 405951124236260488720423955 608926686354390733080635933)
          ·
            refine ⟨228347507382896524905238475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 608926686354390733080635933 228347507382896524905238475)
            ·
              refine ⟨342521261074344787357857713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228347507382896524905238475 342521261074344787357857713)
              ·
                refine ⟨256890945805758590518393285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 342521261074344787357857713 256890945805758590518393285)
                ·
                  refine ⟨48167052338579735722198741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 256890945805758590518393285 48167052338579735722198741)
                  ·
                    refine ⟨1128915289185462555989033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48167052338579735722198741 1128915289185462555989033)
                    ·
                      rfl

theorem cell23_6595664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 4, 7].length) (baseStart_6595664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6595664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6595664 prefixEnd_6595664 := by exact prefixLift 6595664
  have htrace : WordTrace (prefixWord ++ tailWord_6595664) baseStart_6595664 baseEnd_6595664 := by
    simpa [prefixWord, tailWord_6595664, baseEnd_6595664] using wordTrace_append hprefix tailTrace_6595664
  have hstable : (prefixWord ++ tailWord_6595664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6595664).length < 2 ^ (prefixWord ++ tailWord_6595664).sum := by decide
  have hdescent : baseEnd_6595664 < baseStart_6595664 := by decide
  rcases family_descends (prefixWord ++ tailWord_6595664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6595731 : List Nat := [1, 1, 1, 2, 1, 2, 5, 2, 2, 2, 4]
def baseStart_6595731 : Nat := 118140960795 + 6595731 * 2 ^ 59
def prefixEnd_6595731 : Nat := 4983230072969 + 3 ^ 40 * 6595731 * 2
def baseEnd_6595731 : Nat := 3386780270760238905829291

theorem tailTrace_6595731 : CollatzResearch.WordTrace tailWord_6595731 prefixEnd_6595731 3386780270760238905829291 := by
  unfold tailWord_6595731
  simp only [CollatzResearch.WordTrace]
  refine ⟨240566072867800523017755047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160377381911867015345170031 240566072867800523017755047)
  ·
    refine ⟨360849109301700784526632571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240566072867800523017755047 360849109301700784526632571)
    ·
      refine ⟨541273663952551176789948857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360849109301700784526632571 541273663952551176789948857)
      ·
        refine ⟨405955247964413382592461643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 541273663952551176789948857 405955247964413382592461643)
        ·
          refine ⟨608932871946620073888692465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 405955247964413382592461643 608932871946620073888692465)
          ·
            refine ⟨456699653959965055416519349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 608932871946620073888692465 456699653959965055416519349)
            ·
              refine ⟨42815592558746723945298689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 456699653959965055416519349 42815592558746723945298689)
              ·
                refine ⟨32111694419060042958974017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42815592558746723945298689 32111694419060042958974017)
                ·
                  refine ⟨24083770814295032219230513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32111694419060042958974017 24083770814295032219230513)
                  ·
                    refine ⟨18062828110721274164422885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24083770814295032219230513 18062828110721274164422885)
                    ·
                      refine ⟨3386780270760238905829291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18062828110721274164422885 3386780270760238905829291)
                      ·
                        rfl

theorem cell23_6595731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 2, 2, 2, 4].length) (baseStart_6595731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6595731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6595731 prefixEnd_6595731 := by exact prefixLift 6595731
  have htrace : WordTrace (prefixWord ++ tailWord_6595731) baseStart_6595731 baseEnd_6595731 := by
    simpa [prefixWord, tailWord_6595731, baseEnd_6595731] using wordTrace_append hprefix tailTrace_6595731
  have hstable : (prefixWord ++ tailWord_6595731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6595731).length < 2 ^ (prefixWord ++ tailWord_6595731).sum := by decide
  have hdescent : baseEnd_6595731 < baseStart_6595731 := by decide
  rcases family_descends (prefixWord ++ tailWord_6595731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6595748 : List Nat := [2, 3, 1, 2, 3, 1, 2, 1, 2, 2, 4]
def baseStart_6595748 : Nat := 118140960795 + 6595748 * 2 ^ 59
def prefixEnd_6595748 : Nat := 4983230072969 + 3 ^ 40 * 6595748 * 2
def baseEnd_6595748 : Nat := 3386788999931365339316713

theorem tailTrace_6595748 : CollatzResearch.WordTrace tailWord_6595748 prefixEnd_6595748 3386788999931365339316713 := by
  unfold tailWord_6595748
  simp only [CollatzResearch.WordTrace]
  refine ⟨120283346454369467460561949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160377795272492623280749265 120283346454369467460561949)
  ·
    refine ⟨45106254920388550297710731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120283346454369467460561949 45106254920388550297710731)
    ·
      refine ⟨67659382380582825446566097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45106254920388550297710731 67659382380582825446566097)
      ·
        refine ⟨50744536785437119084924573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67659382380582825446566097 50744536785437119084924573)
        ·
          refine ⟨19029201294538919656846715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50744536785437119084924573 19029201294538919656846715)
          ·
            refine ⟨28543801941808379485270073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19029201294538919656846715 28543801941808379485270073)
            ·
              refine ⟨21407851456356284613952555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28543801941808379485270073 21407851456356284613952555)
              ·
                refine ⟨32111777184534426920928833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21407851456356284613952555 32111777184534426920928833)
                ·
                  refine ⟨24083832888400820190696625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32111777184534426920928833 24083832888400820190696625)
                  ·
                    refine ⟨18062874666300615143022469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24083832888400820190696625 18062874666300615143022469)
                    ·
                      refine ⟨3386788999931365339316713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18062874666300615143022469 3386788999931365339316713)
                      ·
                        rfl

theorem cell23_6595748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_6595748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6595748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6595748 prefixEnd_6595748 := by exact prefixLift 6595748
  have htrace : WordTrace (prefixWord ++ tailWord_6595748) baseStart_6595748 baseEnd_6595748 := by
    simpa [prefixWord, tailWord_6595748, baseEnd_6595748] using wordTrace_append hprefix tailTrace_6595748
  have hstable : (prefixWord ++ tailWord_6595748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6595748).length < 2 ^ (prefixWord ++ tailWord_6595748).sum := by decide
  have hdescent : baseEnd_6595748 < baseStart_6595748 := by decide
  rcases family_descends (prefixWord ++ tailWord_6595748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6595781 : List Nat := [1, 3, 1, 1, 1, 1, 3, 4, 1, 2, 5]
def baseStart_6595781 : Nat := 118140960795 + 6595781 * 2 ^ 59
def prefixEnd_6595781 : Nat := 4983230072969 + 3 ^ 40 * 6595781 * 2
def baseEnd_6595781 : Nat := 3386805944792963710204061

theorem tailTrace_6595781 : CollatzResearch.WordTrace tailWord_6595781 prefixEnd_6595781 3386805944792963710204061 := by
  unfold tailWord_6595781
  simp only [CollatzResearch.WordTrace]
  refine ⟨240567896517619381557075197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160378597678412921038050131 240567896517619381557075197)
  ·
    refine ⟨90212961194107268083903199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 240567896517619381557075197 90212961194107268083903199)
    ·
      refine ⟨135319441791160902125854799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90212961194107268083903199 135319441791160902125854799)
      ·
        refine ⟨202979162686741353188782199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135319441791160902125854799 202979162686741353188782199)
        ·
          refine ⟨304468744030112029783173299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202979162686741353188782199 304468744030112029783173299)
          ·
            refine ⟨456703116045168044674759949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 304468744030112029783173299 456703116045168044674759949)
            ·
              refine ⟨171263668516938016753034981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 456703116045168044674759949 171263668516938016753034981)
              ·
                refine ⟨32111937846925878141194059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 171263668516938016753034981 32111937846925878141194059)
                ·
                  refine ⟨48167906770388817211791089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32111937846925878141194059 48167906770388817211791089)
                  ·
                    refine ⟨36125930077791612908843317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48167906770388817211791089 36125930077791612908843317)
                    ·
                      refine ⟨3386805944792963710204061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36125930077791612908843317 3386805944792963710204061)
                      ·
                        rfl

theorem cell23_6595781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 4, 1, 2, 5].length) (baseStart_6595781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6595781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6595781 prefixEnd_6595781 := by exact prefixLift 6595781
  have htrace : WordTrace (prefixWord ++ tailWord_6595781) baseStart_6595781 baseEnd_6595781 := by
    simpa [prefixWord, tailWord_6595781, baseEnd_6595781] using wordTrace_append hprefix tailTrace_6595781
  have hstable : (prefixWord ++ tailWord_6595781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6595781).length < 2 ^ (prefixWord ++ tailWord_6595781).sum := by decide
  have hdescent : baseEnd_6595781 < baseStart_6595781 := by decide
  rcases family_descends (prefixWord ++ tailWord_6595781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6595791 : List Nat := [1, 1, 2, 1, 1, 3, 2, 2, 3, 3, 4]
def baseStart_6595791 : Nat := 118140960795 + 6595791 * 2 ^ 59
def prefixEnd_6595791 : Nat := 4983230072969 + 3 ^ 40 * 6595791 * 2
def baseEnd_6595791 : Nat := 3386811079599508671079015

theorem tailTrace_6595791 : CollatzResearch.WordTrace tailWord_6595791 prefixEnd_6595791 3386811079599508671079015 := by
  unfold tailWord_6595791
  simp only [CollatzResearch.WordTrace]
  refine ⟨240568261247583153264939227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160378840831722102176626151 240568261247583153264939227)
  ·
    refine ⟨360852391871374729897408841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240568261247583153264939227 360852391871374729897408841)
    ·
      refine ⟨270639293903531047423056631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 360852391871374729897408841 270639293903531047423056631)
      ·
        refine ⟨405958940855296571134584947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270639293903531047423056631 405958940855296571134584947)
        ·
          refine ⟨608938411282944856701877421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 405958940855296571134584947 608938411282944856701877421)
          ·
            refine ⟨228351904231104321263204033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 608938411282944856701877421 228351904231104321263204033)
            ·
              refine ⟨171263928173328240947403025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228351904231104321263204033 171263928173328240947403025)
              ·
                refine ⟨128447946129996180710552269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 171263928173328240947403025 128447946129996180710552269)
                ·
                  refine ⟨48167979798748567766457101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 128447946129996180710552269 48167979798748567766457101)
                  ·
                    refine ⟨18062992424530712912421413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48167979798748567766457101 18062992424530712912421413)
                    ·
                      refine ⟨3386811079599508671079015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18062992424530712912421413 3386811079599508671079015)
                      ·
                        rfl

theorem cell23_6595791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 3, 3, 4].length) (baseStart_6595791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6595791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6595791 prefixEnd_6595791 := by exact prefixLift 6595791
  have htrace : WordTrace (prefixWord ++ tailWord_6595791) baseStart_6595791 baseEnd_6595791 := by
    simpa [prefixWord, tailWord_6595791, baseEnd_6595791] using wordTrace_append hprefix tailTrace_6595791
  have hstable : (prefixWord ++ tailWord_6595791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6595791).length < 2 ^ (prefixWord ++ tailWord_6595791).sum := by decide
  have hdescent : baseEnd_6595791 < baseStart_6595791 := by decide
  rcases family_descends (prefixWord ++ tailWord_6595791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6595852 : List Nat := [2, 2, 1, 2, 2, 4, 1, 4, 1, 4]
def baseStart_6595852 : Nat := 118140960795 + 6595852 * 2 ^ 59
def prefixEnd_6595852 : Nat := 4983230072969 + 3 ^ 40 * 6595852 * 2
def baseEnd_6595852 : Nat := 1128947467306477644138745

theorem tailTrace_6595852 : CollatzResearch.WordTrace tailWord_6595852 prefixEnd_6595852 1128947467306477644138745 := by
  unfold tailWord_6595852
  simp only [CollatzResearch.WordTrace]
  refine ⟨120285243050181080341454905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160380324066908107121939873 120285243050181080341454905)
  ·
    refine ⟨90213932287635810256091179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120285243050181080341454905 90213932287635810256091179)
    ·
      refine ⟨135320898431453715384136769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90213932287635810256091179 135320898431453715384136769)
      ·
        refine ⟨101490673823590286538102577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135320898431453715384136769 101490673823590286538102577)
        ·
          refine ⟨76118005367692714903576933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101490673823590286538102577 76118005367692714903576933)
          ·
            refine ⟨14272126006442384044420675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76118005367692714903576933 14272126006442384044420675)
            ·
              refine ⟨21408189009663576066631013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14272126006442384044420675 21408189009663576066631013)
              ·
                refine ⟨4014035439311920512493315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21408189009663576066631013 4014035439311920512493315)
                ·
                  refine ⟨6021053158967880768739973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4014035439311920512493315 6021053158967880768739973)
                  ·
                    refine ⟨1128947467306477644138745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6021053158967880768739973 1128947467306477644138745)
                    ·
                      rfl

theorem cell23_6595852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 4, 1, 4].length) (baseStart_6595852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6595852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6595852 prefixEnd_6595852 := by exact prefixLift 6595852
  have htrace : WordTrace (prefixWord ++ tailWord_6595852) baseStart_6595852 baseEnd_6595852 := by
    simpa [prefixWord, tailWord_6595852, baseEnd_6595852] using wordTrace_append hprefix tailTrace_6595852
  have hstable : (prefixWord ++ tailWord_6595852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6595852).length < 2 ^ (prefixWord ++ tailWord_6595852).sum := by decide
  have hdescent : baseEnd_6595852 < baseStart_6595852 := by decide
  rcases family_descends (prefixWord ++ tailWord_6595852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6595875 : List Nat := [1, 1, 1, 4, 2, 3, 1, 1, 5, 1, 3]
def baseStart_6595875 : Nat := 118140960795 + 6595875 * 2 ^ 59
def prefixEnd_6595875 : Nat := 4983230072969 + 3 ^ 40 * 6595875 * 2
def baseEnd_6595875 : Nat := 3386854211974486342428629

theorem tailTrace_6595875 : CollatzResearch.WordTrace tailWord_6595875 prefixEnd_6595875 3386854211974486342428629 := by
  unfold tailWord_6595875
  simp only [CollatzResearch.WordTrace]
  refine ⟨240571324979278835610997079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160380883319519223740664719 240571324979278835610997079)
  ·
    refine ⟨360856987468918253416495619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240571324979278835610997079 360856987468918253416495619)
    ·
      refine ⟨541285481203377380124743429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360856987468918253416495619 541285481203377380124743429)
      ·
        refine ⟨101491027725633258773389393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 541285481203377380124743429 101491027725633258773389393)
        ·
          refine ⟨76118270794224944080042045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101491027725633258773389393 76118270794224944080042045)
          ·
            refine ⟨28544351547834354030015767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76118270794224944080042045 28544351547834354030015767)
            ·
              refine ⟨42816527321751531045023651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28544351547834354030015767 42816527321751531045023651)
              ·
                refine ⟨64224790982627296567535477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42816527321751531045023651 64224790982627296567535477)
                ·
                  refine ⟨6021074154621309053206451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64224790982627296567535477 6021074154621309053206451)
                  ·
                    refine ⟨9031611231931963579809677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6021074154621309053206451 9031611231931963579809677)
                    ·
                      refine ⟨3386854211974486342428629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9031611231931963579809677 3386854211974486342428629)
                      ·
                        rfl

theorem cell23_6595875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 5, 1, 3].length) (baseStart_6595875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6595875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6595875 prefixEnd_6595875 := by exact prefixLift 6595875
  have htrace : WordTrace (prefixWord ++ tailWord_6595875) baseStart_6595875 baseEnd_6595875 := by
    simpa [prefixWord, tailWord_6595875, baseEnd_6595875] using wordTrace_append hprefix tailTrace_6595875
  have hstable : (prefixWord ++ tailWord_6595875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6595875).length < 2 ^ (prefixWord ++ tailWord_6595875).sum := by decide
  have hdescent : baseEnd_6595875 < baseStart_6595875 := by decide
  rcases family_descends (prefixWord ++ tailWord_6595875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6595881 : List Nat := [1, 2, 1, 1, 1, 1, 1, 2, 2, 1, 10]
def baseStart_6595881 : Nat := 118140960795 + 6595881 * 2 ^ 59
def prefixEnd_6595881 : Nat := 4983230072969 + 3 ^ 40 * 6595881 * 2
def baseEnd_6595881 : Nat := 3386857292858413318953601

theorem tailTrace_6595881 : CollatzResearch.WordTrace tailWord_6595881 prefixEnd_6595881 3386857292858413318953601 := by
  unfold tailWord_6595881
  simp only [CollatzResearch.WordTrace]
  refine ⟨240571543817257098635715497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160381029211504732423810331 240571543817257098635715497)
  ·
    refine ⟨180428657862942823976786623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240571543817257098635715497 180428657862942823976786623)
    ·
      refine ⟨270642986794414235965179935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180428657862942823976786623 270642986794414235965179935)
      ·
        refine ⟨405964480191621353947769903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270642986794414235965179935 405964480191621353947769903)
        ·
          refine ⟨608946720287432030921654855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 405964480191621353947769903 608946720287432030921654855)
          ·
            refine ⟨913420080431148046382482283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 608946720287432030921654855 913420080431148046382482283)
            ·
              refine ⟨1370130120646722069573723425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 913420080431148046382482283 1370130120646722069573723425)
              ·
                refine ⟨1027597590485041552180292569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1370130120646722069573723425 1027597590485041552180292569)
                ·
                  refine ⟨770698192863781164135219427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1027597590485041552180292569 770698192863781164135219427)
                  ·
                    refine ⟨1156047289295671746202829141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 770698192863781164135219427 1156047289295671746202829141)
                    ·
                      refine ⟨3386857292858413318953601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 1156047289295671746202829141 3386857292858413318953601)
                      ·
                        rfl

theorem cell23_6595881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 1, 10].length) (baseStart_6595881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6595881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6595881 prefixEnd_6595881 := by exact prefixLift 6595881
  have htrace : WordTrace (prefixWord ++ tailWord_6595881) baseStart_6595881 baseEnd_6595881 := by
    simpa [prefixWord, tailWord_6595881, baseEnd_6595881] using wordTrace_append hprefix tailTrace_6595881
  have hstable : (prefixWord ++ tailWord_6595881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6595881).length < 2 ^ (prefixWord ++ tailWord_6595881).sum := by decide
  have hdescent : baseEnd_6595881 < baseStart_6595881 := by decide
  rcases family_descends (prefixWord ++ tailWord_6595881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6595892 : List Nat := [2, 5, 1, 1, 1, 1, 1, 2, 5, 1, 3]
def baseStart_6595892 : Nat := 118140960795 + 6595892 * 2 ^ 59
def prefixEnd_6595892 : Nat := 4983230072969 + 3 ^ 40 * 6595892 * 2
def baseEnd_6595892 : Nat := 3386862941145612775916051

theorem tailTrace_6595892 : CollatzResearch.WordTrace tailWord_6595892 prefixEnd_6595892 3386862941145612775916051 := by
  unfold tailWord_6595892
  simp only [CollatzResearch.WordTrace]
  refine ⟨120285972510108623757182965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160381296680144831676243953 120285972510108623757182965)
  ·
    refine ⟨11276809922822683477235903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 120285972510108623757182965 11276809922822683477235903)
    ·
      refine ⟨16915214884234025215853855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11276809922822683477235903 16915214884234025215853855)
      ·
        refine ⟨25372822326351037823780783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16915214884234025215853855 25372822326351037823780783)
        ·
          refine ⟨38059233489526556735671175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25372822326351037823780783 38059233489526556735671175)
          ·
            refine ⟨57088850234289835103506763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38059233489526556735671175 57088850234289835103506763)
            ·
              refine ⟨85633275351434752655260145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57088850234289835103506763 85633275351434752655260145)
              ·
                refine ⟨64224956513576064491445109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85633275351434752655260145 64224956513576064491445109)
                ·
                  refine ⟨6021089673147756046072979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64224956513576064491445109 6021089673147756046072979)
                  ·
                    refine ⟨9031634509721634069109469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6021089673147756046072979 9031634509721634069109469)
                    ·
                      refine ⟨3386862941145612775916051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9031634509721634069109469 3386862941145612775916051)
                      ·
                        rfl

theorem cell23_6595892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_6595892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6595892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6595892 prefixEnd_6595892 := by exact prefixLift 6595892
  have htrace : WordTrace (prefixWord ++ tailWord_6595892) baseStart_6595892 baseEnd_6595892 := by
    simpa [prefixWord, tailWord_6595892, baseEnd_6595892] using wordTrace_append hprefix tailTrace_6595892
  have hstable : (prefixWord ++ tailWord_6595892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6595892).length < 2 ^ (prefixWord ++ tailWord_6595892).sum := by decide
  have hdescent : baseEnd_6595892 < baseStart_6595892 := by decide
  rcases family_descends (prefixWord ++ tailWord_6595892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6595902 : List Nat := [4, 2, 1, 2, 1, 1, 2, 1, 4, 3, 2]
def baseStart_6595902 : Nat := 118140960795 + 6595902 * 2 ^ 59
def prefixEnd_6595902 : Nat := 4983230072969 + 3 ^ 40 * 6595902 * 2
def baseEnd_6595902 : Nat := 3386868075952157736791005

theorem tailTrace_6595902 : CollatzResearch.WordTrace tailWord_6595902 prefixEnd_6595902 3386868075952157736791005 := by
  unfold tailWord_6595902
  simp only [CollatzResearch.WordTrace]
  refine ⟨30071538718772627402778745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160381539833454012814819973 30071538718772627402778745)
  ·
    refine ⟨22553654039079470552084059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30071538718772627402778745 22553654039079470552084059)
    ·
      refine ⟨33830481058619205828126089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22553654039079470552084059 33830481058619205828126089)
      ·
        refine ⟨25372860793964404371094567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33830481058619205828126089 25372860793964404371094567)
        ·
          refine ⟨38059291190946606556641851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25372860793964404371094567 38059291190946606556641851)
          ·
            refine ⟨57088936786419909834962777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38059291190946606556641851 57088936786419909834962777)
            ·
              refine ⟨42816702589814932376222083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57088936786419909834962777 42816702589814932376222083)
              ·
                refine ⟨64225053884722398564333125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42816702589814932376222083 64225053884722398564333125)
                ·
                  refine ⟨12042197603385449730812461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64225053884722398564333125 12042197603385449730812461)
                  ·
                    refine ⟨4515824101269543649054673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12042197603385449730812461 4515824101269543649054673)
                    ·
                      refine ⟨3386868075952157736791005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4515824101269543649054673 3386868075952157736791005)
                      ·
                        rfl

theorem cell23_6595902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 4, 3, 2].length) (baseStart_6595902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6595902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6595902 prefixEnd_6595902 := by exact prefixLift 6595902
  have htrace : WordTrace (prefixWord ++ tailWord_6595902) baseStart_6595902 baseEnd_6595902 := by
    simpa [prefixWord, tailWord_6595902, baseEnd_6595902] using wordTrace_append hprefix tailTrace_6595902
  have hstable : (prefixWord ++ tailWord_6595902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6595902).length < 2 ^ (prefixWord ++ tailWord_6595902).sum := by decide
  have hdescent : baseEnd_6595902 < baseStart_6595902 := by decide
  rcases family_descends (prefixWord ++ tailWord_6595902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6595925 : List Nat := [1, 3, 2, 2, 3, 1, 3, 1, 1, 6]
def baseStart_6595925 : Nat := 118140960795 + 6595925 * 2 ^ 59
def prefixEnd_6595925 : Nat := 4983230072969 + 3 ^ 40 * 6595925 * 2
def baseEnd_6595925 : Nat := 1128959962002403715601133

theorem tailTrace_6595925 : CollatzResearch.WordTrace tailWord_6595925 prefixEnd_6595925 1128959962002403715601133 := by
  unfold tailWord_6595925
  simp only [CollatzResearch.WordTrace]
  refine ⟨240573148629097694150317229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160382099086065129433544819 240573148629097694150317229)
  ·
    refine ⟨90214930735911635306368961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 240573148629097694150317229 90214930735911635306368961)
    ·
      refine ⟨67661198051933726479776721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90214930735911635306368961 67661198051933726479776721)
      ·
        refine ⟨50745898538950294859832541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67661198051933726479776721 50745898538950294859832541)
        ·
          refine ⟨19029711952106360572437203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50745898538950294859832541 19029711952106360572437203)
          ·
            refine ⟨28544567928159540858655805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19029711952106360572437203 28544567928159540858655805)
            ·
              refine ⟨10704212973059827821995927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28544567928159540858655805 10704212973059827821995927)
              ·
                refine ⟨16056319459589741732993891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10704212973059827821995927 16056319459589741732993891)
                ·
                  refine ⟨24084479189384612599490837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16056319459589741732993891 24084479189384612599490837)
                  ·
                    refine ⟨1128959962002403715601133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24084479189384612599490837 1128959962002403715601133)
                    ·
                      rfl

theorem cell23_6595925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 1, 1, 6].length) (baseStart_6595925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6595925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6595925 prefixEnd_6595925 := by exact prefixLift 6595925
  have htrace : WordTrace (prefixWord ++ tailWord_6595925) baseStart_6595925 baseEnd_6595925 := by
    simpa [prefixWord, tailWord_6595925, baseEnd_6595925] using wordTrace_append hprefix tailTrace_6595925
  have hstable : (prefixWord ++ tailWord_6595925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6595925).length < 2 ^ (prefixWord ++ tailWord_6595925).sum := by decide
  have hdescent : baseEnd_6595925 < baseStart_6595925 := by decide
  rcases family_descends (prefixWord ++ tailWord_6595925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6595928 : List Nat := [2, 1, 2, 2, 1, 1, 5, 1, 1, 1, 6]
def baseStart_6595928 : Nat := 118140960795 + 6595928 * 2 ^ 59
def prefixEnd_6595928 : Nat := 4983230072969 + 3 ^ 40 * 6595928 * 2
def baseEnd_6595928 : Nat := 3386881426449174635065885

theorem tailTrace_6595928 : CollatzResearch.WordTrace tailWord_6595928 prefixEnd_6595928 3386881426449174635065885 := by
  unfold tailWord_6595928
  simp only [CollatzResearch.WordTrace]
  refine ⟨120286629024043412831338219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160382172032057883775117625 120286629024043412831338219)
  ·
    refine ⟨180429943536065119247007329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120286629024043412831338219 180429943536065119247007329)
    ·
      refine ⟨135322457652048839435255497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180429943536065119247007329 135322457652048839435255497)
      ·
        refine ⟨101491843239036629576441623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135322457652048839435255497 101491843239036629576441623)
        ·
          refine ⟨152237764858554944364662435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101491843239036629576441623 152237764858554944364662435)
          ·
            refine ⟨228356647287832416546993653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152237764858554944364662435 228356647287832416546993653)
            ·
              refine ⟨21408435683234289051280655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 228356647287832416546993653 21408435683234289051280655)
              ·
                refine ⟨32112653524851433576920983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21408435683234289051280655 32112653524851433576920983)
                ·
                  refine ⟨48168980287277150365381475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32112653524851433576920983 48168980287277150365381475)
                  ·
                    refine ⟨72253470430915725548072213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48168980287277150365381475 72253470430915725548072213)
                    ·
                      refine ⟨3386881426449174635065885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72253470430915725548072213 3386881426449174635065885)
                      ·
                        rfl

theorem cell23_6595928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 1, 1, 1, 6].length) (baseStart_6595928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6595928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6595928 prefixEnd_6595928 := by exact prefixLift 6595928
  have htrace : WordTrace (prefixWord ++ tailWord_6595928) baseStart_6595928 baseEnd_6595928 := by
    simpa [prefixWord, tailWord_6595928, baseEnd_6595928] using wordTrace_append hprefix tailTrace_6595928
  have hstable : (prefixWord ++ tailWord_6595928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6595928).length < 2 ^ (prefixWord ++ tailWord_6595928).sum := by decide
  have hdescent : baseEnd_6595928 < baseStart_6595928 := by decide
  rcases family_descends (prefixWord ++ tailWord_6595928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6595943 : List Nat := [1, 1, 5, 1, 5, 1, 1, 3, 1, 1, 3]
def baseStart_6595943 : Nat := 118140960795 + 6595943 * 2 ^ 59
def prefixEnd_6595943 : Nat := 4983230072969 + 3 ^ 40 * 6595943 * 2
def baseEnd_6595943 : Nat := 3386889128658992076378317

theorem tailTrace_6595943 : CollatzResearch.WordTrace tailWord_6595943 prefixEnd_6595943 3386889128658992076378317 := by
  unfold tailWord_6595943
  simp only [CollatzResearch.WordTrace]
  refine ⟨240573805143032483224472483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160382536762021655482981655 240573805143032483224472483)
  ·
    refine ⟨360860707714548724836708725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240573805143032483224472483 360860707714548724836708725)
    ·
      refine ⟨33830691348238942953441443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 360860707714548724836708725 33830691348238942953441443)
      ·
        refine ⟨50746037022358414430162165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33830691348238942953441443 50746037022358414430162165)
        ·
          refine ⟨4757440970846101352827703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50746037022358414430162165 4757440970846101352827703)
          ·
            refine ⟨7136161456269152029241555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4757440970846101352827703 7136161456269152029241555)
            ·
              refine ⟨10704242184403728043862333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7136161456269152029241555 10704242184403728043862333)
              ·
                refine ⟨4014090819151398016448375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10704242184403728043862333 4014090819151398016448375)
                ·
                  refine ⟨6021136228727097024672563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4014090819151398016448375 6021136228727097024672563)
                  ·
                    refine ⟨9031704343090645537008845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6021136228727097024672563 9031704343090645537008845)
                    ·
                      refine ⟨3386889128658992076378317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9031704343090645537008845 3386889128658992076378317)
                      ·
                        rfl

theorem cell23_6595943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 3, 1, 1, 3].length) (baseStart_6595943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6595943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6595943 prefixEnd_6595943 := by exact prefixLift 6595943
  have htrace : WordTrace (prefixWord ++ tailWord_6595943) baseStart_6595943 baseEnd_6595943 := by
    simpa [prefixWord, tailWord_6595943, baseEnd_6595943] using wordTrace_append hprefix tailTrace_6595943
  have hstable : (prefixWord ++ tailWord_6595943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6595943).length < 2 ^ (prefixWord ++ tailWord_6595943).sum := by decide
  have hdescent : baseEnd_6595943 < baseStart_6595943 := by decide
  rcases family_descends (prefixWord ++ tailWord_6595943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6596039 : List Nat := [1, 1, 4, 1, 1, 3, 1, 5, 2, 2, 2]
def baseStart_6596039 : Nat := 118140960795 + 6596039 * 2 ^ 59
def prefixEnd_6596039 : Nat := 4983230072969 + 3 ^ 40 * 6596039 * 2
def baseEnd_6596039 : Nat := 3386938422801823700777875

theorem tailTrace_6596039 : CollatzResearch.WordTrace tailWord_6596039 prefixEnd_6596039 3386938422801823700777875 := by
  unfold tailWord_6596039
  simp only [CollatzResearch.WordTrace]
  refine ⟨240577306550684691619967171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160384871033789794413311447 240577306550684691619967171)
  ·
    refine ⟨360865959826027037429950757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240577306550684691619967171 360865959826027037429950757)
    ·
      refine ⟨67662367467380069518115767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 360865959826027037429950757 67662367467380069518115767)
      ·
        refine ⟨101493551201070104277173651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67662367467380069518115767 101493551201070104277173651)
        ·
          refine ⟨152240326801605156415760477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101493551201070104277173651 152240326801605156415760477)
          ·
            refine ⟨57090122550601933655910179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 152240326801605156415760477 57090122550601933655910179)
            ·
              refine ⟨85635183825902900483865269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57090122550601933655910179 85635183825902900483865269)
              ·
                refine ⟨8028298483678396920362369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85635183825902900483865269 8028298483678396920362369)
                ·
                  refine ⟨6021223862758797690271777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8028298483678396920362369 6021223862758797690271777)
                  ·
                    refine ⟨4515917897069098267703833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6021223862758797690271777 4515917897069098267703833)
                    ·
                      refine ⟨3386938422801823700777875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4515917897069098267703833 3386938422801823700777875)
                      ·
                        rfl

theorem cell23_6596039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 5, 2, 2, 2].length) (baseStart_6596039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6596039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6596039 prefixEnd_6596039 := by exact prefixLift 6596039
  have htrace : WordTrace (prefixWord ++ tailWord_6596039) baseStart_6596039 baseEnd_6596039 := by
    simpa [prefixWord, tailWord_6596039, baseEnd_6596039] using wordTrace_append hprefix tailTrace_6596039
  have hstable : (prefixWord ++ tailWord_6596039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6596039).length < 2 ^ (prefixWord ++ tailWord_6596039).sum := by decide
  have hdescent : baseEnd_6596039 < baseStart_6596039 := by decide
  rcases family_descends (prefixWord ++ tailWord_6596039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6596048 : List Nat := [2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 8]
def baseStart_6596048 : Nat := 118140960795 + 6596048 * 2 ^ 59
def prefixEnd_6596048 : Nat := 4983230072969 + 3 ^ 40 * 6596048 * 2
def baseEnd_6596048 : Nat := 3386943044127714165565333

theorem tailTrace_6596048 : CollatzResearch.WordTrace tailWord_6596048 prefixEnd_6596048 3386943044127714165565333 := by
  unfold tailWord_6596048
  simp only [CollatzResearch.WordTrace]
  refine ⟨120288817403826043078522399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160385089871768057438029865 120288817403826043078522399)
  ·
    refine ⟨180433226105739064617783599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120288817403826043078522399 180433226105739064617783599)
    ·
      refine ⟨270649839158608596926675399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180433226105739064617783599 270649839158608596926675399)
      ·
        refine ⟨405974758737912895390013099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270649839158608596926675399 405974758737912895390013099)
        ·
          refine ⟨608962138106869343085019649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 405974758737912895390013099 608962138106869343085019649)
          ·
            refine ⟨456721603580152007313764737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 608962138106869343085019649 456721603580152007313764737)
            ·
              refine ⟨342541202685114005485323553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 456721603580152007313764737 342541202685114005485323553)
              ·
                refine ⟨256905902013835504113992665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 342541202685114005485323553 256905902013835504113992665)
                ·
                  refine ⟨192679426510376628085494499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 256905902013835504113992665 192679426510376628085494499)
                  ·
                    refine ⟨289019139765564942128241749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 192679426510376628085494499 289019139765564942128241749)
                    ·
                      refine ⟨3386943044127714165565333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 289019139765564942128241749 3386943044127714165565333)
                      ·
                        rfl

theorem cell23_6596048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 8].length) (baseStart_6596048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6596048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6596048 prefixEnd_6596048 := by exact prefixLift 6596048
  have htrace : WordTrace (prefixWord ++ tailWord_6596048) baseStart_6596048 baseEnd_6596048 := by
    simpa [prefixWord, tailWord_6596048, baseEnd_6596048] using wordTrace_append hprefix tailTrace_6596048
  have hstable : (prefixWord ++ tailWord_6596048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6596048).length < 2 ^ (prefixWord ++ tailWord_6596048).sum := by decide
  have hdescent : baseEnd_6596048 < baseStart_6596048 := by decide
  rcases family_descends (prefixWord ++ tailWord_6596048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6596095 : List Nat := [1, 1, 2, 2, 1, 2, 2, 1, 6, 1, 4]
def baseStart_6596095 : Nat := 118140960795 + 6596095 * 2 ^ 59
def prefixEnd_6596095 : Nat := 4983230072969 + 3 ^ 40 * 6596095 * 2
def baseEnd_6596095 : Nat := 3386967177718475481677617

theorem tailTrace_6596095 : CollatzResearch.WordTrace tailWord_6596095 prefixEnd_6596095 3386967177718475481677617 := by
  unfold tailWord_6596095
  simp only [CollatzResearch.WordTrace]
  refine ⟨240579349038481813184005739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160386232692321208789337159 240579349038481813184005739)
  ·
    refine ⟨360869023557722719776008609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240579349038481813184005739 360869023557722719776008609)
    ·
      refine ⟨270651767668292039832006457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 360869023557722719776008609 270651767668292039832006457)
      ·
        refine ⟨202988825751219029874004843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270651767668292039832006457 202988825751219029874004843)
        ·
          refine ⟨304483238626828544811007265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202988825751219029874004843 304483238626828544811007265)
          ·
            refine ⟨228362428970121408608255449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 304483238626828544811007265 228362428970121408608255449)
            ·
              refine ⟨171271821727591056456191587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228362428970121408608255449 171271821727591056456191587)
              ·
                refine ⟨256907732591386584684287381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171271821727591056456191587 256907732591386584684287381)
                ·
                  refine ⟨12042549965221246157075971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 256907732591386584684287381 12042549965221246157075971)
                  ·
                    refine ⟨18063824947831869235613957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12042549965221246157075971 18063824947831869235613957)
                    ·
                      refine ⟨3386967177718475481677617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18063824947831869235613957 3386967177718475481677617)
                      ·
                        rfl

theorem cell23_6596095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 6, 1, 4].length) (baseStart_6596095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6596095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6596095 prefixEnd_6596095 := by exact prefixLift 6596095
  have htrace : WordTrace (prefixWord ++ tailWord_6596095) baseStart_6596095 baseEnd_6596095 := by
    simpa [prefixWord, tailWord_6596095, baseEnd_6596095] using wordTrace_append hprefix tailTrace_6596095
  have hstable : (prefixWord ++ tailWord_6596095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6596095).length < 2 ^ (prefixWord ++ tailWord_6596095).sum := by decide
  have hdescent : baseEnd_6596095 < baseStart_6596095 := by decide
  rcases family_descends (prefixWord ++ tailWord_6596095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6596152 : List Nat := [2, 1, 2, 1, 4, 3, 1, 3, 6]
def baseStart_6596152 : Nat := 118140960795 + 6596152 * 2 ^ 59
def prefixEnd_6596152 : Nat := 4983230072969 + 3 ^ 40 * 6596152 * 2
def baseEnd_6596152 : Nat := 376332938457309084296095

theorem tailTrace_6596152 : CollatzResearch.WordTrace tailWord_6596152 prefixEnd_6596152 376332938457309084296095 := by
  unfold tailWord_6596152
  simp only [CollatzResearch.WordTrace]
  refine ⟨120290713999637655959415355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160387618666183541279220473 120290713999637655959415355)
  ·
    refine ⟨180436070999456483939123033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120290713999637655959415355 180436070999456483939123033)
    ·
      refine ⟨135327053249592362954342275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180436070999456483939123033 135327053249592362954342275)
      ·
        refine ⟨202990579874388544431513413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135327053249592362954342275 202990579874388544431513413)
        ·
          refine ⟨38060733726447852080908765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 202990579874388544431513413 38060733726447852080908765)
          ·
            refine ⟨14272775147417944530340787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38060733726447852080908765 14272775147417944530340787)
            ·
              refine ⟨21409162721126916795511181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14272775147417944530340787 21409162721126916795511181)
              ·
                refine ⟨8028436020422593798316693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21409162721126916795511181 8028436020422593798316693)
                ·
                  refine ⟨376332938457309084296095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8028436020422593798316693 376332938457309084296095)
                  ·
                    rfl

theorem cell23_6596152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 3, 6].length) (baseStart_6596152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6596152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6596152 prefixEnd_6596152 := by exact prefixLift 6596152
  have htrace : WordTrace (prefixWord ++ tailWord_6596152) baseStart_6596152 baseEnd_6596152 := by
    simpa [prefixWord, tailWord_6596152, baseEnd_6596152] using wordTrace_append hprefix tailTrace_6596152
  have hstable : (prefixWord ++ tailWord_6596152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6596152).length < 2 ^ (prefixWord ++ tailWord_6596152).sum := by decide
  have hdescent : baseEnd_6596152 < baseStart_6596152 := by decide
  rcases family_descends (prefixWord ++ tailWord_6596152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6596282 : List Nat := [3, 1, 1, 1, 2, 4, 1, 1, 2, 2, 5]
def baseStart_6596282 : Nat := 118140960795 + 6596282 * 2 ^ 59
def prefixEnd_6596282 : Nat := 4983230072969 + 3 ^ 40 * 6596282 * 2
def baseEnd_6596282 : Nat := 3387063198600866250039257

theorem tailTrace_6596282 : CollatzResearch.WordTrace tailWord_6596282 prefixEnd_6596282 3387063198600866250039257 := by
  unfold tailWord_6596282
  simp only [CollatzResearch.WordTrace]
  refine ⟨60146542372201086030265775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160390779659202896080708733 60146542372201086030265775)
  ·
    refine ⟨90219813558301629045398663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60146542372201086030265775 90219813558301629045398663)
    ·
      refine ⟨135329720337452443568097995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90219813558301629045398663 135329720337452443568097995)
      ·
        refine ⟨202994580506178665352146993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135329720337452443568097995 202994580506178665352146993)
        ·
          refine ⟨152245935379633999014110245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202994580506178665352146993 152245935379633999014110245)
          ·
            refine ⟨28546112883681374815145671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 152245935379633999014110245 28546112883681374815145671)
            ·
              refine ⟨42819169325522062222718507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28546112883681374815145671 42819169325522062222718507)
              ·
                refine ⟨64228753988283093334077761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42819169325522062222718507 64228753988283093334077761)
                ·
                  refine ⟨48171565491212320000558321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64228753988283093334077761 48171565491212320000558321)
                  ·
                    refine ⟨36128674118409240000418741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48171565491212320000558321 36128674118409240000418741)
                    ·
                      refine ⟨3387063198600866250039257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36128674118409240000418741 3387063198600866250039257)
                      ·
                        rfl

theorem cell23_6596282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 2, 2, 5].length) (baseStart_6596282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6596282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6596282 prefixEnd_6596282 := by exact prefixLift 6596282
  have htrace : WordTrace (prefixWord ++ tailWord_6596282) baseStart_6596282 baseEnd_6596282 := by
    simpa [prefixWord, tailWord_6596282, baseEnd_6596282] using wordTrace_append hprefix tailTrace_6596282
  have hstable : (prefixWord ++ tailWord_6596282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6596282).length < 2 ^ (prefixWord ++ tailWord_6596282).sum := by decide
  have hdescent : baseEnd_6596282 < baseStart_6596282 := by decide
  rcases family_descends (prefixWord ++ tailWord_6596282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6596286 : List Nat := [4, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3]
def baseStart_6596286 : Nat := 118140960795 + 6596286 * 2 ^ 59
def prefixEnd_6596286 : Nat := 4983230072969 + 3 ^ 40 * 6596286 * 2
def baseEnd_6596286 : Nat := 3387065252523484234389239

theorem tailTrace_6596286 : CollatzResearch.WordTrace tailWord_6596286 prefixEnd_6596286 3387065252523484234389239 := by
  unfold tailWord_6596286
  simp only [CollatzResearch.WordTrace]
  refine ⟨30073289422598731600526089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160390876920526568536139141 30073289422598731600526089)
  ·
    refine ⟨22554967066949048700394567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30073289422598731600526089 22554967066949048700394567)
    ·
      refine ⟨33832450600423573050591851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22554967066949048700394567 33832450600423573050591851)
      ·
        refine ⟨50748675900635359575887777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33832450600423573050591851 50748675900635359575887777)
        ·
          refine ⟨38061506925476519681915833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50748675900635359575887777 38061506925476519681915833)
          ·
            refine ⟨28546130194107389761436875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38061506925476519681915833 28546130194107389761436875)
            ·
              refine ⟨42819195291161084642155313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28546130194107389761436875 42819195291161084642155313)
              ·
                refine ⟨32114396468370813481616485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42819195291161084642155313 32114396468370813481616485)
                ·
                  refine ⟨6021449337819527527803091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32114396468370813481616485 6021449337819527527803091)
                  ·
                    refine ⟨9032174006729291291704637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6021449337819527527803091 9032174006729291291704637)
                    ·
                      refine ⟨3387065252523484234389239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9032174006729291291704637 3387065252523484234389239)
                      ·
                        rfl

theorem cell23_6596286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3].length) (baseStart_6596286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6596286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6596286 prefixEnd_6596286 := by exact prefixLift 6596286
  have htrace : WordTrace (prefixWord ++ tailWord_6596286) baseStart_6596286 baseEnd_6596286 := by
    simpa [prefixWord, tailWord_6596286, baseEnd_6596286] using wordTrace_append hprefix tailTrace_6596286
  have hstable : (prefixWord ++ tailWord_6596286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6596286).length < 2 ^ (prefixWord ++ tailWord_6596286).sum := by decide
  have hdescent : baseEnd_6596286 < baseStart_6596286 := by decide
  rcases family_descends (prefixWord ++ tailWord_6596286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6596290 : List Nat := [3, 5, 1, 2, 1, 1, 2, 1, 1, 1, 5]
def baseStart_6596290 : Nat := 118140960795 + 6596290 * 2 ^ 59
def prefixEnd_6596290 : Nat := 4983230072969 + 3 ^ 40 * 6596290 * 2
def baseEnd_6596290 : Nat := 3387067306446102218739221

theorem tailTrace_6596290 : CollatzResearch.WordTrace tailWord_6596290 prefixEnd_6596290 3387067306446102218739221 := by
  unfold tailWord_6596290
  simp only [CollatzResearch.WordTrace]
  refine ⟨60146615318193840371838581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160390974181850240991569549 60146615318193840371838581)
  ·
    refine ⟨5638745186080672534859867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60146615318193840371838581 5638745186080672534859867)
    ·
      refine ⟨8458117779121008802289801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5638745186080672534859867 8458117779121008802289801)
      ·
        refine ⟨6343588334340756601717351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8458117779121008802289801 6343588334340756601717351)
        ·
          refine ⟨9515382501511134902576027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6343588334340756601717351 9515382501511134902576027)
          ·
            refine ⟨14273073752266702353864041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9515382501511134902576027 14273073752266702353864041)
            ·
              refine ⟨10704805314200026765398031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14273073752266702353864041 10704805314200026765398031)
              ·
                refine ⟨16057207971300040148097047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10704805314200026765398031 16057207971300040148097047)
                ·
                  refine ⟨24085811956950060222145571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16057207971300040148097047 24085811956950060222145571)
                  ·
                    refine ⟨36128717935425090333218357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24085811956950060222145571 36128717935425090333218357)
                    ·
                      refine ⟨3387067306446102218739221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36128717935425090333218357 3387067306446102218739221)
                      ·
                        rfl

theorem cell23_6596290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_6596290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6596290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6596290 prefixEnd_6596290 := by exact prefixLift 6596290
  have htrace : WordTrace (prefixWord ++ tailWord_6596290) baseStart_6596290 baseEnd_6596290 := by
    simpa [prefixWord, tailWord_6596290, baseEnd_6596290] using wordTrace_append hprefix tailTrace_6596290
  have hstable : (prefixWord ++ tailWord_6596290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6596290).length < 2 ^ (prefixWord ++ tailWord_6596290).sum := by decide
  have hdescent : baseEnd_6596290 < baseStart_6596290 := by decide
  rcases family_descends (prefixWord ++ tailWord_6596290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6596296 : List Nat := [2, 1, 3, 1, 2, 2, 1, 5, 1, 3, 2]
def baseStart_6596296 : Nat := 118140960795 + 6596296 * 2 ^ 59
def prefixEnd_6596296 : Nat := 4983230072969 + 3 ^ 40 * 6596296 * 2
def baseEnd_6596296 : Nat := 3387070387330029195264193

theorem tailTrace_6596296 : CollatzResearch.WordTrace tailWord_6596296 prefixEnd_6596296 3387070387330029195264193 := by
  unfold tailWord_6596296
  simp only [CollatzResearch.WordTrace]
  refine ⟨120293340055376812256036371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160391120073835749674715161 120293340055376812256036371)
  ·
    refine ⟨180440010083065218384054557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120293340055376812256036371 180440010083065218384054557)
    ·
      refine ⟨67665003781149456894020459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180440010083065218384054557 67665003781149456894020459)
      ·
        refine ⟨101497505671724185341030689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67665003781149456894020459 101497505671724185341030689)
        ·
          refine ⟨76123129253793139005773017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101497505671724185341030689 76123129253793139005773017)
          ·
            refine ⟨57092346940344854254329763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76123129253793139005773017 57092346940344854254329763)
            ·
              refine ⟨85638520410517281381494645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57092346940344854254329763 85638520410517281381494645)
              ·
                refine ⟨8028611288485995129515123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85638520410517281381494645 8028611288485995129515123)
                ·
                  refine ⟨12042916932728992694272685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8028611288485995129515123 12042916932728992694272685)
                  ·
                    refine ⟨4516093849773372260352257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12042916932728992694272685 4516093849773372260352257)
                    ·
                      refine ⟨3387070387330029195264193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4516093849773372260352257 3387070387330029195264193)
                      ·
                        rfl

theorem cell23_6596296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 5, 1, 3, 2].length) (baseStart_6596296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6596296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6596296 prefixEnd_6596296 := by exact prefixLift 6596296
  have htrace : WordTrace (prefixWord ++ tailWord_6596296) baseStart_6596296 baseEnd_6596296 := by
    simpa [prefixWord, tailWord_6596296, baseEnd_6596296] using wordTrace_append hprefix tailTrace_6596296
  have hstable : (prefixWord ++ tailWord_6596296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6596296).length < 2 ^ (prefixWord ++ tailWord_6596296).sum := by decide
  have hdescent : baseEnd_6596296 < baseStart_6596296 := by decide
  rcases family_descends (prefixWord ++ tailWord_6596296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6596312 : List Nat := [2, 1, 2, 2, 3, 1, 1, 2, 1, 3, 5]
def baseStart_6596312 : Nat := 118140960795 + 6596312 * 2 ^ 59
def prefixEnd_6596312 : Nat := 4983230072969 + 3 ^ 40 * 6596312 * 2
def baseEnd_6596312 : Nat := 3387078603020501132664119

theorem tailTrace_6596312 : CollatzResearch.WordTrace tailWord_6596312 prefixEnd_6596312 3387078603020501132664119 := by
  unfold tailWord_6596312
  simp only [CollatzResearch.WordTrace]
  refine ⟨120293631839347829622327595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160391509119130439496436793 120293631839347829622327595)
  ·
    refine ⟨180440447759021744433491393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120293631839347829622327595 180440447759021744433491393)
    ·
      refine ⟨135330335819266308325118545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180440447759021744433491393 135330335819266308325118545)
      ·
        refine ⟨101497751864449731243838909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135330335819266308325118545 101497751864449731243838909)
        ·
          refine ⟨38061656949168649216439591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101497751864449731243838909 38061656949168649216439591)
          ·
            refine ⟨57092485423752973824659387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38061656949168649216439591 57092485423752973824659387)
            ·
              refine ⟨85638728135629460736989081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57092485423752973824659387 85638728135629460736989081)
              ·
                refine ⟨64229046101722095552741811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85638728135629460736989081 64229046101722095552741811)
                ·
                  refine ⟨96343569152583143329112717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64229046101722095552741811 96343569152583143329112717)
                  ·
                    refine ⟨36128838432218678748417269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 96343569152583143329112717 36128838432218678748417269)
                    ·
                      refine ⟨3387078603020501132664119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36128838432218678748417269 3387078603020501132664119)
                      ·
                        rfl

theorem cell23_6596312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 1, 3, 5].length) (baseStart_6596312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6596312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6596312 prefixEnd_6596312 := by exact prefixLift 6596312
  have htrace : WordTrace (prefixWord ++ tailWord_6596312) baseStart_6596312 baseEnd_6596312 := by
    simpa [prefixWord, tailWord_6596312, baseEnd_6596312] using wordTrace_append hprefix tailTrace_6596312
  have hstable : (prefixWord ++ tailWord_6596312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6596312).length < 2 ^ (prefixWord ++ tailWord_6596312).sum := by decide
  have hdescent : baseEnd_6596312 < baseStart_6596312 := by decide
  rcases family_descends (prefixWord ++ tailWord_6596312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6596332 : List Nat := [2, 2, 1, 1, 2, 2, 2, 4, 7]
def baseStart_6596332 : Nat := 118140960795 + 6596332 * 2 ^ 59
def prefixEnd_6596332 : Nat := 4983230072969 + 3 ^ 40 * 6596332 * 2
def baseEnd_6596332 : Nat := 376343208070399006046003

theorem tailTrace_6596332 : CollatzResearch.WordTrace tailWord_6596332 prefixEnd_6596332 376343208070399006046003 := by
  unfold tailWord_6596332
  simp only [CollatzResearch.WordTrace]
  refine ⟨120293996569311601330191625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160391995425748801773588833 120293996569311601330191625)
  ·
    refine ⟨90220497426983700997643719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120293996569311601330191625 90220497426983700997643719)
    ·
      refine ⟨135330746140475551496465579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90220497426983700997643719 135330746140475551496465579)
      ·
        refine ⟨202996119210713327244698369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135330746140475551496465579 202996119210713327244698369)
        ·
          refine ⟨152247089408034995433523777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202996119210713327244698369 152247089408034995433523777)
          ·
            refine ⟨114185317056026246575142833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152247089408034995433523777 114185317056026246575142833)
            ·
              refine ⟨85638987792019684931357125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114185317056026246575142833 85638987792019684931357125)
              ·
                refine ⟨16057310211003690924629461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85638987792019684931357125 16057310211003690924629461)
                ·
                  refine ⟨376343208070399006046003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16057310211003690924629461 376343208070399006046003)
                  ·
                    rfl

theorem cell23_6596332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 7].length) (baseStart_6596332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6596332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6596332 prefixEnd_6596332 := by exact prefixLift 6596332
  have htrace : WordTrace (prefixWord ++ tailWord_6596332) baseStart_6596332 baseEnd_6596332 := by
    simpa [prefixWord, tailWord_6596332, baseEnd_6596332] using wordTrace_append hprefix tailTrace_6596332
  have hstable : (prefixWord ++ tailWord_6596332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6596332).length < 2 ^ (prefixWord ++ tailWord_6596332).sum := by decide
  have hdescent : baseEnd_6596332 < baseStart_6596332 := by decide
  rcases family_descends (prefixWord ++ tailWord_6596332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6596386 : List Nat := [3, 3, 1, 1, 2, 1, 1, 2, 2, 5, 2]
def baseStart_6596386 : Nat := 118140960795 + 6596386 * 2 ^ 59
def prefixEnd_6596386 : Nat := 4983230072969 + 3 ^ 40 * 6596386 * 2
def baseEnd_6596386 : Nat := 3387116600588933843138779

theorem tailTrace_6596386 : CollatzResearch.WordTrace tailWord_6596386 prefixEnd_6596386 3387116600588933843138779 := by
  unfold tailWord_6596386
  simp only [CollatzResearch.WordTrace]
  refine ⟨60147490670106892470712253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160393308453618379921899341 60147490670106892470712253)
  ·
    refine ⟨22555309001290084676517095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60147490670106892470712253 22555309001290084676517095)
    ·
      refine ⟨33832963501935127014775643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22555309001290084676517095 33832963501935127014775643)
      ·
        refine ⟨50749445252902690522163465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33832963501935127014775643 50749445252902690522163465)
        ·
          refine ⟨38062083939677017891622599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50749445252902690522163465 38062083939677017891622599)
          ·
            refine ⟨57093125909515526837433899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38062083939677017891622599 57093125909515526837433899)
            ·
              refine ⟨85639688864273290256150849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57093125909515526837433899 85639688864273290256150849)
              ·
                refine ⟨64229766648204967692113137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85639688864273290256150849 64229766648204967692113137)
                ·
                  refine ⟨48172324986153725769084853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64229766648204967692113137 48172324986153725769084853)
                  ·
                    refine ⟨4516155467451911790851705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48172324986153725769084853 4516155467451911790851705)
                    ·
                      refine ⟨3387116600588933843138779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4516155467451911790851705 3387116600588933843138779)
                      ·
                        rfl

theorem cell23_6596386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 2, 5, 2].length) (baseStart_6596386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6596386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6596386 prefixEnd_6596386 := by exact prefixLift 6596386
  have htrace : WordTrace (prefixWord ++ tailWord_6596386) baseStart_6596386 baseEnd_6596386 := by
    simpa [prefixWord, tailWord_6596386, baseEnd_6596386] using wordTrace_append hprefix tailTrace_6596386
  have hstable : (prefixWord ++ tailWord_6596386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6596386).length < 2 ^ (prefixWord ++ tailWord_6596386).sum := by decide
  have hdescent : baseEnd_6596386 < baseStart_6596386 := by decide
  rcases family_descends (prefixWord ++ tailWord_6596386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6596396 : List Nat := [2, 2, 1, 1, 1, 7, 1, 1, 2, 5]
def baseStart_6596396 : Nat := 118140960795 + 6596396 * 2 ^ 59
def prefixEnd_6596396 : Nat := 4983230072969 + 3 ^ 40 * 6596396 * 2
def baseEnd_6596396 : Nat := 1129040578465159601337911

theorem tailTrace_6596396 : CollatzResearch.WordTrace tailWord_6596396 prefixEnd_6596396 1129040578465159601337911 := by
  unfold tailWord_6596396
  simp only [CollatzResearch.WordTrace]
  refine ⟨120295163705195670795356521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160393551606927561060475361 120295163705195670795356521)
  ·
    refine ⟨90221372778896753096517391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120295163705195670795356521 90221372778896753096517391)
    ·
      refine ⟨135332059168345129644776087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90221372778896753096517391 135332059168345129644776087)
      ·
        refine ⟨202998088752517694467164131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135332059168345129644776087 202998088752517694467164131)
        ·
          refine ⟨304497133128776541700746197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202998088752517694467164131 304497133128776541700746197)
          ·
            refine ⟨7136651557705700196111239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 304497133128776541700746197 7136651557705700196111239)
            ·
              refine ⟨10704977336558550294166859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7136651557705700196111239 10704977336558550294166859)
              ·
                refine ⟨16057466004837825441250289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10704977336558550294166859 16057466004837825441250289)
                ·
                  refine ⟨12043099503628369080937717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16057466004837825441250289 12043099503628369080937717)
                  ·
                    refine ⟨1129040578465159601337911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12043099503628369080937717 1129040578465159601337911)
                    ·
                      rfl

theorem cell23_6596396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 5].length) (baseStart_6596396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6596396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6596396 prefixEnd_6596396 := by exact prefixLift 6596396
  have htrace : WordTrace (prefixWord ++ tailWord_6596396) baseStart_6596396 baseEnd_6596396 := by
    simpa [prefixWord, tailWord_6596396, baseEnd_6596396] using wordTrace_append hprefix tailTrace_6596396
  have hstable : (prefixWord ++ tailWord_6596396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6596396).length < 2 ^ (prefixWord ++ tailWord_6596396).sum := by decide
  have hdescent : baseEnd_6596396 < baseStart_6596396 := by decide
  rcases family_descends (prefixWord ++ tailWord_6596396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6596426 : List Nat := [3, 1, 2, 1, 1, 1, 6, 1, 3, 4]
def baseStart_6596426 : Nat := 118140960795 + 6596426 * 2 ^ 59
def prefixEnd_6596426 : Nat := 4983230072969 + 3 ^ 40 * 6596426 * 2
def baseEnd_6596426 : Nat := 1129045713271704562212865

theorem tailTrace_6596426 : CollatzResearch.WordTrace tailWord_6596426 prefixEnd_6596426 1129045713271704562212865 := by
  unfold tailWord_6596426
  simp only [CollatzResearch.WordTrace]
  refine ⟨60147855400070664178576283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160394281066855104476203421 60147855400070664178576283)
  ·
    refine ⟨90221783100105996267864425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60147855400070664178576283 90221783100105996267864425)
    ·
      refine ⟨67666337325079497200898319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90221783100105996267864425 67666337325079497200898319)
      ·
        refine ⟨101499505987619245801347479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67666337325079497200898319 101499505987619245801347479)
        ·
          refine ⟨152249258981428868702021219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101499505987619245801347479 152249258981428868702021219)
          ·
            refine ⟨228373888472143303053031829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152249258981428868702021219 228373888472143303053031829)
            ·
              refine ⟨10705026022131717330610867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 228373888472143303053031829 10705026022131717330610867)
              ·
                refine ⟨16057539033197575995916301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10705026022131717330610867 16057539033197575995916301)
                ·
                  refine ⟨6021577137449090998468613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16057539033197575995916301 6021577137449090998468613)
                  ·
                    refine ⟨1129045713271704562212865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6021577137449090998468613 1129045713271704562212865)
                    ·
                      rfl

theorem cell23_6596426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 1, 3, 4].length) (baseStart_6596426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6596426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6596426 prefixEnd_6596426 := by exact prefixLift 6596426
  have htrace : WordTrace (prefixWord ++ tailWord_6596426) baseStart_6596426 baseEnd_6596426 := by
    simpa [prefixWord, tailWord_6596426, baseEnd_6596426] using wordTrace_append hprefix tailTrace_6596426
  have hstable : (prefixWord ++ tailWord_6596426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6596426).length < 2 ^ (prefixWord ++ tailWord_6596426).sum := by decide
  have hdescent : baseEnd_6596426 < baseStart_6596426 := by decide
  rcases family_descends (prefixWord ++ tailWord_6596426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6596436 : List Nat := [2, 4, 1, 1, 3, 1, 1, 2, 1, 4, 3]
def baseStart_6596436 : Nat := 118140960795 + 6596436 * 2 ^ 59
def prefixEnd_6596436 : Nat := 4983230072969 + 3 ^ 40 * 6596436 * 2
def baseEnd_6596436 : Nat := 3387142274621658647513549

theorem tailTrace_6596436 : CollatzResearch.WordTrace tailWord_6596436 prefixEnd_6596436 3387142274621658647513549 := by
  unfold tailWord_6596436
  simp only [CollatzResearch.WordTrace]
  refine ⟨120295893165123214211084581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160394524220164285614779441 120295893165123214211084581)
  ·
    refine ⟨22555479968460602664578359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120295893165123214211084581 22555479968460602664578359)
    ·
      refine ⟨33833219952690903996867539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22555479968460602664578359 33833219952690903996867539)
      ·
        refine ⟨50749829929036355995301309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33833219952690903996867539 50749829929036355995301309)
        ·
          refine ⟨19031186223388633498237991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50749829929036355995301309 19031186223388633498237991)
          ·
            refine ⟨28546779335082950247356987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19031186223388633498237991 28546779335082950247356987)
            ·
              refine ⟨42820169002624425371035481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28546779335082950247356987 42820169002624425371035481)
              ·
                refine ⟨32115126751968319028276611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42820169002624425371035481 32115126751968319028276611)
                ·
                  refine ⟨48172690127952478542414917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32115126751968319028276611 48172690127952478542414917)
                  ·
                    refine ⟨9032379398991089726702797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48172690127952478542414917 9032379398991089726702797)
                    ·
                      refine ⟨3387142274621658647513549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9032379398991089726702797 3387142274621658647513549)
                      ·
                        rfl

theorem cell23_6596436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 2, 1, 4, 3].length) (baseStart_6596436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6596436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6596436 prefixEnd_6596436 := by exact prefixLift 6596436
  have htrace : WordTrace (prefixWord ++ tailWord_6596436) baseStart_6596436 baseEnd_6596436 := by
    simpa [prefixWord, tailWord_6596436, baseEnd_6596436] using wordTrace_append hprefix tailTrace_6596436
  have hstable : (prefixWord ++ tailWord_6596436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6596436).length < 2 ^ (prefixWord ++ tailWord_6596436).sum := by decide
  have hdescent : baseEnd_6596436 < baseStart_6596436 := by decide
  rcases family_descends (prefixWord ++ tailWord_6596436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6596449 : List Nat := [1, 2, 3, 1, 1, 1, 3, 1, 2, 5, 3]
def baseStart_6596449 : Nat := 118140960795 + 6596449 * 2 ^ 59
def prefixEnd_6596449 : Nat := 4983230072969 + 3 ^ 40 * 6596449 * 2
def baseEnd_6596449 : Nat := 3387148949870167096650989

theorem tailTrace_6596449 : CollatzResearch.WordTrace tailWord_6596449 prefixEnd_6596449 3387148949870167096650989 := by
  unfold tailWord_6596449
  simp only [CollatzResearch.WordTrace]
  refine ⟨240592260479199331642392401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160394840319466221094928267 240592260479199331642392401)
  ·
    refine ⟨180444195359399498731794301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240592260479199331642392401 180444195359399498731794301)
    ·
      refine ⟨67666573259774812024422863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180444195359399498731794301 67666573259774812024422863)
      ·
        refine ⟨101499859889662218036634295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67666573259774812024422863 101499859889662218036634295)
        ·
          refine ⟨152249789834493327054951443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101499859889662218036634295 152249789834493327054951443)
          ·
            refine ⟨228374684751739990582427165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152249789834493327054951443 228374684751739990582427165)
            ·
              refine ⟨85640506781902496468410187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 228374684751739990582427165 85640506781902496468410187)
              ·
                refine ⟨128460760172853744702615281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85640506781902496468410187 128460760172853744702615281)
                ·
                  refine ⟨96345570129640308526961461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 128460760172853744702615281 96345570129640308526961461)
                  ·
                    refine ⟨9032397199653778924402637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 96345570129640308526961461 9032397199653778924402637)
                    ·
                      refine ⟨3387148949870167096650989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9032397199653778924402637 3387148949870167096650989)
                      ·
                        rfl

theorem cell23_6596449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 5, 3].length) (baseStart_6596449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6596449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6596449 prefixEnd_6596449 := by exact prefixLift 6596449
  have htrace : WordTrace (prefixWord ++ tailWord_6596449) baseStart_6596449 baseEnd_6596449 := by
    simpa [prefixWord, tailWord_6596449, baseEnd_6596449] using wordTrace_append hprefix tailTrace_6596449
  have hstable : (prefixWord ++ tailWord_6596449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6596449).length < 2 ^ (prefixWord ++ tailWord_6596449).sum := by decide
  have hdescent : baseEnd_6596449 < baseStart_6596449 := by decide
  rcases family_descends (prefixWord ++ tailWord_6596449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6596460 : List Nat := [2, 2, 1, 1, 4, 4, 1, 3, 1, 4]
def baseStart_6596460 : Nat := 118140960795 + 6596460 * 2 ^ 59
def prefixEnd_6596460 : Nat := 4983230072969 + 3 ^ 40 * 6596460 * 2
def baseEnd_6596460 : Nat := 1129051532719122184537813

theorem tailTrace_6596460 : CollatzResearch.WordTrace tailWord_6596460 prefixEnd_6596460 1129051532719122184537813 := by
  unfold tailWord_6596460
  simp only [CollatzResearch.WordTrace]
  refine ⟨120296330841079740260521417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160395107788106320347361889 120296330841079740260521417)
  ·
    refine ⟨90222248130809805195391063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120296330841079740260521417 90222248130809805195391063)
    ·
      refine ⟨135333372196214707793086595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90222248130809805195391063 135333372196214707793086595)
      ·
        refine ⟨203000058294322061689629893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135333372196214707793086595 203000058294322061689629893)
        ·
          refine ⟨38062510930185386566805605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 203000058294322061689629893 38062510930185386566805605)
          ·
            refine ⟨7136720799409759981276051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38062510930185386566805605 7136720799409759981276051)
            ·
              refine ⟨10705081199114639971914077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7136720799409759981276051 10705081199114639971914077)
              ·
                refine ⟨4014405449667989989467779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10705081199114639971914077 4014405449667989989467779)
                ·
                  refine ⟨6021608174501984984201669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4014405449667989989467779 6021608174501984984201669)
                  ·
                    refine ⟨1129051532719122184537813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6021608174501984984201669 1129051532719122184537813)
                    ·
                      rfl

theorem cell23_6596460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 3, 1, 4].length) (baseStart_6596460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6596460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6596460 prefixEnd_6596460 := by exact prefixLift 6596460
  have htrace : WordTrace (prefixWord ++ tailWord_6596460) baseStart_6596460 baseEnd_6596460 := by
    simpa [prefixWord, tailWord_6596460, baseEnd_6596460] using wordTrace_append hprefix tailTrace_6596460
  have hstable : (prefixWord ++ tailWord_6596460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6596460).length < 2 ^ (prefixWord ++ tailWord_6596460).sum := by decide
  have hdescent : baseEnd_6596460 < baseStart_6596460 := by decide
  rcases family_descends (prefixWord ++ tailWord_6596460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6596470 : List Nat := [5, 1, 1, 3, 2, 1, 1, 2, 2, 2, 3]
def baseStart_6596470 : Nat := 118140960795 + 6596470 * 2 ^ 59
def prefixEnd_6596470 : Nat := 4983230072969 + 3 ^ 40 * 6596470 * 2
def baseEnd_6596470 : Nat := 3387159732963911514488393

theorem tailTrace_6596470 : CollatzResearch.WordTrace tailWord_6596470 prefixEnd_6596470 3387159732963911514488393 := by
  unfold tailWord_6596470
  simp only [CollatzResearch.WordTrace]
  refine ⟨15037064150757703264306679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 160395350941415501485937909 15037064150757703264306679)
  ·
    refine ⟨22555596226136554896460019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15037064150757703264306679 22555596226136554896460019)
    ·
      refine ⟨33833394339204832344690029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22555596226136554896460019 33833394339204832344690029)
      ·
        refine ⟨12687522877201812129258761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33833394339204832344690029 12687522877201812129258761)
        ·
          refine ⟨9515642157901359096944071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12687522877201812129258761 9515642157901359096944071)
          ·
            refine ⟨14273463236852038645416107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9515642157901359096944071 14273463236852038645416107)
            ·
              refine ⟨21410194855278057968124161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14273463236852038645416107 21410194855278057968124161)
              ·
                refine ⟨16057646141458543476093121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21410194855278057968124161 16057646141458543476093121)
                ·
                  refine ⟨12043234606093907607069841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16057646141458543476093121 12043234606093907607069841)
                  ·
                    refine ⟨9032425954570430705302381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12043234606093907607069841 9032425954570430705302381)
                    ·
                      refine ⟨3387159732963911514488393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9032425954570430705302381 3387159732963911514488393)
                      ·
                        rfl

theorem cell23_6596470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_6596470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6596470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6596470 prefixEnd_6596470 := by exact prefixLift 6596470
  have htrace : WordTrace (prefixWord ++ tailWord_6596470) baseStart_6596470 baseEnd_6596470 := by
    simpa [prefixWord, tailWord_6596470, baseEnd_6596470] using wordTrace_append hprefix tailTrace_6596470
  have hstable : (prefixWord ++ tailWord_6596470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6596470).length < 2 ^ (prefixWord ++ tailWord_6596470).sum := by decide
  have hdescent : baseEnd_6596470 < baseStart_6596470 := by decide
  rcases family_descends (prefixWord ++ tailWord_6596470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6596483 : List Nat := [1, 1, 1, 3, 4, 2, 3, 1, 3, 1, 3]
def baseStart_6596483 : Nat := 118140960795 + 6596483 * 2 ^ 59
def prefixEnd_6596483 : Nat := 4983230072969 + 3 ^ 40 * 6596483 * 2
def baseEnd_6596483 : Nat := 3387166408212419963625833

theorem tailTrace_6596483 : CollatzResearch.WordTrace tailWord_6596483 prefixEnd_6596483 3387166408212419963625833 := by
  unfold tailWord_6596483
  simp only [CollatzResearch.WordTrace]
  refine ⟨240593500561076155449130103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160395667040717436966086735 240593500561076155449130103)
  ·
    refine ⟨360890250841614233173695155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240593500561076155449130103 360890250841614233173695155)
    ·
      refine ⟨541335376262421349760542733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360890250841614233173695155 541335376262421349760542733)
      ·
        refine ⟨203000766098408006160203525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 541335376262421349760542733 203000766098408006160203525)
        ·
          refine ⟨38062643643451501155038161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 203000766098408006160203525 38062643643451501155038161)
          ·
            refine ⟨28546982732588625866278621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38062643643451501155038161 28546982732588625866278621)
            ·
              refine ⟨10705118524720734699854483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28546982732588625866278621 10705118524720734699854483)
              ·
                refine ⟨16057677787081102049781725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10705118524720734699854483 16057677787081102049781725)
                ·
                  refine ⟨6021629170155413268668147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16057677787081102049781725 6021629170155413268668147)
                  ·
                    refine ⟨9032443755233119903002221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6021629170155413268668147 9032443755233119903002221)
                    ·
                      refine ⟨3387166408212419963625833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9032443755233119903002221 3387166408212419963625833)
                      ·
                        rfl

theorem cell23_6596483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 1, 3, 1, 3].length) (baseStart_6596483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6596483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6596483 prefixEnd_6596483 := by exact prefixLift 6596483
  have htrace : WordTrace (prefixWord ++ tailWord_6596483) baseStart_6596483 baseEnd_6596483 := by
    simpa [prefixWord, tailWord_6596483, baseEnd_6596483] using wordTrace_append hprefix tailTrace_6596483
  have hstable : (prefixWord ++ tailWord_6596483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6596483).length < 2 ^ (prefixWord ++ tailWord_6596483).sum := by decide
  have hdescent : baseEnd_6596483 < baseStart_6596483 := by decide
  rcases family_descends (prefixWord ++ tailWord_6596483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6596490 : List Nat := [3, 1, 2, 4, 2, 2, 2, 1, 6]
def baseStart_6596490 : Nat := 118140960795 + 6596490 * 2 ^ 59
def prefixEnd_6596490 : Nat := 4983230072969 + 3 ^ 40 * 6596490 * 2
def baseEnd_6596490 : Nat := 376352222508555715137589

theorem tailTrace_6596490 : CollatzResearch.WordTrace tailWord_6596490 prefixEnd_6596490 376352222508555715137589 := by
  unfold tailWord_6596490
  simp only [CollatzResearch.WordTrace]
  refine ⟨60148438968012698911158731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160395837248033863763089949 60148438968012698911158731)
  ·
    refine ⟨90222658452019048366738097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60148438968012698911158731 90222658452019048366738097)
    ·
      refine ⟨67666993839014286275053573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90222658452019048366738097 67666993839014286275053573)
      ·
        refine ⟨12687561344815178676572545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67666993839014286275053573 12687561344815178676572545)
        ·
          refine ⟨9515671008611384007429409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12687561344815178676572545 9515671008611384007429409)
          ·
            refine ⟨7136753256458538005572057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9515671008611384007429409 7136753256458538005572057)
            ·
              refine ⟨5352564942343903504179043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7136753256458538005572057 5352564942343903504179043)
              ·
                refine ⟨8028847413515855256268565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5352564942343903504179043 8028847413515855256268565)
                ·
                  refine ⟨376352222508555715137589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8028847413515855256268565 376352222508555715137589)
                  ·
                    rfl

theorem cell23_6596490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 2, 1, 6].length) (baseStart_6596490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6596490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6596490 prefixEnd_6596490 := by exact prefixLift 6596490
  have htrace : WordTrace (prefixWord ++ tailWord_6596490) baseStart_6596490 baseEnd_6596490 := by
    simpa [prefixWord, tailWord_6596490, baseEnd_6596490] using wordTrace_append hprefix tailTrace_6596490
  have hstable : (prefixWord ++ tailWord_6596490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6596490).length < 2 ^ (prefixWord ++ tailWord_6596490).sum := by decide
  have hdescent : baseEnd_6596490 < baseStart_6596490 := by decide
  rcases family_descends (prefixWord ++ tailWord_6596490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6596503 : List Nat := [1, 1, 3, 3, 1, 5, 1, 2, 1, 5]
def baseStart_6596503 : Nat := 118140960795 + 6596503 * 2 ^ 59
def prefixEnd_6596503 : Nat := 4983230072969 + 3 ^ 40 * 6596503 * 2
def baseEnd_6596503 : Nat := 1129058892608503295125247

theorem tailTrace_6596503 : CollatzResearch.WordTrace tailWord_6596503 prefixEnd_6596503 1129058892608503295125247 := by
  unfold tailWord_6596503
  simp only [CollatzResearch.WordTrace]
  refine ⟨240594230021003698864858163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160396153347335799243238775 240594230021003698864858163)
  ·
    refine ⟨360891345031505548297287245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240594230021003698864858163 360891345031505548297287245)
    ·
      refine ⟨135334254386814580611482717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 360891345031505548297287245 135334254386814580611482717)
      ·
        refine ⟨50750345395055467729306019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135334254386814580611482717 50750345395055467729306019)
        ·
          refine ⟨76125518092583201593959029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50750345395055467729306019 76125518092583201593959029)
          ·
            refine ⟨7136767321179675149433659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76125518092583201593959029 7136767321179675149433659)
            ·
              refine ⟨10705150981769512724150489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7136767321179675149433659 10705150981769512724150489)
              ·
                refine ⟨8028863236327134543112867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10705150981769512724150489 8028863236327134543112867)
                ·
                  refine ⟨12043294854490701814669301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8028863236327134543112867 12043294854490701814669301)
                  ·
                    refine ⟨1129058892608503295125247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12043294854490701814669301 1129058892608503295125247)
                    ·
                      rfl

theorem cell23_6596503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 2, 1, 5].length) (baseStart_6596503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6596503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6596503 prefixEnd_6596503 := by exact prefixLift 6596503
  have htrace : WordTrace (prefixWord ++ tailWord_6596503) baseStart_6596503 baseEnd_6596503 := by
    simpa [prefixWord, tailWord_6596503, baseEnd_6596503] using wordTrace_append hprefix tailTrace_6596503
  have hstable : (prefixWord ++ tailWord_6596503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6596503).length < 2 ^ (prefixWord ++ tailWord_6596503).sum := by decide
  have hdescent : baseEnd_6596503 < baseStart_6596503 := by decide
  rcases family_descends (prefixWord ++ tailWord_6596503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6596516 : List Nat := [2, 3, 1, 2, 1, 4, 1, 2, 1, 6]
def baseStart_6596516 : Nat := 118140960795 + 6596516 * 2 ^ 59
def prefixEnd_6596516 : Nat := 4983230072969 + 3 ^ 40 * 6596516 * 2
def baseEnd_6596516 : Nat := 1129061117691339444837727

theorem tailTrace_6596516 : CollatzResearch.WordTrace tailWord_6596516 prefixEnd_6596516 1129061117691339444837727 := by
  unfold tailWord_6596516
  simp only [CollatzResearch.WordTrace]
  refine ⟨120297352084978301042540701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160396469446637734723387601 120297352084978301042540701)
  ·
    refine ⟨45111507031866862890952763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120297352084978301042540701 45111507031866862890952763)
    ·
      refine ⟨67667260547800294336429145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45111507031866862890952763 67667260547800294336429145)
      ·
        refine ⟨50750445410850220752321859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67667260547800294336429145 50750445410850220752321859)
        ·
          refine ⟨76125668116275331128482789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50750445410850220752321859 76125668116275331128482789)
          ·
            refine ⟨14273562771801624586590523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76125668116275331128482789 14273562771801624586590523)
            ·
              refine ⟨21410344157702436879885785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14273562771801624586590523 21410344157702436879885785)
              ·
                refine ⟨16057758118276827659914339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21410344157702436879885785 16057758118276827659914339)
                ·
                  refine ⟨24086637177415241489871509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16057758118276827659914339 24086637177415241489871509)
                  ·
                    refine ⟨1129061117691339444837727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24086637177415241489871509 1129061117691339444837727)
                    ·
                      rfl

theorem cell23_6596516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 2, 1, 6].length) (baseStart_6596516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6596516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6596516 prefixEnd_6596516 := by exact prefixLift 6596516
  have htrace : WordTrace (prefixWord ++ tailWord_6596516) baseStart_6596516 baseEnd_6596516 := by
    simpa [prefixWord, tailWord_6596516, baseEnd_6596516] using wordTrace_append hprefix tailTrace_6596516
  have hstable : (prefixWord ++ tailWord_6596516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6596516).length < 2 ^ (prefixWord ++ tailWord_6596516).sum := by decide
  have hdescent : baseEnd_6596516 < baseStart_6596516 := by decide
  rcases family_descends (prefixWord ++ tailWord_6596516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6596529 : List Nat := [1, 2, 2, 4, 2, 12]
def baseStart_6596529 : Nat := 118140960795 + 6596529 * 2 ^ 59
def prefixEnd_6596529 : Nat := 4983230072969 + 3 ^ 40 * 6596529 * 2
def baseEnd_6596529 : Nat := 13939053614495994994447

theorem tailTrace_6596529 : CollatzResearch.WordTrace tailWord_6596529 prefixEnd_6596529 13939053614495994994447 := by
  unfold tailWord_6596529
  simp only [CollatzResearch.WordTrace]
  refine ⟨240595178318909505305304641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160396785545939670203536427 240595178318909505305304641)
  ·
    refine ⟨180446383739182128978978481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240595178318909505305304641 180446383739182128978978481)
    ·
      refine ⟨135334787804386596734233861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180446383739182128978978481 135334787804386596734233861)
      ·
        refine ⟨25375272713322486887668849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135334787804386596734233861 25375272713322486887668849)
        ·
          refine ⟨19031454534991865165751637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25375272713322486887668849 19031454534991865165751637)
          ·
            refine ⟨13939053614495994994447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 19031454534991865165751637 13939053614495994994447)
            ·
              rfl

theorem cell23_6596529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 12].length) (baseStart_6596529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6596529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6596529 prefixEnd_6596529 := by exact prefixLift 6596529
  have htrace : WordTrace (prefixWord ++ tailWord_6596529) baseStart_6596529 baseEnd_6596529 := by
    simpa [prefixWord, tailWord_6596529, baseEnd_6596529] using wordTrace_append hprefix tailTrace_6596529
  have hstable : (prefixWord ++ tailWord_6596529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6596529).length < 2 ^ (prefixWord ++ tailWord_6596529).sum := by decide
  have hdescent : baseEnd_6596529 < baseStart_6596529 := by decide
  rcases family_descends (prefixWord ++ tailWord_6596529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6596533 : List Nat := [1, 3, 3, 2, 1, 2, 1, 4, 2, 4]
def baseStart_6596533 : Nat := 118140960795 + 6596533 * 2 ^ 59
def prefixEnd_6596533 : Nat := 4983230072969 + 3 ^ 40 * 6596533 * 2
def baseEnd_6596533 : Nat := 1129064027415048256000201

theorem tailTrace_6596533 : CollatzResearch.WordTrace tailWord_6596533 prefixEnd_6596533 1129064027415048256000201 := by
  unfold tailWord_6596533
  simp only [CollatzResearch.WordTrace]
  refine ⟨240595324210895013988450253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160396882807263342658966835 240595324210895013988450253)
  ·
    refine ⟨90223246579085630245668845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 240595324210895013988450253 90223246579085630245668845)
    ·
      refine ⟨33833717467157111342125817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90223246579085630245668845 33833717467157111342125817)
      ·
        refine ⟨25375288100367833506594363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33833717467157111342125817 25375288100367833506594363)
        ·
          refine ⟨38062932150551750259891545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25375288100367833506594363 38062932150551750259891545)
          ·
            refine ⟨28547199112913812694918659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38062932150551750259891545 28547199112913812694918659)
            ·
              refine ⟨42820798669370719042377989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28547199112913812694918659 42820798669370719042377989)
              ·
                refine ⟨8028899750507009820445873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42820798669370719042377989 8028899750507009820445873)
                ·
                  refine ⟨6021674812880257365334405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8028899750507009820445873 6021674812880257365334405)
                  ·
                    refine ⟨1129064027415048256000201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6021674812880257365334405 1129064027415048256000201)
                    ·
                      rfl

theorem cell23_6596533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 4, 2, 4].length) (baseStart_6596533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6596533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6596533 prefixEnd_6596533 := by exact prefixLift 6596533
  have htrace : WordTrace (prefixWord ++ tailWord_6596533) baseStart_6596533 baseEnd_6596533 := by
    simpa [prefixWord, tailWord_6596533, baseEnd_6596533] using wordTrace_append hprefix tailTrace_6596533
  have hstable : (prefixWord ++ tailWord_6596533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6596533).length < 2 ^ (prefixWord ++ tailWord_6596533).sum := by decide
  have hdescent : baseEnd_6596533 < baseStart_6596533 := by decide
  rcases family_descends (prefixWord ++ tailWord_6596533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6596559 : List Nat := [1, 1, 2, 1, 1, 5, 1, 2, 2, 7]
def baseStart_6596559 : Nat := 118140960795 + 6596559 * 2 ^ 59
def prefixEnd_6596559 : Nat := 4983230072969 + 3 ^ 40 * 6596559 * 2
def baseEnd_6596559 : Nat := 1129068477580720555425161

theorem tailTrace_6596559 : CollatzResearch.WordTrace tailWord_6596559 prefixEnd_6596559 1129068477580720555425161 := by
  unfold tailWord_6596559
  simp only [CollatzResearch.WordTrace]
  refine ⟨240596272508800820428896731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160397515005867213619264487 240596272508800820428896731)
  ·
    refine ⟨360894408763201230643345097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240596272508800820428896731 360894408763201230643345097)
    ·
      refine ⟨270670806572400922982508823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 360894408763201230643345097 270670806572400922982508823)
      ·
        refine ⟨406006209858601384473763235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270670806572400922982508823 406006209858601384473763235)
        ·
          refine ⟨609009314787902076710644853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 406006209858601384473763235 609009314787902076710644853)
          ·
            refine ⟨57094623261365819691622955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 609009314787902076710644853 57094623261365819691622955)
            ·
              refine ⟨85641934892048729537434433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57094623261365819691622955 85641934892048729537434433)
              ·
                refine ⟨64231451169036547153075825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85641934892048729537434433 64231451169036547153075825)
                ·
                  refine ⟨48173588376777410364806869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64231451169036547153075825 48173588376777410364806869)
                  ·
                    refine ⟨1129068477580720555425161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48173588376777410364806869 1129068477580720555425161)
                    ·
                      rfl

theorem cell23_6596559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 2, 7].length) (baseStart_6596559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6596559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6596559 prefixEnd_6596559 := by exact prefixLift 6596559
  have htrace : WordTrace (prefixWord ++ tailWord_6596559) baseStart_6596559 baseEnd_6596559 := by
    simpa [prefixWord, tailWord_6596559, baseEnd_6596559] using wordTrace_append hprefix tailTrace_6596559
  have hstable : (prefixWord ++ tailWord_6596559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6596559).length < 2 ^ (prefixWord ++ tailWord_6596559).sum := by decide
  have hdescent : baseEnd_6596559 < baseStart_6596559 := by decide
  rcases family_descends (prefixWord ++ tailWord_6596559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6596590 : List Nat := [4, 1, 2, 1, 3, 2, 1, 1, 4, 1, 3]
def baseStart_6596590 : Nat := 118140960795 + 6596590 * 2 ^ 59
def prefixEnd_6596590 : Nat := 4983230072969 + 3 ^ 40 * 6596590 * 2
def baseEnd_6596590 : Nat := 3387221350642451044987841

theorem tailTrace_6596590 : CollatzResearch.WordTrace tailWord_6596590 prefixEnd_6596590 3387221350642451044987841 := by
  unfold tailWord_6596590
  simp only [CollatzResearch.WordTrace]
  refine ⟨30074675396461064090409403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160398268781125675148850149 30074675396461064090409403)
  ·
    refine ⟨45112013094691596135614105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30074675396461064090409403 45112013094691596135614105)
    ·
      refine ⟨33834009821018697101710579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45112013094691596135614105 33834009821018697101710579)
      ·
        refine ⟨50751014731528045652565869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33834009821018697101710579 50751014731528045652565869)
        ·
          refine ⟨19031630524323017119712201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50751014731528045652565869 19031630524323017119712201)
          ·
            refine ⟨14273722893242262839784151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19031630524323017119712201 14273722893242262839784151)
            ·
              refine ⟨21410584339863394259676227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14273722893242262839784151 21410584339863394259676227)
              ·
                refine ⟨32115876509795091389514341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21410584339863394259676227 32115876509795091389514341)
                ·
                  refine ⟨6021726845586579635533939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32115876509795091389514341 6021726845586579635533939)
                  ·
                    refine ⟨9032590268379869453300909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6021726845586579635533939 9032590268379869453300909)
                    ·
                      refine ⟨3387221350642451044987841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9032590268379869453300909 3387221350642451044987841)
                      ·
                        rfl

theorem cell23_6596590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 1, 4, 1, 3].length) (baseStart_6596590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6596590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6596590 prefixEnd_6596590 := by exact prefixLift 6596590
  have htrace : WordTrace (prefixWord ++ tailWord_6596590) baseStart_6596590 baseEnd_6596590 := by
    simpa [prefixWord, tailWord_6596590, baseEnd_6596590] using wordTrace_append hprefix tailTrace_6596590
  have hstable : (prefixWord ++ tailWord_6596590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6596590).length < 2 ^ (prefixWord ++ tailWord_6596590).sum := by decide
  have hdescent : baseEnd_6596590 < baseStart_6596590 := by decide
  rcases family_descends (prefixWord ++ tailWord_6596590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6596616 : List Nat := [2, 1, 3, 2, 1, 2, 2, 2, 2, 1, 5]
def baseStart_6596616 : Nat := 118140960795 + 6596616 * 2 ^ 59
def prefixEnd_6596616 : Nat := 4983230072969 + 3 ^ 40 * 6596616 * 2
def baseEnd_6596616 : Nat := 3387234701139467943262721

theorem tailTrace_6596616 : CollatzResearch.WordTrace tailWord_6596616 prefixEnd_6596616 3387234701139467943262721 := by
  unfold tailWord_6596616
  simp only [CollatzResearch.WordTrace]
  refine ⟨120299175734797159581860851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160398900979729546109147801 120299175734797159581860851)
  ·
    refine ⟨180448763602195739372791277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120299175734797159581860851 180448763602195739372791277)
    ·
      refine ⟨67668286350823402264796729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180448763602195739372791277 67668286350823402264796729)
      ·
        refine ⟨50751214763117551698597547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67668286350823402264796729 50751214763117551698597547)
        ·
          refine ⟨76126822144676327547896321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50751214763117551698597547 76126822144676327547896321)
          ·
            refine ⟨57095116608507245660922241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76126822144676327547896321 57095116608507245660922241)
            ·
              refine ⟨42821337456380434245691681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57095116608507245660922241 42821337456380434245691681)
              ·
                refine ⟨32116003092285325684268761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42821337456380434245691681 32116003092285325684268761)
                ·
                  refine ⟨24087002319213994263201571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32116003092285325684268761 24087002319213994263201571)
                  ·
                    refine ⟨36130503478820991394802357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24087002319213994263201571 36130503478820991394802357)
                    ·
                      refine ⟨3387234701139467943262721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36130503478820991394802357 3387234701139467943262721)
                      ·
                        rfl

theorem cell23_6596616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_6596616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6596616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6596616 prefixEnd_6596616 := by exact prefixLift 6596616
  have htrace : WordTrace (prefixWord ++ tailWord_6596616) baseStart_6596616 baseEnd_6596616 := by
    simpa [prefixWord, tailWord_6596616, baseEnd_6596616] using wordTrace_append hprefix tailTrace_6596616
  have hstable : (prefixWord ++ tailWord_6596616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6596616).length < 2 ^ (prefixWord ++ tailWord_6596616).sum := by decide
  have hdescent : baseEnd_6596616 < baseStart_6596616 := by decide
  rcases family_descends (prefixWord ++ tailWord_6596616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6596666 : List Nat := [3, 1, 1, 1, 3, 1, 1, 1, 6, 5]
def baseStart_6596666 : Nat := 118140960795 + 6596666 * 2 ^ 59
def prefixEnd_6596666 : Nat := 4983230072969 + 3 ^ 40 * 6596666 * 2
def baseEnd_6596666 : Nat := 1129086791724064249212497

theorem tailTrace_6596666 : CollatzResearch.WordTrace tailWord_6596666 prefixEnd_6596666 1129086791724064249212497 := by
  unfold tailWord_6596666
  simp only [CollatzResearch.WordTrace]
  refine ⟨60150043779853294425760463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160400116746275451802027901 60150043779853294425760463)
  ·
    refine ⟨90225065669779941638640695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60150043779853294425760463 90225065669779941638640695)
    ·
      refine ⟨135337598504669912457961043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90225065669779941638640695 135337598504669912457961043)
      ·
        refine ⟨203006397757004868686941565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135337598504669912457961043 203006397757004868686941565)
        ·
          refine ⟨76127399158876825757603087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 203006397757004868686941565 76127399158876825757603087)
          ·
            refine ⟨114191098738315238636404631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76127399158876825757603087 114191098738315238636404631)
            ·
              refine ⟨171286648107472857954606947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114191098738315238636404631 171286648107472857954606947)
              ·
                refine ⟨256929972161209286931910421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171286648107472857954606947 256929972161209286931910421)
                ·
                  refine ⟨12043592445056685324933301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 256929972161209286931910421 12043592445056685324933301)
                  ·
                    refine ⟨1129086791724064249212497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12043592445056685324933301 1129086791724064249212497)
                    ·
                      rfl

theorem cell23_6596666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 6, 5].length) (baseStart_6596666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6596666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6596666 prefixEnd_6596666 := by exact prefixLift 6596666
  have htrace : WordTrace (prefixWord ++ tailWord_6596666) baseStart_6596666 baseEnd_6596666 := by
    simpa [prefixWord, tailWord_6596666, baseEnd_6596666] using wordTrace_append hprefix tailTrace_6596666
  have hstable : (prefixWord ++ tailWord_6596666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6596666).length < 2 ^ (prefixWord ++ tailWord_6596666).sum := by decide
  have hdescent : baseEnd_6596666 < baseStart_6596666 := by decide
  rcases family_descends (prefixWord ++ tailWord_6596666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6596713 : List Nat := [1, 2, 1, 1, 1, 5, 2, 3, 3, 4]
def baseStart_6596713 : Nat := 118140960795 + 6596713 * 2 ^ 59
def prefixEnd_6596713 : Nat := 4983230072969 + 3 ^ 40 * 6596713 * 2
def baseEnd_6596713 : Nat := 1129094836254318021249925

theorem tailTrace_6596713 : CollatzResearch.WordTrace tailWord_6596713 prefixEnd_6596713 1129094836254318021249925 := by
  unfold tailWord_6596713
  simp only [CollatzResearch.WordTrace]
  refine ⟨240601889350242904730002793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160401259566828603153335195 240601889350242904730002793)
  ·
    refine ⟨180451417012682178547502095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240601889350242904730002793 180451417012682178547502095)
    ·
      refine ⟨270677125519023267821253143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180451417012682178547502095 270677125519023267821253143)
      ·
        refine ⟨406015688278534901731879715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270677125519023267821253143 406015688278534901731879715)
        ·
          refine ⟨609023532417802352597819573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 406015688278534901731879715 609023532417802352597819573)
          ·
            refine ⟨57095956164168970556045585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 609023532417802352597819573 57095956164168970556045585)
            ·
              refine ⟨42821967123126727917034189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57095956164168970556045585 42821967123126727917034189)
              ·
                refine ⟨16058237671172522968887821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42821967123126727917034189 16058237671172522968887821)
                ·
                  refine ⟨6021839126689696113332933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16058237671172522968887821 6021839126689696113332933)
                  ·
                    refine ⟨1129094836254318021249925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6021839126689696113332933 1129094836254318021249925)
                    ·
                      rfl

theorem cell23_6596713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 3, 3, 4].length) (baseStart_6596713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6596713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6596713 prefixEnd_6596713 := by exact prefixLift 6596713
  have htrace : WordTrace (prefixWord ++ tailWord_6596713) baseStart_6596713 baseEnd_6596713 := by
    simpa [prefixWord, tailWord_6596713, baseEnd_6596713] using wordTrace_append hprefix tailTrace_6596713
  have hstable : (prefixWord ++ tailWord_6596713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6596713).length < 2 ^ (prefixWord ++ tailWord_6596713).sum := by decide
  have hdescent : baseEnd_6596713 < baseStart_6596713 := by decide
  rcases family_descends (prefixWord ++ tailWord_6596713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6596720 : List Nat := [2, 1, 1, 1, 5, 3, 1, 1, 2, 4, 2]
def baseStart_6596720 : Nat := 118140960795 + 6596720 * 2 ^ 59
def prefixEnd_6596720 : Nat := 4983230072969 + 3 ^ 40 * 6596720 * 2
def baseEnd_6596720 : Nat := 3387288103127535536362243

theorem tailTrace_6596720 : CollatzResearch.WordTrace tailWord_6596720 prefixEnd_6596720 3387288103127535536362243 := by
  unfold tailWord_6596720
  simp only [CollatzResearch.WordTrace]
  refine ⟨120301072330608772462753807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160401429774145029950338409 120301072330608772462753807)
  ·
    refine ⟨180451608495913158694130711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120301072330608772462753807 180451608495913158694130711)
    ·
      refine ⟨270677412743869738041196067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180451608495913158694130711 270677412743869738041196067)
      ·
        refine ⟨406016119115804607061794101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270677412743869738041196067 406016119115804607061794101)
        ·
          refine ⟨38064011167106681912043197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 406016119115804607061794101 38064011167106681912043197)
          ·
            refine ⟨14274004187665005717016199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38064011167106681912043197 14274004187665005717016199)
            ·
              refine ⟨21411006281497508575524299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14274004187665005717016199 21411006281497508575524299)
              ·
                refine ⟨32116509422246262863286449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21411006281497508575524299 32116509422246262863286449)
                ·
                  refine ⟨24087382066684697147464837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32116509422246262863286449 24087382066684697147464837)
                  ·
                    refine ⟨4516384137503380715149657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24087382066684697147464837 4516384137503380715149657)
                    ·
                      refine ⟨3387288103127535536362243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4516384137503380715149657 3387288103127535536362243)
                      ·
                        rfl

theorem cell23_6596720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 1, 2, 4, 2].length) (baseStart_6596720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6596720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6596720 prefixEnd_6596720 := by exact prefixLift 6596720
  have htrace : WordTrace (prefixWord ++ tailWord_6596720) baseStart_6596720 baseEnd_6596720 := by
    simpa [prefixWord, tailWord_6596720, baseEnd_6596720] using wordTrace_append hprefix tailTrace_6596720
  have hstable : (prefixWord ++ tailWord_6596720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6596720).length < 2 ^ (prefixWord ++ tailWord_6596720).sum := by decide
  have hdescent : baseEnd_6596720 < baseStart_6596720 := by decide
  rcases family_descends (prefixWord ++ tailWord_6596720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6596737 : List Nat := [1, 2, 4, 2, 3, 2, 1, 1, 2, 1, 4]
def baseStart_6596737 : Nat := 118140960795 + 6596737 * 2 ^ 59
def prefixEnd_6596737 : Nat := 4983230072969 + 3 ^ 40 * 6596737 * 2
def baseEnd_6596737 : Nat := 3387296832298661969849665

theorem tailTrace_6596737 : CollatzResearch.WordTrace tailWord_6596737 prefixEnd_6596737 3387296832298661969849665 := by
  unfold tailWord_6596737
  simp only [CollatzResearch.WordTrace]
  refine ⟨240602764702155956828876465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160401843134770637885917643 240602764702155956828876465)
  ·
    refine ⟨180452073526616967621657349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240602764702155956828876465 180452073526616967621657349)
    ·
      refine ⟨33834763786240681429060753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 180452073526616967621657349 33834763786240681429060753)
      ·
        refine ⟨25376072839680511071795565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33834763786240681429060753 25376072839680511071795565)
        ·
          refine ⟨9516027314880191651923337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25376072839680511071795565 9516027314880191651923337)
          ·
            refine ⟨7137020486160143738942503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9516027314880191651923337 7137020486160143738942503)
            ·
              refine ⟨10705530729240215608413755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7137020486160143738942503 10705530729240215608413755)
              ·
                refine ⟨16058296093860323412620633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10705530729240215608413755 16058296093860323412620633)
                ·
                  refine ⟨12043722070395242559465475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16058296093860323412620633 12043722070395242559465475)
                  ·
                    refine ⟨18065583105592863839198213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12043722070395242559465475 18065583105592863839198213)
                    ·
                      refine ⟨3387296832298661969849665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18065583105592863839198213 3387296832298661969849665)
                      ·
                        rfl

theorem cell23_6596737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_6596737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6596737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6596737 prefixEnd_6596737 := by exact prefixLift 6596737
  have htrace : WordTrace (prefixWord ++ tailWord_6596737) baseStart_6596737 baseEnd_6596737 := by
    simpa [prefixWord, tailWord_6596737, baseEnd_6596737] using wordTrace_append hprefix tailTrace_6596737
  have hstable : (prefixWord ++ tailWord_6596737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6596737).length < 2 ^ (prefixWord ++ tailWord_6596737).sum := by decide
  have hdescent : baseEnd_6596737 < baseStart_6596737 := by decide
  rcases family_descends (prefixWord ++ tailWord_6596737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6596810 : List Nat := [3, 1, 2, 1, 3, 1, 1, 5, 1, 1, 4]
def baseStart_6596810 : Nat := 118140960795 + 6596810 * 2 ^ 59
def prefixEnd_6596810 : Nat := 4983230072969 + 3 ^ 40 * 6596810 * 2
def baseEnd_6596810 : Nat := 3387334316386440184236829

theorem tailTrace_6596810 : CollatzResearch.WordTrace tailWord_6596810 prefixEnd_6596810 3387334316386440184236829 := by
  unfold tailWord_6596810
  simp only [CollatzResearch.WordTrace]
  refine ⟨60151356807722872574070971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160403618153927660197522589 60151356807722872574070971)
  ·
    refine ⟨90227035211584308861106457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60151356807722872574070971 90227035211584308861106457)
    ·
      refine ⟨67670276408688231645829843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90227035211584308861106457 67670276408688231645829843)
      ·
        refine ⟨101505414613032347468744765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67670276408688231645829843 101505414613032347468744765)
        ·
          refine ⟨38064530479887130300779287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101505414613032347468744765 38064530479887130300779287)
          ·
            refine ⟨57096795719830695451168931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38064530479887130300779287 57096795719830695451168931)
            ·
              refine ⟨85645193579746043176753397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57096795719830695451168931 85645193579746043176753397)
              ·
                refine ⟨8029236898101191547820631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85645193579746043176753397 8029236898101191547820631)
                ·
                  refine ⟨12043855347151787321730947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8029236898101191547820631 12043855347151787321730947)
                  ·
                    refine ⟨18065783020727680982596421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12043855347151787321730947 18065783020727680982596421)
                    ·
                      refine ⟨3387334316386440184236829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18065783020727680982596421 3387334316386440184236829)
                      ·
                        rfl

theorem cell23_6596810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 5, 1, 1, 4].length) (baseStart_6596810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6596810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6596810 prefixEnd_6596810 := by exact prefixLift 6596810
  have htrace : WordTrace (prefixWord ++ tailWord_6596810) baseStart_6596810 baseEnd_6596810 := by
    simpa [prefixWord, tailWord_6596810, baseEnd_6596810] using wordTrace_append hprefix tailTrace_6596810
  have hstable : (prefixWord ++ tailWord_6596810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6596810).length < 2 ^ (prefixWord ++ tailWord_6596810).sum := by decide
  have hdescent : baseEnd_6596810 < baseStart_6596810 := by decide
  rcases family_descends (prefixWord ++ tailWord_6596810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6596821 : List Nat := [1, 3, 2, 4, 3, 1, 1, 1, 3, 1, 3]
def baseStart_6596821 : Nat := 118140960795 + 6596821 * 2 ^ 59
def prefixEnd_6596821 : Nat := 4983230072969 + 3 ^ 40 * 6596821 * 2
def baseEnd_6596821 : Nat := 3387339964673639641199279

theorem tailTrace_6596821 : CollatzResearch.WordTrace tailWord_6596821 prefixEnd_6596821 3387339964673639641199279 := by
  unfold tailWord_6596821
  simp only [CollatzResearch.WordTrace]
  refine ⟨240605828433851639174934317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160403885622567759449956211 240605828433851639174934317)
  ·
    refine ⟨90227185662694364690600369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 240605828433851639174934317 90227185662694364690600369)
    ·
      refine ⟨67670389247020773517950277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90227185662694364690600369 67670389247020773517950277)
      ·
        refine ⟨12688197983816395034615677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67670389247020773517950277 12688197983816395034615677)
        ·
          refine ⟨4758074243931148137980879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12688197983816395034615677 4758074243931148137980879)
          ·
            refine ⟨7137111365896722206971319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4758074243931148137980879 7137111365896722206971319)
            ·
              refine ⟨10705667048845083310456979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7137111365896722206971319 10705667048845083310456979)
              ·
                refine ⟨16058500573267624965685469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10705667048845083310456979 16058500573267624965685469)
                ·
                  refine ⟨6021937714975359362132051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16058500573267624965685469 6021937714975359362132051)
                  ·
                    refine ⟨9032906572463039043198077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6021937714975359362132051 9032906572463039043198077)
                    ·
                      refine ⟨3387339964673639641199279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9032906572463039043198077 3387339964673639641199279)
                      ·
                        rfl

theorem cell23_6596821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_6596821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6596821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6596821 prefixEnd_6596821 := by exact prefixLift 6596821
  have htrace : WordTrace (prefixWord ++ tailWord_6596821) baseStart_6596821 baseEnd_6596821 := by
    simpa [prefixWord, tailWord_6596821, baseEnd_6596821] using wordTrace_append hprefix tailTrace_6596821
  have hstable : (prefixWord ++ tailWord_6596821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6596821).length < 2 ^ (prefixWord ++ tailWord_6596821).sum := by decide
  have hdescent : baseEnd_6596821 < baseStart_6596821 := by decide
  rcases family_descends (prefixWord ++ tailWord_6596821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6596833 : List Nat := [1, 2, 3, 1, 3, 1, 4, 8]
def baseStart_6596833 : Nat := 118140960795 + 6596833 * 2 ^ 59
def prefixEnd_6596833 : Nat := 4983230072969 + 3 ^ 40 * 6596833 * 2
def baseEnd_6596833 : Nat := 125457263942277540527749

theorem tailTrace_6596833 : CollatzResearch.WordTrace tailWord_6596833 prefixEnd_6596833 125457263942277540527749 := by
  unfold tailWord_6596833
  simp only [CollatzResearch.WordTrace]
  refine ⟨240606266109808165224371153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160404177406538776816247435 240606266109808165224371153)
  ·
    refine ⟨180454699582356123918278365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240606266109808165224371153 180454699582356123918278365)
    ·
      refine ⟨67670512343383546469354387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180454699582356123918278365 67670512343383546469354387)
      ·
        refine ⟨101505768515075319704031581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67670512343383546469354387 101505768515075319704031581)
        ·
          refine ⟨38064663193153244889011843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101505768515075319704031581 38064663193153244889011843)
          ·
            refine ⟨57096994789729867333517765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38064663193153244889011843 57096994789729867333517765)
            ·
              refine ⟨10705686523074350125034581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57096994789729867333517765 10705686523074350125034581)
              ·
                refine ⟨125457263942277540527749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10705686523074350125034581 125457263942277540527749)
                ·
                  rfl

theorem cell23_6596833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 8].length) (baseStart_6596833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6596833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6596833 prefixEnd_6596833 := by exact prefixLift 6596833
  have htrace : WordTrace (prefixWord ++ tailWord_6596833) baseStart_6596833 baseEnd_6596833 := by
    simpa [prefixWord, tailWord_6596833, baseEnd_6596833] using wordTrace_append hprefix tailTrace_6596833
  have hstable : (prefixWord ++ tailWord_6596833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6596833).length < 2 ^ (prefixWord ++ tailWord_6596833).sum := by decide
  have hdescent : baseEnd_6596833 < baseStart_6596833 := by decide
  rcases family_descends (prefixWord ++ tailWord_6596833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6596837 : List Nat := [1, 3, 1, 4, 2, 2, 1, 3, 2, 4]
def baseStart_6596837 : Nat := 118140960795 + 6596837 * 2 ^ 59
def prefixEnd_6596837 : Nat := 4983230072969 + 3 ^ 40 * 6596837 * 2
def baseEnd_6596837 : Nat := 1129116060121370526199735

theorem tailTrace_6596837 : CollatzResearch.WordTrace tailWord_6596837 prefixEnd_6596837 1129116060121370526199735 := by
  unfold tailWord_6596837
  simp only [CollatzResearch.WordTrace]
  refine ⟨240606412001793673907516765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160404274667862449271677843 240606412001793673907516765)
  ·
    refine ⟨90227404500672627715318787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 240606412001793673907516765 90227404500672627715318787)
    ·
      refine ⟨135341106751008941572978181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90227404500672627715318787 135341106751008941572978181)
      ·
        refine ⟨25376457515814176544933409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135341106751008941572978181 25376457515814176544933409)
        ·
          refine ⟨19032343136860632408700057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25376457515814176544933409 19032343136860632408700057)
          ·
            refine ⟨14274257352645474306525043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19032343136860632408700057 14274257352645474306525043)
            ·
              refine ⟨21411386028968211459787565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14274257352645474306525043 21411386028968211459787565)
              ·
                refine ⟨8029269760863079297420337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21411386028968211459787565 8029269760863079297420337)
                ·
                  refine ⟨6021952320647309473065253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8029269760863079297420337 6021952320647309473065253)
                  ·
                    refine ⟨1129116060121370526199735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6021952320647309473065253 1129116060121370526199735)
                    ·
                      rfl

theorem cell23_6596837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 3, 2, 4].length) (baseStart_6596837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6596837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6596837 prefixEnd_6596837 := by exact prefixLift 6596837
  have htrace : WordTrace (prefixWord ++ tailWord_6596837) baseStart_6596837 baseEnd_6596837 := by
    simpa [prefixWord, tailWord_6596837, baseEnd_6596837] using wordTrace_append hprefix tailTrace_6596837
  have hstable : (prefixWord ++ tailWord_6596837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6596837).length < 2 ^ (prefixWord ++ tailWord_6596837).sum := by decide
  have hdescent : baseEnd_6596837 < baseStart_6596837 := by decide
  rcases family_descends (prefixWord ++ tailWord_6596837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6596847 : List Nat := [1, 1, 2, 1, 6, 1, 3, 2, 1, 2, 3]
def baseStart_6596847 : Nat := 118140960795 + 6596847 * 2 ^ 59
def prefixEnd_6596847 : Nat := 4983230072969 + 3 ^ 40 * 6596847 * 2
def baseEnd_6596847 : Nat := 3387353315170656539474159

theorem tailTrace_6596847 : CollatzResearch.WordTrace tailWord_6596847 prefixEnd_6596847 3387353315170656539474159 := by
  unfold tailWord_6596847
  simp only [CollatzResearch.WordTrace]
  refine ⟨240606776731757445615380795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160404517821171630410253863 240606776731757445615380795)
  ·
    refine ⟨360910165097636168423071193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240606776731757445615380795 360910165097636168423071193)
    ·
      refine ⟨270682623823227126317303395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 360910165097636168423071193 270682623823227126317303395)
      ·
        refine ⟨406023935734840689475955093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270682623823227126317303395 406023935734840689475955093)
        ·
          refine ⟨19032371987570657319185395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 406023935734840689475955093 19032371987570657319185395)
          ·
            refine ⟨28548557981355985978778093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19032371987570657319185395 28548557981355985978778093)
            ·
              refine ⟨10705709243008494742041785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28548557981355985978778093 10705709243008494742041785)
              ·
                refine ⟨8029281932256371056531339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10705709243008494742041785 8029281932256371056531339)
                ·
                  refine ⟨12043922898384556584797009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8029281932256371056531339 12043922898384556584797009)
                  ·
                    refine ⟨9032942173788417438597757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12043922898384556584797009 9032942173788417438597757)
                    ·
                      refine ⟨3387353315170656539474159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9032942173788417438597757 3387353315170656539474159)
                      ·
                        rfl

theorem cell23_6596847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 2, 1, 2, 3].length) (baseStart_6596847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6596847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6596847 prefixEnd_6596847 := by exact prefixLift 6596847
  have htrace : WordTrace (prefixWord ++ tailWord_6596847) baseStart_6596847 baseEnd_6596847 := by
    simpa [prefixWord, tailWord_6596847, baseEnd_6596847] using wordTrace_append hprefix tailTrace_6596847
  have hstable : (prefixWord ++ tailWord_6596847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6596847).length < 2 ^ (prefixWord ++ tailWord_6596847).sum := by decide
  have hdescent : baseEnd_6596847 < baseStart_6596847 := by decide
  rcases family_descends (prefixWord ++ tailWord_6596847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6596860 : List Nat := [2, 2, 2, 1, 4, 1, 1, 1, 3, 3, 3]
def baseStart_6596860 : Nat := 118140960795 + 6596860 * 2 ^ 59
def prefixEnd_6596860 : Nat := 4983230072969 + 3 ^ 40 * 6596860 * 2
def baseEnd_6596860 : Nat := 3387359990419164988611599

theorem tailTrace_6596860 : CollatzResearch.WordTrace tailWord_6596860 prefixEnd_6596860 3387359990419164988611599 := by
  unfold tailWord_6596860
  simp only [CollatzResearch.WordTrace]
  refine ⟨120303625440355174417802017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160404833920473565890402689 120303625440355174417802017)
  ·
    refine ⟨90227719080266380813351513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120303625440355174417802017 90227719080266380813351513)
    ·
      refine ⟨67670789310199785610013635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90227719080266380813351513 67670789310199785610013635)
      ·
        refine ⟨101506183965299678415020453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67670789310199785610013635 101506183965299678415020453)
        ·
          refine ⟨19032409493493689702816335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101506183965299678415020453 19032409493493689702816335)
          ·
            refine ⟨28548614240240534554224503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19032409493493689702816335 28548614240240534554224503)
            ·
              refine ⟨42822921360360801831336755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28548614240240534554224503 42822921360360801831336755)
              ·
                refine ⟨64234382040541202747005133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42822921360360801831336755 64234382040541202747005133)
                ·
                  refine ⟨24087893265202951030126925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64234382040541202747005133 24087893265202951030126925)
                  ·
                    refine ⟨9032959974451106636297597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24087893265202951030126925 9032959974451106636297597)
                    ·
                      refine ⟨3387359990419164988611599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9032959974451106636297597 3387359990419164988611599)
                      ·
                        rfl

theorem cell23_6596860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 3, 3, 3].length) (baseStart_6596860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6596860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6596860 prefixEnd_6596860 := by exact prefixLift 6596860
  have htrace : WordTrace (prefixWord ++ tailWord_6596860) baseStart_6596860 baseEnd_6596860 := by
    simpa [prefixWord, tailWord_6596860, baseEnd_6596860] using wordTrace_append hprefix tailTrace_6596860
  have hstable : (prefixWord ++ tailWord_6596860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6596860).length < 2 ^ (prefixWord ++ tailWord_6596860).sum := by decide
  have hdescent : baseEnd_6596860 < baseStart_6596860 := by decide
  rcases family_descends (prefixWord ++ tailWord_6596860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6596887 : List Nat := [1, 1, 3, 4, 1, 2, 1, 2, 3, 3, 2]
def baseStart_6596887 : Nat := 118140960795 + 6596887 * 2 ^ 59
def prefixEnd_6596887 : Nat := 4983230072969 + 3 ^ 40 * 6596887 * 2
def baseEnd_6596887 : Nat := 3387373854396836382973975

theorem tailTrace_6596887 : CollatzResearch.WordTrace tailWord_6596887 prefixEnd_6596887 3387373854396836382973975 := by
  unfold tailWord_6596887
  simp only [CollatzResearch.WordTrace]
  refine ⟨240608235651612532446836915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160405490434408354964557943 240608235651612532446836915)
  ·
    refine ⟨360912353477418798670255373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240608235651612532446836915 360912353477418798670255373)
    ·
      refine ⟨135342132554032049501345765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 360912353477418798670255373 135342132554032049501345765)
      ·
        refine ⟨25376649853881009281502331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135342132554032049501345765 25376649853881009281502331)
        ·
          refine ⟨38064974780821513922253497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25376649853881009281502331 38064974780821513922253497)
          ·
            refine ⟨28548731085616135441690123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38064974780821513922253497 28548731085616135441690123)
            ·
              refine ⟨42823096628424203162535185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28548731085616135441690123 42823096628424203162535185)
              ·
                refine ⟨32117322471318152371901389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42823096628424203162535185 32117322471318152371901389)
                ·
                  refine ⟨12043995926744307139463021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32117322471318152371901389 12043995926744307139463021)
                  ·
                    refine ⟨4516498472529115177298633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12043995926744307139463021 4516498472529115177298633)
                    ·
                      refine ⟨3387373854396836382973975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4516498472529115177298633 3387373854396836382973975)
                      ·
                        rfl

theorem cell23_6596887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 2, 3, 3, 2].length) (baseStart_6596887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6596887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6596887 prefixEnd_6596887 := by exact prefixLift 6596887
  have htrace : WordTrace (prefixWord ++ tailWord_6596887) baseStart_6596887 baseEnd_6596887 := by
    simpa [prefixWord, tailWord_6596887, baseEnd_6596887] using wordTrace_append hprefix tailTrace_6596887
  have hstable : (prefixWord ++ tailWord_6596887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6596887).length < 2 ^ (prefixWord ++ tailWord_6596887).sum := by decide
  have hdescent : baseEnd_6596887 < baseStart_6596887 := by decide
  rcases family_descends (prefixWord ++ tailWord_6596887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6596894 : List Nat := [4, 3, 2, 1, 1, 1, 1, 3, 1, 3, 3]
def baseStart_6596894 : Nat := 118140960795 + 6596894 * 2 ^ 59
def prefixEnd_6596894 : Nat := 4983230072969 + 3 ^ 40 * 6596894 * 2
def baseEnd_6596894 : Nat := 3387377448761417855586443

theorem tailTrace_6596894 : CollatzResearch.WordTrace tailWord_6596894 prefixEnd_6596894 3387377448761417855586443 := by
  unfold tailWord_6596894
  simp only [CollatzResearch.WordTrace]
  refine ⟨30076061370323396580292717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160405660641724781761561157 30076061370323396580292717)
  ·
    refine ⟨11278523013871273717609769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30076061370323396580292717 11278523013871273717609769)
    ·
      refine ⟨8458892260403455288207327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11278523013871273717609769 8458892260403455288207327)
      ·
        refine ⟨12688338390605182932310991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8458892260403455288207327 12688338390605182932310991)
        ·
          refine ⟨19032507585907774398466487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12688338390605182932310991 19032507585907774398466487)
          ·
            refine ⟨28548761378861661597699731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19032507585907774398466487 28548761378861661597699731)
            ·
              refine ⟨42823142068292492396549597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28548761378861661597699731 42823142068292492396549597)
              ·
                refine ⟨16058678275609684648706099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42823142068292492396549597 16058678275609684648706099)
                ·
                  refine ⟨24088017413414526973059149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16058678275609684648706099 24088017413414526973059149)
                  ·
                    refine ⟨9033006530030447614897181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24088017413414526973059149 9033006530030447614897181)
                    ·
                      refine ⟨3387377448761417855586443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9033006530030447614897181 3387377448761417855586443)
                      ·
                        rfl

theorem cell23_6596894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_6596894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6596894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6596894 prefixEnd_6596894 := by exact prefixLift 6596894
  have htrace : WordTrace (prefixWord ++ tailWord_6596894) baseStart_6596894 baseEnd_6596894 := by
    simpa [prefixWord, tailWord_6596894, baseEnd_6596894] using wordTrace_append hprefix tailTrace_6596894
  have hstable : (prefixWord ++ tailWord_6596894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6596894).length < 2 ^ (prefixWord ++ tailWord_6596894).sum := by decide
  have hdescent : baseEnd_6596894 < baseStart_6596894 := by decide
  rcases family_descends (prefixWord ++ tailWord_6596894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6596917 : List Nat := [1, 3, 3, 1, 2, 1, 1, 4, 1, 4, 2]
def baseStart_6596917 : Nat := 118140960795 + 6596917 * 2 ^ 59
def prefixEnd_6596917 : Nat := 4983230072969 + 3 ^ 40 * 6596917 * 2
def baseEnd_6596917 : Nat := 3387389258816471265598837

theorem tailTrace_6596917 : CollatzResearch.WordTrace tailWord_6596917 prefixEnd_6596917 3387389258816471265598837 := by
  unfold tailWord_6596917
  simp only [CollatzResearch.WordTrace]
  refine ⟨240609329841503847570429005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160406219894335898380286003 240609329841503847570429005)
  ·
    refine ⟨90228498690563942838910877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 240609329841503847570429005 90228498690563942838910877)
    ·
      refine ⟨33835687008961478564591579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90228498690563942838910877 33835687008961478564591579)
      ·
        refine ⟨50753530513442217846887369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33835687008961478564591579 50753530513442217846887369)
        ·
          refine ⟨38065147885081663385165527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50753530513442217846887369 38065147885081663385165527)
          ·
            refine ⟨57097721827622495077748291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38065147885081663385165527 57097721827622495077748291)
            ·
              refine ⟨85646582741433742616622437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57097721827622495077748291 85646582741433742616622437)
              ·
                refine ⟨16058734264018826740616707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85646582741433742616622437 16058734264018826740616707)
                ·
                  refine ⟨24088101396028240110925061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16058734264018826740616707 24088101396028240110925061)
                  ·
                    refine ⟨4516519011755295020798449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24088101396028240110925061 4516519011755295020798449)
                    ·
                      refine ⟨3387389258816471265598837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4516519011755295020798449 3387389258816471265598837)
                      ·
                        rfl

theorem cell23_6596917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 4, 1, 4, 2].length) (baseStart_6596917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6596917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6596917 prefixEnd_6596917 := by exact prefixLift 6596917
  have htrace : WordTrace (prefixWord ++ tailWord_6596917) baseStart_6596917 baseEnd_6596917 := by
    simpa [prefixWord, tailWord_6596917, baseEnd_6596917] using wordTrace_append hprefix tailTrace_6596917
  have hstable : (prefixWord ++ tailWord_6596917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6596917).length < 2 ^ (prefixWord ++ tailWord_6596917).sum := by decide
  have hdescent : baseEnd_6596917 < baseStart_6596917 := by decide
  rcases family_descends (prefixWord ++ tailWord_6596917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6596921 : List Nat := [1, 2, 1, 6, 1, 1, 4, 1, 1, 3, 2]
def baseStart_6596921 : Nat := 118140960795 + 6596921 * 2 ^ 59
def prefixEnd_6596921 : Nat := 4983230072969 + 3 ^ 40 * 6596921 * 2
def baseEnd_6596921 : Nat := 3387391312739089249948819

theorem tailTrace_6596921 : CollatzResearch.WordTrace tailWord_6596921 prefixEnd_6596921 3387391312739089249948819 := by
  unfold tailWord_6596921
  simp only [CollatzResearch.WordTrace]
  refine ⟨240609475733489356253574617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160406317155659570835716411 240609475733489356253574617)
  ·
    refine ⟨180457106800117017190180963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240609475733489356253574617 180457106800117017190180963)
    ·
      refine ⟨270685660200175525785271445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180457106800117017190180963 270685660200175525785271445)
      ·
        refine ⟨12688390321883227771184599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 270685660200175525785271445 12688390321883227771184599)
        ·
          refine ⟨19032585482824841656776899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12688390321883227771184599 19032585482824841656776899)
          ·
            refine ⟨28548878224237262485165349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19032585482824841656776899 28548878224237262485165349)
            ·
              refine ⟨5352914667044486715968503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28548878224237262485165349 5352914667044486715968503)
              ·
                refine ⟨8029372000566730073952755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5352914667044486715968503 8029372000566730073952755)
                ·
                  refine ⟨12044058000850095110929133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8029372000566730073952755 12044058000850095110929133)
                  ·
                    refine ⟨4516521750318785666598425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12044058000850095110929133 4516521750318785666598425)
                    ·
                      refine ⟨3387391312739089249948819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4516521750318785666598425 3387391312739089249948819)
                      ·
                        rfl

theorem cell23_6596921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_6596921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6596921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6596921 prefixEnd_6596921 := by exact prefixLift 6596921
  have htrace : WordTrace (prefixWord ++ tailWord_6596921) baseStart_6596921 baseEnd_6596921 := by
    simpa [prefixWord, tailWord_6596921, baseEnd_6596921] using wordTrace_append hprefix tailTrace_6596921
  have hstable : (prefixWord ++ tailWord_6596921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6596921).length < 2 ^ (prefixWord ++ tailWord_6596921).sum := by decide
  have hdescent : baseEnd_6596921 < baseStart_6596921 := by decide
  rcases family_descends (prefixWord ++ tailWord_6596921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6596940 : List Nat := [2, 2, 1, 3, 2, 1, 4, 1, 7]
def baseStart_6596940 : Nat := 118140960795 + 6596940 * 2 ^ 59
def prefixEnd_6596940 : Nat := 4983230072969 + 3 ^ 40 * 6596940 * 2
def baseEnd_6596940 : Nat := 376377896541280519512359

theorem tailTrace_6596940 : CollatzResearch.WordTrace tailWord_6596940 prefixEnd_6596940 376377896541280519512359 := by
  unfold tailWord_6596940
  simp only [CollatzResearch.WordTrace]
  refine ⟨120305084360210261249258137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160406779146947014999010849 120305084360210261249258137)
  ·
    refine ⟨90228813270157695936943603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120305084360210261249258137 90228813270157695936943603)
    ·
      refine ⟨135343219905236543905415405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90228813270157695936943603 135343219905236543905415405)
      ·
        refine ⟨50753707464463703964530777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135343219905236543905415405 50753707464463703964530777)
        ·
          refine ⟨38065280598347777973398083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50753707464463703964530777 38065280598347777973398083)
          ·
            refine ⟨57097920897521666960097125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38065280598347777973398083 57097920897521666960097125)
            ·
              refine ⟨10705860168285312555018211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57097920897521666960097125 10705860168285312555018211)
              ·
                refine ⟨16058790252427968832527317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10705860168285312555018211 16058790252427968832527317)
                ·
                  refine ⟨376377896541280519512359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16058790252427968832527317 376377896541280519512359)
                  ·
                    rfl

theorem cell23_6596940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 1, 7].length) (baseStart_6596940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6596940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6596940 prefixEnd_6596940 := by exact prefixLift 6596940
  have htrace : WordTrace (prefixWord ++ tailWord_6596940) baseStart_6596940 baseEnd_6596940 := by
    simpa [prefixWord, tailWord_6596940, baseEnd_6596940] using wordTrace_append hprefix tailTrace_6596940
  have hstable : (prefixWord ++ tailWord_6596940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6596940).length < 2 ^ (prefixWord ++ tailWord_6596940).sum := by decide
  have hdescent : baseEnd_6596940 < baseStart_6596940 := by decide
  rcases family_descends (prefixWord ++ tailWord_6596940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6596951 : List Nat := [1, 1, 3, 2, 3, 1, 5, 1, 2, 2, 2]
def baseStart_6596951 : Nat := 118140960795 + 6596951 * 2 ^ 59
def prefixEnd_6596951 : Nat := 4983230072969 + 3 ^ 40 * 6596951 * 2
def baseEnd_6596951 : Nat := 3387406717158724132573681

theorem tailTrace_6596951 : CollatzResearch.WordTrace tailWord_6596951 prefixEnd_6596951 3387406717158724132573681 := by
  unfold tailWord_6596951
  simp only [CollatzResearch.WordTrace]
  refine ⟨240610569923380671377166707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160407046615587114251444471 240610569923380671377166707)
  ·
    refine ⟨360915854885071007065750061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240610569923380671377166707 360915854885071007065750061)
    ·
      refine ⟨135343445581901627649656273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 360915854885071007065750061 135343445581901627649656273)
      ·
        refine ⟨101507584186426220737242205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135343445581901627649656273 101507584186426220737242205)
        ·
          refine ⟨38065344069909832776465827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101507584186426220737242205 38065344069909832776465827)
          ·
            refine ⟨57098016104864749164698741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38065344069909832776465827 57098016104864749164698741)
            ·
              refine ⟨5352939009831070234190507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57098016104864749164698741 5352939009831070234190507)
              ·
                refine ⟨8029408514746605351285761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5352939009831070234190507 8029408514746605351285761)
                ·
                  refine ⟨6022056386059954013464321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8029408514746605351285761 6022056386059954013464321)
                  ·
                    refine ⟨4516542289544965510098241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6022056386059954013464321 4516542289544965510098241)
                    ·
                      refine ⟨3387406717158724132573681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4516542289544965510098241 3387406717158724132573681)
                      ·
                        rfl

theorem cell23_6596951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 5, 1, 2, 2, 2].length) (baseStart_6596951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6596951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6596951 prefixEnd_6596951 := by exact prefixLift 6596951
  have htrace : WordTrace (prefixWord ++ tailWord_6596951) baseStart_6596951 baseEnd_6596951 := by
    simpa [prefixWord, tailWord_6596951, baseEnd_6596951] using wordTrace_append hprefix tailTrace_6596951
  have hstable : (prefixWord ++ tailWord_6596951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6596951).length < 2 ^ (prefixWord ++ tailWord_6596951).sum := by decide
  have hdescent : baseEnd_6596951 < baseStart_6596951 := by decide
  rcases family_descends (prefixWord ++ tailWord_6596951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6597002 : List Nat := [3, 1, 2, 5, 2, 1, 2, 1, 2, 2, 2]
def baseStart_6597002 : Nat := 118140960795 + 6597002 * 2 ^ 59
def prefixEnd_6597002 : Nat := 4983230072969 + 3 ^ 40 * 6597002 * 2
def baseEnd_6597002 : Nat := 3387432904672103433035947

theorem tailTrace_6597002 : CollatzResearch.WordTrace tailWord_6597002 prefixEnd_6597002 3387432904672103433035947 := by
  unfold tailWord_6597002
  simp only [CollatzResearch.WordTrace]
  refine ⟨60153107511548976771818315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160408286697463938058182173 60153107511548976771818315)
  ·
    refine ⟨90229661267323465157727473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60153107511548976771818315 90229661267323465157727473)
    ·
      refine ⟨67672245950492598868295605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90229661267323465157727473 67672245950492598868295605)
      ·
        refine ⟨6344273057858681143902713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67672245950492598868295605 6344273057858681143902713)
        ·
          refine ⟨4758204793394010857927035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6344273057858681143902713 4758204793394010857927035)
          ·
            refine ⟨7137307190091016286890553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4758204793394010857927035 7137307190091016286890553)
            ·
              refine ⟨5352980392568262215167915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7137307190091016286890553 5352980392568262215167915)
              ·
                refine ⟨8029470588852393322751873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5352980392568262215167915 8029470588852393322751873)
                ·
                  refine ⟨6022102941639294992063905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8029470588852393322751873 6022102941639294992063905)
                  ·
                    refine ⟨4516577206229471244047929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6022102941639294992063905 4516577206229471244047929)
                    ·
                      refine ⟨3387432904672103433035947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4516577206229471244047929 3387432904672103433035947)
                      ·
                        rfl

theorem cell23_6597002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_6597002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6597002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6597002 prefixEnd_6597002 := by exact prefixLift 6597002
  have htrace : WordTrace (prefixWord ++ tailWord_6597002) baseStart_6597002 baseEnd_6597002 := by
    simpa [prefixWord, tailWord_6597002, baseEnd_6597002] using wordTrace_append hprefix tailTrace_6597002
  have hstable : (prefixWord ++ tailWord_6597002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6597002).length < 2 ^ (prefixWord ++ tailWord_6597002).sum := by decide
  have hdescent : baseEnd_6597002 < baseStart_6597002 := by decide
  rcases family_descends (prefixWord ++ tailWord_6597002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6597027 : List Nat := [1, 1, 1, 4, 1, 4, 1, 3, 2, 2, 3]
def baseStart_6597027 : Nat := 118140960795 + 6597027 * 2 ^ 59
def prefixEnd_6597027 : Nat := 4983230072969 + 3 ^ 40 * 6597027 * 2
def baseEnd_6597027 : Nat := 3387445741688465835223331

theorem tailTrace_6597027 : CollatzResearch.WordTrace tailWord_6597027 prefixEnd_6597027 3387445741688465835223331 := by
  unfold tailWord_6597027
  simp only [CollatzResearch.WordTrace]
  refine ⟨240613341871105336356933335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160408894580736890904622223 240613341871105336356933335)
  ·
    refine ⟨360920012806658004535400003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240613341871105336356933335 360920012806658004535400003)
    ·
      refine ⟨541380019209987006803100005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360920012806658004535400003 541380019209987006803100005)
      ·
        refine ⟨101508753601872563775581251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 541380019209987006803100005 101508753601872563775581251)
        ·
          refine ⟨152263130402808845663371877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101508753601872563775581251 152263130402808845663371877)
          ·
            refine ⟨28549336950526658561882227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 152263130402808845663371877 28549336950526658561882227)
            ·
              refine ⟨42824005425789987842823341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28549336950526658561882227 42824005425789987842823341)
              ·
                refine ⟨16059002034671245441058753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42824005425789987842823341 16059002034671245441058753)
                ·
                  refine ⟨12044251526003434080794065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16059002034671245441058753 12044251526003434080794065)
                  ·
                    refine ⟨9033188644502575560595549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12044251526003434080794065 9033188644502575560595549)
                    ·
                      refine ⟨3387445741688465835223331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9033188644502575560595549 3387445741688465835223331)
                      ·
                        rfl

theorem cell23_6597027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 3, 2, 2, 3].length) (baseStart_6597027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6597027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6597027 prefixEnd_6597027 := by exact prefixLift 6597027
  have htrace : WordTrace (prefixWord ++ tailWord_6597027) baseStart_6597027 baseEnd_6597027 := by
    simpa [prefixWord, tailWord_6597027, baseEnd_6597027] using wordTrace_append hprefix tailTrace_6597027
  have hstable : (prefixWord ++ tailWord_6597027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6597027).length < 2 ^ (prefixWord ++ tailWord_6597027).sum := by decide
  have hdescent : baseEnd_6597027 < baseStart_6597027 := by decide
  rcases family_descends (prefixWord ++ tailWord_6597027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6597040 : List Nat := [2, 1, 1, 1, 2, 1, 1, 2, 4, 5, 3]
def baseStart_6597040 : Nat := 118140960795 + 6597040 * 2 ^ 59
def prefixEnd_6597040 : Nat := 4983230072969 + 3 ^ 40 * 6597040 * 2
def baseEnd_6597040 : Nat := 3387452416936974284360771

theorem tailTrace_6597040 : CollatzResearch.WordTrace tailWord_6597040 prefixEnd_6597040 3387452416936974284360771 := by
  unfold tailWord_6597040
  simp only [CollatzResearch.WordTrace]
  refine ⟨120306908010029119788578287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160409210680038826384771049 120306908010029119788578287)
  ·
    refine ⟨180460362015043679682867431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120306908010029119788578287 180460362015043679682867431)
    ·
      refine ⟨270690543022565519524301147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180460362015043679682867431 270690543022565519524301147)
      ·
        refine ⟨406035814533848279286451721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270690543022565519524301147 406035814533848279286451721)
        ·
          refine ⟨304526860900386209464838791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 406035814533848279286451721 304526860900386209464838791)
          ·
            refine ⟨456790291350579314197258187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 304526860900386209464838791 456790291350579314197258187)
            ·
              refine ⟨685185437025868971295887281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 456790291350579314197258187 685185437025868971295887281)
              ·
                refine ⟨513889077769401728471915461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 685185437025868971295887281 513889077769401728471915461)
                ·
                  refine ⟨96354202081762824088484149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 513889077769401728471915461 96354202081762824088484149)
                  ·
                    refine ⟨9033206445165264758295389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 96354202081762824088484149 9033206445165264758295389)
                    ·
                      refine ⟨3387452416936974284360771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9033206445165264758295389 3387452416936974284360771)
                      ·
                        rfl

theorem cell23_6597040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 4, 5, 3].length) (baseStart_6597040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6597040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6597040 prefixEnd_6597040 := by exact prefixLift 6597040
  have htrace : WordTrace (prefixWord ++ tailWord_6597040) baseStart_6597040 baseEnd_6597040 := by
    simpa [prefixWord, tailWord_6597040, baseEnd_6597040] using wordTrace_append hprefix tailTrace_6597040
  have hstable : (prefixWord ++ tailWord_6597040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6597040).length < 2 ^ (prefixWord ++ tailWord_6597040).sum := by decide
  have hdescent : baseEnd_6597040 < baseStart_6597040 := by decide
  rcases family_descends (prefixWord ++ tailWord_6597040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6597047 : List Nat := [1, 1, 3, 1, 3, 4, 2, 2, 6]
def baseStart_6597047 : Nat := 118140960795 + 6597047 * 2 ^ 59
def prefixEnd_6597047 : Nat := 4983230072969 + 3 ^ 40 * 6597047 * 2
def baseEnd_6597047 : Nat := 376384001255728417441471

theorem tailTrace_6597047 : CollatzResearch.WordTrace tailWord_6597047 prefixEnd_6597047 376384001255728417441471 := by
  unfold tailWord_6597047
  simp only [CollatzResearch.WordTrace]
  refine ⟨240614071331032879772661395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160409380887355253181774263 240614071331032879772661395)
  ·
    refine ⟨360921106996549319658992093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240614071331032879772661395 360921106996549319658992093)
    ·
      refine ⟨135345415123705994872122035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 360921106996549319658992093 135345415123705994872122035)
      ·
        refine ⟨203018122685558992308183053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135345415123705994872122035 203018122685558992308183053)
        ·
          refine ⟨76131796007084622115568645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 203018122685558992308183053 76131796007084622115568645)
          ·
            refine ⟨14274711751328366646669121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76131796007084622115568645 14274711751328366646669121)
            ·
              refine ⟨10706033813496274985001841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14274711751328366646669121 10706033813496274985001841)
              ·
                refine ⟨8029525360122206238751381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10706033813496274985001841 8029525360122206238751381)
                ·
                  refine ⟨376384001255728417441471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8029525360122206238751381 376384001255728417441471)
                  ·
                    rfl

theorem cell23_6597047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 2, 6].length) (baseStart_6597047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6597047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6597047 prefixEnd_6597047 := by exact prefixLift 6597047
  have htrace : WordTrace (prefixWord ++ tailWord_6597047) baseStart_6597047 baseEnd_6597047 := by
    simpa [prefixWord, tailWord_6597047, baseEnd_6597047] using wordTrace_append hprefix tailTrace_6597047
  have hstable : (prefixWord ++ tailWord_6597047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6597047).length < 2 ^ (prefixWord ++ tailWord_6597047).sum := by decide
  have hdescent : baseEnd_6597047 < baseStart_6597047 := by decide
  rcases family_descends (prefixWord ++ tailWord_6597047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6597067 : List Nat := [1, 1, 1, 1, 3, 3, 1, 4, 1, 5, 2]
def baseStart_6597067 : Nat := 118140960795 + 6597067 * 2 ^ 59
def prefixEnd_6597067 : Nat := 4983230072969 + 3 ^ 40 * 6597067 * 2
def baseEnd_6597067 : Nat := 3387466280914645678723147

theorem tailTrace_6597067 : CollatzResearch.WordTrace tailWord_6597067 prefixEnd_6597067 3387466280914645678723147 := by
  unfold tailWord_6597067
  simp only [CollatzResearch.WordTrace]
  refine ⟨240614800790960423188389455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160409867193973615458926303 240614800790960423188389455)
  ·
    refine ⟨360922201186440634782584183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240614800790960423188389455 360922201186440634782584183)
    ·
      refine ⟨541383301779660952173876275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360922201186440634782584183 541383301779660952173876275)
      ·
        refine ⟨812074952669491428260814413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 541383301779660952173876275 812074952669491428260814413)
        ·
          refine ⟨304528107251059285597805405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 812074952669491428260814413 304528107251059285597805405)
          ·
            refine ⟨114198040219147232099177027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 304528107251059285597805405 114198040219147232099177027)
            ·
              refine ⟨171297060328720848148765541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114198040219147232099177027 171297060328720848148765541)
              ·
                refine ⟨32118198811635159027893539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 171297060328720848148765541 32118198811635159027893539)
                ·
                  refine ⟨48177298217452738541840309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32118198811635159027893539 48177298217452738541840309)
                  ·
                    refine ⟨4516621707886194238297529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48177298217452738541840309 4516621707886194238297529)
                    ·
                      refine ⟨3387466280914645678723147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4516621707886194238297529 3387466280914645678723147)
                      ·
                        rfl

theorem cell23_6597067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 4, 1, 5, 2].length) (baseStart_6597067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6597067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6597067 prefixEnd_6597067 := by exact prefixLift 6597067
  have htrace : WordTrace (prefixWord ++ tailWord_6597067) baseStart_6597067 baseEnd_6597067 := by
    simpa [prefixWord, tailWord_6597067, baseEnd_6597067] using wordTrace_append hprefix tailTrace_6597067
  have hstable : (prefixWord ++ tailWord_6597067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6597067).length < 2 ^ (prefixWord ++ tailWord_6597067).sum := by decide
  have hdescent : baseEnd_6597067 < baseStart_6597067 := by decide
  rcases family_descends (prefixWord ++ tailWord_6597067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6597070 : List Nat := [4, 1, 1, 1, 2, 1, 1, 1, 1, 3, 7]
def baseStart_6597070 : Nat := 118140960795 + 6597070 * 2 ^ 59
def prefixEnd_6597070 : Nat := 4983230072969 + 3 ^ 40 * 6597070 * 2
def baseEnd_6597070 : Nat := 3387467821356609166985633

theorem tailTrace_6597070 : CollatzResearch.WordTrace tailWord_6597070 prefixEnd_6597070 3387467821356609166985633 := by
  unfold tailWord_6597070
  simp only [CollatzResearch.WordTrace]
  refine ⟨30076863776243694337593583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160409940139966369800499109 30076863776243694337593583)
  ·
    refine ⟨45115295664365541506390375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30076863776243694337593583 45115295664365541506390375)
    ·
      refine ⟨67672943496548312259585563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45115295664365541506390375 67672943496548312259585563)
      ·
        refine ⟨101509415244822468389378345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67672943496548312259585563 101509415244822468389378345)
        ·
          refine ⟨76132061433616851292033759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101509415244822468389378345 76132061433616851292033759)
          ·
            refine ⟨114198092150425276938050639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76132061433616851292033759 114198092150425276938050639)
            ·
              refine ⟨171297138225637915407075959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114198092150425276938050639 171297138225637915407075959)
              ·
                refine ⟨256945707338456873110613939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171297138225637915407075959 256945707338456873110613939)
                ·
                  refine ⟨385418561007685309665920909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 256945707338456873110613939 385418561007685309665920909)
                  ·
                    refine ⟨144531960377881991124720341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 385418561007685309665920909 144531960377881991124720341)
                    ·
                      refine ⟨3387467821356609166985633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 144531960377881991124720341 3387467821356609166985633)
                      ·
                        rfl

theorem cell23_6597070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 1, 3, 7].length) (baseStart_6597070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6597070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6597070 prefixEnd_6597070 := by exact prefixLift 6597070
  have htrace : WordTrace (prefixWord ++ tailWord_6597070) baseStart_6597070 baseEnd_6597070 := by
    simpa [prefixWord, tailWord_6597070, baseEnd_6597070] using wordTrace_append hprefix tailTrace_6597070
  have hstable : (prefixWord ++ tailWord_6597070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6597070).length < 2 ^ (prefixWord ++ tailWord_6597070).sum := by decide
  have hdescent : baseEnd_6597070 < baseStart_6597070 := by decide
  rcases family_descends (prefixWord ++ tailWord_6597070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6597077 : List Nat := [1, 3, 2, 3, 1, 2, 2, 1, 3, 5]
def baseStart_6597077 : Nat := 118140960795 + 6597077 * 2 ^ 59
def prefixEnd_6597077 : Nat := 4983230072969 + 3 ^ 40 * 6597077 * 2
def baseEnd_6597077 : Nat := 1129157138573730213199367

theorem tailTrace_6597077 : CollatzResearch.WordTrace tailWord_6597077 prefixEnd_6597077 1129157138573730213199367 := by
  unfold tailWord_6597077
  simp only [CollatzResearch.WordTrace]
  refine ⟨240615165520924194896253485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160410110347282796597502323 240615165520924194896253485)
  ·
    refine ⟨90230687070346573086095057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 240615165520924194896253485 90230687070346573086095057)
    ·
      refine ⟨67673015302759929814571293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90230687070346573086095057 67673015302759929814571293)
      ·
        refine ⟨25377380738534973680464235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67673015302759929814571293 25377380738534973680464235)
        ·
          refine ⟨38066071107802460520696353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25377380738534973680464235 38066071107802460520696353)
          ·
            refine ⟨28549553330851845390522265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38066071107802460520696353 28549553330851845390522265)
            ·
              refine ⟨21412164998138884042891699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28549553330851845390522265 21412164998138884042891699)
              ·
                refine ⟨32118247497208326064337549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21412164998138884042891699 32118247497208326064337549)
                ·
                  refine ⟨12044342811453122274126581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32118247497208326064337549 12044342811453122274126581)
                  ·
                    refine ⟨1129157138573730213199367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12044342811453122274126581 1129157138573730213199367)
                    ·
                      rfl

theorem cell23_6597077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 1, 3, 5].length) (baseStart_6597077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6597077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6597077 prefixEnd_6597077 := by exact prefixLift 6597077
  have htrace : WordTrace (prefixWord ++ tailWord_6597077) baseStart_6597077 baseEnd_6597077 := by
    simpa [prefixWord, tailWord_6597077, baseEnd_6597077] using wordTrace_append hprefix tailTrace_6597077
  have hstable : (prefixWord ++ tailWord_6597077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6597077).length < 2 ^ (prefixWord ++ tailWord_6597077).sum := by decide
  have hdescent : baseEnd_6597077 < baseStart_6597077 := by decide
  rcases family_descends (prefixWord ++ tailWord_6597077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6597107 : List Nat := [1, 1, 1, 2, 2, 2, 5, 1, 4, 4]
def baseStart_6597107 : Nat := 118140960795 + 6597107 * 2 ^ 59
def prefixEnd_6597107 : Nat := 4983230072969 + 3 ^ 40 * 6597107 * 2
def baseEnd_6597107 : Nat := 1129162273380275174074321

theorem tailTrace_6597107 : CollatzResearch.WordTrace tailWord_6597107 prefixEnd_6597107 1129162273380275174074321 := by
  unfold tailWord_6597107
  simp only [CollatzResearch.WordTrace]
  refine ⟨240616259710815510019845575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160410839807210340013230383 240616259710815510019845575)
  ·
    refine ⟨360924389566223265029768363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240616259710815510019845575 360924389566223265029768363)
    ·
      refine ⟨541386584349334897544652545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360924389566223265029768363 541386584349334897544652545)
      ·
        refine ⟨406039938262001173158489409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 541386584349334897544652545 406039938262001173158489409)
        ·
          refine ⟨304529953696500879868867057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 406039938262001173158489409 304529953696500879868867057)
          ·
            refine ⟨228397465272375659901650293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 304529953696500879868867057 228397465272375659901650293)
            ·
              refine ⟨21412262369285218115779715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 228397465272375659901650293 21412262369285218115779715)
              ·
                refine ⟨32118393553927827173669573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21412262369285218115779715 32118393553927827173669573)
                ·
                  refine ⟨6022198791361467595063045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32118393553927827173669573 6022198791361467595063045)
                  ·
                    refine ⟨1129162273380275174074321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6022198791361467595063045 1129162273380275174074321)
                    ·
                      rfl

theorem cell23_6597107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 1, 4, 4].length) (baseStart_6597107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6597107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6597107 prefixEnd_6597107 := by exact prefixLift 6597107
  have htrace : WordTrace (prefixWord ++ tailWord_6597107) baseStart_6597107 baseEnd_6597107 := by
    simpa [prefixWord, tailWord_6597107, baseEnd_6597107] using wordTrace_append hprefix tailTrace_6597107
  have hstable : (prefixWord ++ tailWord_6597107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6597107).length < 2 ^ (prefixWord ++ tailWord_6597107).sum := by decide
  have hdescent : baseEnd_6597107 < baseStart_6597107 := by decide
  rcases family_descends (prefixWord ++ tailWord_6597107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6597117 : List Nat := [1, 4, 1, 1, 1, 3, 3, 2, 1, 1, 5]
def baseStart_6597117 : Nat := 118140960795 + 6597117 * 2 ^ 59
def prefixEnd_6597117 : Nat := 4983230072969 + 3 ^ 40 * 6597117 * 2
def baseEnd_6597117 : Nat := 3387491954947370483097917

theorem tailTrace_6597117 : CollatzResearch.WordTrace tailWord_6597117 prefixEnd_6597117 3387491954947370483097917 := by
  unfold tailWord_6597117
  simp only [CollatzResearch.WordTrace]
  refine ⟨240616624440779281727709605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160411082960519521151806403 240616624440779281727709605)
  ·
    refine ⟨45115617082646115323945551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 240616624440779281727709605 45115617082646115323945551)
    ·
      refine ⟨67673425623969172985918327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45115617082646115323945551 67673425623969172985918327)
      ·
        refine ⟨101510138435953759478877491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67673425623969172985918327 101510138435953759478877491)
        ·
          refine ⟨152265207653930639218316237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101510138435953759478877491 152265207653930639218316237)
          ·
            refine ⟨57099452870223989706868589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 152265207653930639218316237 57099452870223989706868589)
            ·
              refine ⟨21412294826333996140075721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57099452870223989706868589 21412294826333996140075721)
              ·
                refine ⟨16059221119750497105056791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21412294826333996140075721 16059221119750497105056791)
                ·
                  refine ⟨24088831679625745657585187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16059221119750497105056791 24088831679625745657585187)
                  ·
                    refine ⟨36133247519438618486377781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24088831679625745657585187 36133247519438618486377781)
                    ·
                      refine ⟨3387491954947370483097917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36133247519438618486377781 3387491954947370483097917)
                      ·
                        rfl

theorem cell23_6597117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 2, 1, 1, 5].length) (baseStart_6597117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6597117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6597117 prefixEnd_6597117 := by exact prefixLift 6597117
  have htrace : WordTrace (prefixWord ++ tailWord_6597117) baseStart_6597117 baseEnd_6597117 := by
    simpa [prefixWord, tailWord_6597117, baseEnd_6597117] using wordTrace_append hprefix tailTrace_6597117
  have hstable : (prefixWord ++ tailWord_6597117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6597117).length < 2 ^ (prefixWord ++ tailWord_6597117).sum := by decide
  have hdescent : baseEnd_6597117 < baseStart_6597117 := by decide
  rcases family_descends (prefixWord ++ tailWord_6597117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6597124 : List Nat := [2, 3, 2, 3, 1, 1, 3, 1, 1, 6]
def baseStart_6597124 : Nat := 118140960795 + 6597124 * 2 ^ 59
def prefixEnd_6597124 : Nat := 4983230072969 + 3 ^ 40 * 6597124 * 2
def baseEnd_6597124 : Nat := 1129165183103983985236795

theorem tailTrace_6597124 : CollatzResearch.WordTrace tailWord_6597124 prefixEnd_6597124 1129165183103983985236795 := by
  unfold tailWord_6597124
  simp only [CollatzResearch.WordTrace]
  refine ⟨120308439875876960961607213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160411253167835947948809617 120308439875876960961607213)
  ·
    refine ⟨45115664953453860360602705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120308439875876960961607213 45115664953453860360602705)
    ·
      refine ⟨33836748715090395270452029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45115664953453860360602705 33836748715090395270452029)
      ·
        refine ⟨12688780768158898226419511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33836748715090395270452029 12688780768158898226419511)
        ·
          refine ⟨19033171152238347339629267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12688780768158898226419511 19033171152238347339629267)
          ·
            refine ⟨28549756728357521009443901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19033171152238347339629267 28549756728357521009443901)
            ·
              refine ⟨10706158773134070378541463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28549756728357521009443901 10706158773134070378541463)
              ·
                refine ⟨16059238159701105567812195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10706158773134070378541463 16059238159701105567812195)
                ·
                  refine ⟨24088857239551658351718293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16059238159701105567812195 24088857239551658351718293)
                  ·
                    refine ⟨1129165183103983985236795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24088857239551658351718293 1129165183103983985236795)
                    ·
                      rfl

theorem cell23_6597124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 1, 1, 6].length) (baseStart_6597124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6597124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6597124 prefixEnd_6597124 := by exact prefixLift 6597124
  have htrace : WordTrace (prefixWord ++ tailWord_6597124) baseStart_6597124 baseEnd_6597124 := by
    simpa [prefixWord, tailWord_6597124, baseEnd_6597124] using wordTrace_append hprefix tailTrace_6597124
  have hstable : (prefixWord ++ tailWord_6597124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6597124).length < 2 ^ (prefixWord ++ tailWord_6597124).sum := by decide
  have hdescent : baseEnd_6597124 < baseStart_6597124 := by decide
  rcases family_descends (prefixWord ++ tailWord_6597124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6597131 : List Nat := [1, 1, 1, 1, 7, 1, 2, 2, 3, 2, 2]
def baseStart_6597131 : Nat := 118140960795 + 6597131 * 2 ^ 59
def prefixEnd_6597131 : Nat := 4983230072969 + 3 ^ 40 * 6597131 * 2
def baseEnd_6597131 : Nat := 3387499143676533428322853

theorem tailTrace_6597131 : CollatzResearch.WordTrace tailWord_6597131 prefixEnd_6597131 3387499143676533428322853 := by
  unfold tailWord_6597131
  simp only [CollatzResearch.WordTrace]
  refine ⟨240617135062728562118719247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160411423375152374745812831 240617135062728562118719247)
  ·
    refine ⟨360925702594092843178078871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240617135062728562118719247 360925702594092843178078871)
    ·
      refine ⟨541388553891139264767118307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360925702594092843178078871 541388553891139264767118307)
      ·
        refine ⟨812082830836708897150677461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 541388553891139264767118307 812082830836708897150677461)
        ·
          refine ⟨19033191347735364776969003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 812082830836708897150677461 19033191347735364776969003)
          ·
            refine ⟨28549787021603047165453505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19033191347735364776969003 28549787021603047165453505)
            ·
              refine ⟨21412340266202285374090129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28549787021603047165453505 21412340266202285374090129)
              ·
                refine ⟨16059255199651714030567597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21412340266202285374090129 16059255199651714030567597)
                ·
                  refine ⟨6022220699869392761462849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16059255199651714030567597 6022220699869392761462849)
                  ·
                    refine ⟨4516665524902044571097137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6022220699869392761462849 4516665524902044571097137)
                    ·
                      refine ⟨3387499143676533428322853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4516665524902044571097137 3387499143676533428322853)
                      ·
                        rfl

theorem cell23_6597131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 2, 3, 2, 2].length) (baseStart_6597131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6597131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6597131 prefixEnd_6597131 := by exact prefixLift 6597131
  have htrace : WordTrace (prefixWord ++ tailWord_6597131) baseStart_6597131 baseEnd_6597131 := by
    simpa [prefixWord, tailWord_6597131, baseEnd_6597131] using wordTrace_append hprefix tailTrace_6597131
  have hstable : (prefixWord ++ tailWord_6597131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6597131).length < 2 ^ (prefixWord ++ tailWord_6597131).sum := by decide
  have hdescent : baseEnd_6597131 < baseStart_6597131 := by decide
  rcases family_descends (prefixWord ++ tailWord_6597131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6597191 : List Nat := [1, 1, 4, 1, 4, 2, 1, 1, 3, 3, 2]
def baseStart_6597191 : Nat := 118140960795 + 6597191 * 2 ^ 59
def prefixEnd_6597191 : Nat := 4983230072969 + 3 ^ 40 * 6597191 * 2
def baseEnd_6597191 : Nat := 3387529952515803193572577

theorem tailTrace_6597191 : CollatzResearch.WordTrace tailWord_6597191 prefixEnd_6597191 3387529952515803193572577 := by
  unfold tailWord_6597191
  simp only [CollatzResearch.WordTrace]
  refine ⟨240619323442511192365903427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160412882295007461577268951 240619323442511192365903427)
  ·
    refine ⟨360928985163766788548855141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240619323442511192365903427 360928985163766788548855141)
    ·
      refine ⟨67674184718206272852910339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 360928985163766788548855141 67674184718206272852910339)
      ·
        refine ⟨101511277077309409279365509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67674184718206272852910339 101511277077309409279365509)
        ·
          refine ⟨19033364451995514239881033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101511277077309409279365509 19033364451995514239881033)
          ·
            refine ⟨14275023338996635679910775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19033364451995514239881033 14275023338996635679910775)
            ·
              refine ⟨21412535008494953519866163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14275023338996635679910775 21412535008494953519866163)
              ·
                refine ⟨32118802512742430279799245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21412535008494953519866163 32118802512742430279799245)
                ·
                  refine ⟨12044550942278411354924717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32118802512742430279799245 12044550942278411354924717)
                  ·
                    refine ⟨4516706603354404258096769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12044550942278411354924717 4516706603354404258096769)
                    ·
                      refine ⟨3387529952515803193572577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4516706603354404258096769 3387529952515803193572577)
                      ·
                        rfl

theorem cell23_6597191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 1, 3, 3, 2].length) (baseStart_6597191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6597191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6597191 prefixEnd_6597191 := by exact prefixLift 6597191
  have htrace : WordTrace (prefixWord ++ tailWord_6597191) baseStart_6597191 baseEnd_6597191 := by
    simpa [prefixWord, tailWord_6597191, baseEnd_6597191] using wordTrace_append hprefix tailTrace_6597191
  have hstable : (prefixWord ++ tailWord_6597191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6597191).length < 2 ^ (prefixWord ++ tailWord_6597191).sum := by decide
  have hdescent : baseEnd_6597191 < baseStart_6597191 := by decide
  rcases family_descends (prefixWord ++ tailWord_6597191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6597207 : List Nat := [1, 1, 3, 2, 2, 2, 1, 3, 2, 1, 5]
def baseStart_6597207 : Nat := 118140960795 + 6597207 * 2 ^ 59
def prefixEnd_6597207 : Nat := 4983230072969 + 3 ^ 40 * 6597207 * 2
def baseEnd_6597207 : Nat := 3387538168206275130972503

theorem tailTrace_6597207 : CollatzResearch.WordTrace tailWord_6597207 prefixEnd_6597207 3387538168206275130972503 := by
  unfold tailWord_6597207
  simp only [CollatzResearch.WordTrace]
  refine ⟨240619907010453227098485875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160413271340302151398990583 240619907010453227098485875)
  ·
    refine ⟨360929860515679840647728813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240619907010453227098485875 360929860515679840647728813)
    ·
      refine ⟨135348697693379940242898305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 360929860515679840647728813 135348697693379940242898305)
      ·
        refine ⟨101511523270034955182173729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135348697693379940242898305 101511523270034955182173729)
        ·
          refine ⟨76133642452526216386630297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101511523270034955182173729 76133642452526216386630297)
          ·
            refine ⟨57100231839394662289972723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76133642452526216386630297 57100231839394662289972723)
            ·
              refine ⟨85650347759091993434959085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57100231839394662289972723 85650347759091993434959085)
              ·
                refine ⟨32118880409659497538109657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85650347759091993434959085 32118880409659497538109657)
                ·
                  refine ⟨24089160307244623153582243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32118880409659497538109657 24089160307244623153582243)
                  ·
                    refine ⟨36133740460866934730373365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24089160307244623153582243 36133740460866934730373365)
                    ·
                      refine ⟨3387538168206275130972503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36133740460866934730373365 3387538168206275130972503)
                      ·
                        rfl

theorem cell23_6597207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 3, 2, 1, 5].length) (baseStart_6597207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6597207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6597207 prefixEnd_6597207 := by exact prefixLift 6597207
  have htrace : WordTrace (prefixWord ++ tailWord_6597207) baseStart_6597207 baseEnd_6597207 := by
    simpa [prefixWord, tailWord_6597207, baseEnd_6597207] using wordTrace_append hprefix tailTrace_6597207
  have hstable : (prefixWord ++ tailWord_6597207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6597207).length < 2 ^ (prefixWord ++ tailWord_6597207).sum := by decide
  have hdescent : baseEnd_6597207 < baseStart_6597207 := by decide
  rcases family_descends (prefixWord ++ tailWord_6597207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6597361 : List Nat := [1, 2, 2, 2, 2, 2, 2, 1, 5, 1, 3]
def baseStart_6597361 : Nat := 118140960795 + 6597361 * 2 ^ 59
def prefixEnd_6597361 : Nat := 4983230072969 + 3 ^ 40 * 6597361 * 2
def baseEnd_6597361 : Nat := 3387617244227067528446795

theorem tailTrace_6597361 : CollatzResearch.WordTrace tailWord_6597361 prefixEnd_6597361 3387617244227067528446795 := by
  unfold tailWord_6597361
  simp only [CollatzResearch.WordTrace]
  refine ⟨240625523851895311399591937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160417015901263540933061291 240625523851895311399591937)
  ·
    refine ⟨180469142888921483549693953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240625523851895311399591937 180469142888921483549693953)
    ·
      refine ⟨135351857166691112662270465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180469142888921483549693953 135351857166691112662270465)
      ·
        refine ⟨101513892875018334496702849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135351857166691112662270465 101513892875018334496702849)
        ·
          refine ⟨76135419656263750872527137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101513892875018334496702849 76135419656263750872527137)
          ·
            refine ⟨57101564742197813154395353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76135419656263750872527137 57101564742197813154395353)
            ·
              refine ⟨42826173556648359865796515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57101564742197813154395353 42826173556648359865796515)
              ·
                refine ⟨64239260334972539798694773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42826173556648359865796515 64239260334972539798694773)
                ·
                  refine ⟨6022430656403675606127635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64239260334972539798694773 6022430656403675606127635)
                  ·
                    refine ⟨9033645984605513409191453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6022430656403675606127635 9033645984605513409191453)
                    ·
                      refine ⟨3387617244227067528446795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9033645984605513409191453 3387617244227067528446795)
                      ·
                        rfl

theorem cell23_6597361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 5, 1, 3].length) (baseStart_6597361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6597361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6597361 prefixEnd_6597361 := by exact prefixLift 6597361
  have htrace : WordTrace (prefixWord ++ tailWord_6597361) baseStart_6597361 baseEnd_6597361 := by
    simpa [prefixWord, tailWord_6597361, baseEnd_6597361] using wordTrace_append hprefix tailTrace_6597361
  have hstable : (prefixWord ++ tailWord_6597361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6597361).length < 2 ^ (prefixWord ++ tailWord_6597361).sum := by decide
  have hdescent : baseEnd_6597361 < baseStart_6597361 := by decide
  rcases family_descends (prefixWord ++ tailWord_6597361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6597422 : List Nat := [4, 1, 3, 2, 1, 3, 1, 1, 2, 3, 2]
def baseStart_6597422 : Nat := 118140960795 + 6597422 * 2 ^ 59
def prefixEnd_6597422 : Nat := 4983230072969 + 3 ^ 40 * 6597422 * 2
def baseEnd_6597422 : Nat := 3387648566546991789784015

theorem tailTrace_6597422 : CollatzResearch.WordTrace tailWord_6597422 prefixEnd_6597422 3387648566546991789784015 := by
  unfold tailWord_6597422
  simp only [CollatzResearch.WordTrace]
  refine ⟨30078468588084289852195315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160418499136449545878375013 30078468588084289852195315)
  ·
    refine ⟨45117702882126434778292973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30078468588084289852195315 45117702882126434778292973)
    ·
      refine ⟨16919138580797413041859865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45117702882126434778292973 16919138580797413041859865)
      ·
        refine ⟨12689353935598059781394899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16919138580797413041859865 12689353935598059781394899)
        ·
          refine ⟨19034030903397089672092349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12689353935598059781394899 19034030903397089672092349)
          ·
            refine ⟨7137761588773908627034631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19034030903397089672092349 7137761588773908627034631)
            ·
              refine ⟨10706642383160862940551947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7137761588773908627034631 10706642383160862940551947)
              ·
                refine ⟨16059963574741294410827921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10706642383160862940551947 16059963574741294410827921)
                ·
                  refine ⟨12044972681055970808120941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16059963574741294410827921 12044972681055970808120941)
                  ·
                    refine ⟨4516864755395989053045353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12044972681055970808120941 4516864755395989053045353)
                    ·
                      refine ⟨3387648566546991789784015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4516864755395989053045353 3387648566546991789784015)
                      ·
                        rfl

theorem cell23_6597422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_6597422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6597422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6597422 prefixEnd_6597422 := by exact prefixLift 6597422
  have htrace : WordTrace (prefixWord ++ tailWord_6597422) baseStart_6597422 baseEnd_6597422 := by
    simpa [prefixWord, tailWord_6597422, baseEnd_6597422] using wordTrace_append hprefix tailTrace_6597422
  have hstable : (prefixWord ++ tailWord_6597422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6597422).length < 2 ^ (prefixWord ++ tailWord_6597422).sum := by decide
  have hdescent : baseEnd_6597422 < baseStart_6597422 := by decide
  rcases family_descends (prefixWord ++ tailWord_6597422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6597452 : List Nat := [2, 2, 1, 3, 3, 1, 2, 4, 1, 2, 2]
def baseStart_6597452 : Nat := 118140960795 + 6597452 * 2 ^ 59
def prefixEnd_6597452 : Nat := 4983230072969 + 3 ^ 40 * 6597452 * 2
def baseEnd_6597452 : Nat := 3387663970966626672408877

theorem tailTrace_6597452 : CollatzResearch.WordTrace tailWord_6597452 prefixEnd_6597452 3387663970966626672408877 := by
  unfold tailWord_6597452
  simp only [CollatzResearch.WordTrace]
  refine ⟨120314421447282816970577305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160419228596377089294103073 120314421447282816970577305)
  ·
    refine ⟨90235816085462112727932979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120314421447282816970577305 90235816085462112727932979)
    ·
      refine ⟨135353724128193169091899469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90235816085462112727932979 135353724128193169091899469)
      ·
        refine ⟨50757646548072438409462301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135353724128193169091899469 50757646548072438409462301)
        ·
          refine ⟨19034117455527164403548363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50757646548072438409462301 19034117455527164403548363)
          ·
            refine ⟨28551176183290746605322545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19034117455527164403548363 28551176183290746605322545)
            ·
              refine ⟨21413382137468059953991909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28551176183290746605322545 21413382137468059953991909)
              ·
                refine ⟨4015009150775261241373483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21413382137468059953991909 4015009150775261241373483)
                ·
                  refine ⟨6022513726162891862060225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4015009150775261241373483 6022513726162891862060225)
                  ·
                    refine ⟨4516885294622168896545169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6022513726162891862060225 4516885294622168896545169)
                    ·
                      refine ⟨3387663970966626672408877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4516885294622168896545169 3387663970966626672408877)
                      ·
                        rfl

theorem cell23_6597452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 4, 1, 2, 2].length) (baseStart_6597452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6597452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6597452 prefixEnd_6597452 := by exact prefixLift 6597452
  have htrace : WordTrace (prefixWord ++ tailWord_6597452) baseStart_6597452 baseEnd_6597452 := by
    simpa [prefixWord, tailWord_6597452, baseEnd_6597452] using wordTrace_append hprefix tailTrace_6597452
  have hstable : (prefixWord ++ tailWord_6597452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6597452).length < 2 ^ (prefixWord ++ tailWord_6597452).sum := by decide
  have hdescent : baseEnd_6597452 < baseStart_6597452 := by decide
  rcases family_descends (prefixWord ++ tailWord_6597452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6597454 : List Nat := [4, 1, 1, 1, 1, 1, 1, 3, 1, 9]
def baseStart_6597454 : Nat := 118140960795 + 6597454 * 2 ^ 59
def prefixEnd_6597454 : Nat := 4983230072969 + 3 ^ 40 * 6597454 * 2
def baseEnd_6597454 : Nat := 1129221665975978554861289

theorem tailTrace_6597454 : CollatzResearch.WordTrace tailWord_6597454 prefixEnd_6597454 1129221665975978554861289 := by
  unfold tailWord_6597454
  simp only [CollatzResearch.WordTrace]
  refine ⟨30078614480069798535340927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160419277227038925521818277 30078614480069798535340927)
  ·
    refine ⟨45117921720104697803011391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30078614480069798535340927 45117921720104697803011391)
    ·
      refine ⟨67676882580157046704517087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45117921720104697803011391 67676882580157046704517087)
      ·
        refine ⟨101515323870235570056775631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67676882580157046704517087 101515323870235570056775631)
        ·
          refine ⟨152272985805353355085163447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101515323870235570056775631 152272985805353355085163447)
          ·
            refine ⟨228409478708030032627745171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152272985805353355085163447 228409478708030032627745171)
            ·
              refine ⟨342614218062045048941617757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228409478708030032627745171 342614218062045048941617757)
              ·
                refine ⟨128480331773266893353106659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 342614218062045048941617757 128480331773266893353106659)
                ·
                  refine ⟨192720497659900340029659989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 128480331773266893353106659 192720497659900340029659989)
                  ·
                    refine ⟨1129221665975978554861289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 192720497659900340029659989 1129221665975978554861289)
                    ·
                      rfl

theorem cell23_6597454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 1, 9].length) (baseStart_6597454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6597454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6597454 prefixEnd_6597454 := by exact prefixLift 6597454
  have htrace : WordTrace (prefixWord ++ tailWord_6597454) baseStart_6597454 baseEnd_6597454 := by
    simpa [prefixWord, tailWord_6597454, baseEnd_6597454] using wordTrace_append hprefix tailTrace_6597454
  have hstable : (prefixWord ++ tailWord_6597454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6597454).length < 2 ^ (prefixWord ++ tailWord_6597454).sum := by decide
  have hdescent : baseEnd_6597454 < baseStart_6597454 := by decide
  rcases family_descends (prefixWord ++ tailWord_6597454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6597464 : List Nat := [2, 1, 2, 2, 1, 1, 1, 2, 4, 2, 5]
def baseStart_6597464 : Nat := 118140960795 + 6597464 * 2 ^ 59
def prefixEnd_6597464 : Nat := 4983230072969 + 3 ^ 40 * 6597464 * 2
def baseEnd_6597464 : Nat := 3387670132734480625458821

theorem tailTrace_6597464 : CollatzResearch.WordTrace tailWord_6597464 prefixEnd_6597464 3387670132734480625458821 := by
  unfold tailWord_6597464
  simp only [CollatzResearch.WordTrace]
  refine ⟨120314640285261079995295723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160419520380348106660394297 120314640285261079995295723)
  ·
    refine ⟨180471960427891619992943585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120314640285261079995295723 180471960427891619992943585)
    ·
      refine ⟨135353970320918714994707689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180471960427891619992943585 135353970320918714994707689)
      ·
        refine ⟨101515477740689036246030767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135353970320918714994707689 101515477740689036246030767)
        ·
          refine ⟨152273216611033554369046151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101515477740689036246030767 152273216611033554369046151)
          ·
            refine ⟨228409824916550331553569227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152273216611033554369046151 228409824916550331553569227)
            ·
              refine ⟨342614737374825497330353841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228409824916550331553569227 342614737374825497330353841)
              ·
                refine ⟨256961053031119122997765381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 342614737374825497330353841 256961053031119122997765381)
                ·
                  refine ⟨48180197443334835562081009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 256961053031119122997765381 48180197443334835562081009)
                  ·
                    refine ⟨36135148082501126671560757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48180197443334835562081009 36135148082501126671560757)
                    ·
                      refine ⟨3387670132734480625458821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36135148082501126671560757 3387670132734480625458821)
                      ·
                        rfl

theorem cell23_6597464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 4, 2, 5].length) (baseStart_6597464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6597464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6597464 prefixEnd_6597464 := by exact prefixLift 6597464
  have htrace : WordTrace (prefixWord ++ tailWord_6597464) baseStart_6597464 baseEnd_6597464 := by
    simpa [prefixWord, tailWord_6597464, baseEnd_6597464] using wordTrace_append hprefix tailTrace_6597464
  have hstable : (prefixWord ++ tailWord_6597464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6597464).length < 2 ^ (prefixWord ++ tailWord_6597464).sum := by decide
  have hdescent : baseEnd_6597464 < baseStart_6597464 := by decide
  rcases family_descends (prefixWord ++ tailWord_6597464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6597486 : List Nat := [4, 1, 2, 3, 2, 2, 1, 3, 1, 2, 2]
def baseStart_6597486 : Nat := 118140960795 + 6597486 * 2 ^ 59
def prefixEnd_6597486 : Nat := 4983230072969 + 3 ^ 40 * 6597486 * 2
def baseEnd_6597486 : Nat := 3387681429308879539383721

theorem tailTrace_6597486 : CollatzResearch.WordTrace tailWord_6597486 prefixEnd_6597486 3387681429308879539383721 := by
  unfold tailWord_6597486
  simp only [CollatzResearch.WordTrace]
  refine ⟨30078760372055307218486539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160420055317628305165261541 30078760372055307218486539)
  ·
    refine ⟨45118140558082960827729809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30078760372055307218486539 45118140558082960827729809)
    ·
      refine ⟨33838605418562220620797357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45118140558082960827729809 33838605418562220620797357)
      ·
        refine ⟨12689477031960832732799009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33838605418562220620797357 12689477031960832732799009)
        ·
          refine ⟨9517107773970624549599257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12689477031960832732799009 9517107773970624549599257)
          ·
            refine ⟨7137830830477968412199443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9517107773970624549599257 7137830830477968412199443)
            ·
              refine ⟨10706746245716952618299165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7137830830477968412199443 10706746245716952618299165)
              ·
                refine ⟨4015029842143857231862187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10706746245716952618299165 4015029842143857231862187)
                ·
                  refine ⟨6022544763215785847793281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4015029842143857231862187 6022544763215785847793281)
                  ·
                    refine ⟨4516908572411839385844961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6022544763215785847793281 4516908572411839385844961)
                    ·
                      refine ⟨3387681429308879539383721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4516908572411839385844961 3387681429308879539383721)
                      ·
                        rfl

theorem cell23_6597486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_6597486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6597486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6597486 prefixEnd_6597486 := by exact prefixLift 6597486
  have htrace : WordTrace (prefixWord ++ tailWord_6597486) baseStart_6597486 baseEnd_6597486 := by
    simpa [prefixWord, tailWord_6597486, baseEnd_6597486] using wordTrace_append hprefix tailTrace_6597486
  have hstable : (prefixWord ++ tailWord_6597486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6597486).length < 2 ^ (prefixWord ++ tailWord_6597486).sum := by decide
  have hdescent : baseEnd_6597486 < baseStart_6597486 := by decide
  rcases family_descends (prefixWord ++ tailWord_6597486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6597504 : List Nat := [2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 6]
def baseStart_6597504 : Nat := 118140960795 + 6597504 * 2 ^ 59
def prefixEnd_6597504 : Nat := 4983230072969 + 3 ^ 40 * 6597504 * 2
def baseEnd_6597504 : Nat := 3387690671960660468958637

theorem tailTrace_6597504 : CollatzResearch.WordTrace tailWord_6597504 prefixEnd_6597504 3387690671960660468958637 := by
  unfold tailWord_6597504
  simp only [CollatzResearch.WordTrace]
  refine ⟨120315369745188623411023783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160420492993584831214698377 120315369745188623411023783)
  ·
    refine ⟨180473054617782935116535675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120315369745188623411023783 180473054617782935116535675)
    ·
      refine ⟨270709581926674402674803513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180473054617782935116535675 270709581926674402674803513)
      ·
        refine ⟨203032186445005802006102635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270709581926674402674803513 203032186445005802006102635)
        ·
          refine ⟨304548279667508703009153953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203032186445005802006102635 304548279667508703009153953)
          ·
            refine ⟨228411209750631527256865465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 304548279667508703009153953 228411209750631527256865465)
            ·
              refine ⟨171308407312973645442649099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228411209750631527256865465 171308407312973645442649099)
              ·
                refine ⟨256962610969460468163973649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171308407312973645442649099 256962610969460468163973649)
                ·
                  refine ⟨192721958227095351122980237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 256962610969460468163973649 192721958227095351122980237)
                  ·
                    refine ⟨72270734335160756671117589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 192721958227095351122980237 72270734335160756671117589)
                    ·
                      refine ⟨3387690671960660468958637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72270734335160756671117589 3387690671960660468958637)
                      ·
                        rfl

theorem cell23_6597504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 6].length) (baseStart_6597504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6597504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6597504 prefixEnd_6597504 := by exact prefixLift 6597504
  have htrace : WordTrace (prefixWord ++ tailWord_6597504) baseStart_6597504 baseEnd_6597504 := by
    simpa [prefixWord, tailWord_6597504, baseEnd_6597504] using wordTrace_append hprefix tailTrace_6597504
  have hstable : (prefixWord ++ tailWord_6597504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6597504).length < 2 ^ (prefixWord ++ tailWord_6597504).sum := by decide
  have hdescent : baseEnd_6597504 < baseStart_6597504 := by decide
  rcases family_descends (prefixWord ++ tailWord_6597504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6597541 : List Nat := [1, 3, 1, 2, 1, 1, 1, 1, 6, 3, 3]
def baseStart_6597541 : Nat := 118140960795 + 6597541 * 2 ^ 59
def prefixEnd_6597541 : Nat := 4983230072969 + 3 ^ 40 * 6597541 * 2
def baseEnd_6597541 : Nat := 3387709670744876824195967

theorem tailTrace_6597541 : CollatzResearch.WordTrace tailWord_6597541 prefixEnd_6597541 3387709670744876824195967 := by
  unfold tailWord_6597541
  simp only [CollatzResearch.WordTrace]
  refine ⟨240632088991243202141144477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160421392660828801427429651 240632088991243202141144477)
  ·
    refine ⟨90237033371716200802929179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 240632088991243202141144477 90237033371716200802929179)
    ·
      refine ⟨135355550057574301204393769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90237033371716200802929179 135355550057574301204393769)
      ·
        refine ⟨101516662543180725903295327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135355550057574301204393769 101516662543180725903295327)
        ·
          refine ⟨152274993814771088854942991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101516662543180725903295327 152274993814771088854942991)
          ·
            refine ⟨228412490722156633282414487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152274993814771088854942991 228412490722156633282414487)
            ·
              refine ⟨342618736083234949923621731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228412490722156633282414487 342618736083234949923621731)
              ·
                refine ⟨513928104124852424885432597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 342618736083234949923621731 513928104124852424885432597)
                ·
                  refine ⟨24090379880852457416504653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 513928104124852424885432597 24090379880852457416504653)
                  ·
                    refine ⟨9033892455319671531189245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24090379880852457416504653 9033892455319671531189245)
                    ·
                      refine ⟨3387709670744876824195967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9033892455319671531189245 3387709670744876824195967)
                      ·
                        rfl

theorem cell23_6597541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 6, 3, 3].length) (baseStart_6597541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6597541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6597541 prefixEnd_6597541 := by exact prefixLift 6597541
  have htrace : WordTrace (prefixWord ++ tailWord_6597541) baseStart_6597541 baseEnd_6597541 := by
    simpa [prefixWord, tailWord_6597541, baseEnd_6597541] using wordTrace_append hprefix tailTrace_6597541
  have hstable : (prefixWord ++ tailWord_6597541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6597541).length < 2 ^ (prefixWord ++ tailWord_6597541).sum := by decide
  have hdescent : baseEnd_6597541 < baseStart_6597541 := by decide
  rcases family_descends (prefixWord ++ tailWord_6597541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6597565 : List Nat := [1, 4, 1, 2, 4, 1, 1, 4, 5]
def baseStart_6597565 : Nat := 118140960795 + 6597565 * 2 ^ 59
def prefixEnd_6597565 : Nat := 4983230072969 + 3 ^ 40 * 6597565 * 2
def baseEnd_6597565 : Nat := 376413554920064970032873

theorem tailTrace_6597565 : CollatzResearch.WordTrace tailWord_6597565 prefixEnd_6597565 376413554920064970032873 := by
  unfold tailWord_6597565
  simp only [CollatzResearch.WordTrace]
  refine ⟨240632964343156254240018149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160421976228770836160012099 240632964343156254240018149)
  ·
    refine ⟨45118680814341797670003403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 240632964343156254240018149 45118680814341797670003403)
    ·
      refine ⟨67678021221512696505005105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45118680814341797670003403 67678021221512696505005105)
      ·
        refine ⟨50758515916134522378753829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67678021221512696505005105 50758515916134522378753829)
        ·
          refine ⟨9517221734275222946016343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50758515916134522378753829 9517221734275222946016343)
          ·
            refine ⟨14275832601412834419024515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9517221734275222946016343 14275832601412834419024515)
            ·
              refine ⟨21413748902119251628536773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14275832601412834419024515 21413748902119251628536773)
              ·
                refine ⟨4015077919147359680350645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21413748902119251628536773 4015077919147359680350645)
                ·
                  refine ⟨376413554920064970032873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4015077919147359680350645 376413554920064970032873)
                  ·
                    rfl

theorem cell23_6597565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 4, 5].length) (baseStart_6597565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6597565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6597565 prefixEnd_6597565 := by exact prefixLift 6597565
  have htrace : WordTrace (prefixWord ++ tailWord_6597565) baseStart_6597565 baseEnd_6597565 := by
    simpa [prefixWord, tailWord_6597565, baseEnd_6597565] using wordTrace_append hprefix tailTrace_6597565
  have hstable : (prefixWord ++ tailWord_6597565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6597565).length < 2 ^ (prefixWord ++ tailWord_6597565).sum := by decide
  have hdescent : baseEnd_6597565 < baseStart_6597565 := by decide
  rcases family_descends (prefixWord ++ tailWord_6597565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6597568 : List Nat := [2, 1, 1, 2, 3, 3, 1, 1, 2, 5, 2]
def baseStart_6597568 : Nat := 118140960795 + 6597568 * 2 ^ 59
def prefixEnd_6597568 : Nat := 4983230072969 + 3 ^ 40 * 6597568 * 2
def baseEnd_6597568 : Nat := 3387723534722548218558343

theorem tailTrace_6597568 : CollatzResearch.WordTrace tailWord_6597568 prefixEnd_6597568 3387723534722548218558343 := by
  unfold tailWord_6597568
  simp only [CollatzResearch.WordTrace]
  refine ⟨120316536881072692876188679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160422049174763590501584905 120316536881072692876188679)
  ·
    refine ⟨180474805321609039314283019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120316536881072692876188679 180474805321609039314283019)
    ·
      refine ⟨270712207982413558971424529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180474805321609039314283019 270712207982413558971424529)
      ·
        refine ⟨203034155986810169228568397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270712207982413558971424529 203034155986810169228568397)
        ·
          refine ⟨76137808495053813460713149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 203034155986810169228568397 76137808495053813460713149)
          ·
            refine ⟨28551678185645180047767431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76137808495053813460713149 28551678185645180047767431)
            ·
              refine ⟨42827517278467770071651147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28551678185645180047767431 42827517278467770071651147)
              ·
                refine ⟨64241275917701655107476721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42827517278467770071651147 64241275917701655107476721)
                ·
                  refine ⟨48180956938276241330607541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64241275917701655107476721 48180956938276241330607541)
                  ·
                    refine ⟨4516964712963397624744457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48180956938276241330607541 4516964712963397624744457)
                    ·
                      refine ⟨3387723534722548218558343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4516964712963397624744457 3387723534722548218558343)
                      ·
                        rfl

theorem cell23_6597568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 2, 5, 2].length) (baseStart_6597568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6597568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6597568 prefixEnd_6597568 := by exact prefixLift 6597568
  have htrace : WordTrace (prefixWord ++ tailWord_6597568) baseStart_6597568 baseEnd_6597568 := by
    simpa [prefixWord, tailWord_6597568, baseEnd_6597568] using wordTrace_append hprefix tailTrace_6597568
  have hstable : (prefixWord ++ tailWord_6597568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6597568).length < 2 ^ (prefixWord ++ tailWord_6597568).sum := by decide
  have hdescent : baseEnd_6597568 < baseStart_6597568 := by decide
  rcases family_descends (prefixWord ++ tailWord_6597568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6597625 : List Nat := [1, 2, 1, 3, 1, 3, 1, 6, 1, 4]
def baseStart_6597625 : Nat := 118140960795 + 6597625 * 2 ^ 59
def prefixEnd_6597625 : Nat := 4983230072969 + 3 ^ 40 * 6597625 * 2
def baseEnd_6597625 : Nat := 1129250934373284831848527

theorem tailTrace_6597625 : CollatzResearch.WordTrace tailWord_6597625 prefixEnd_6597625 1129250934373284831848527 := by
  unfold tailWord_6597625
  simp only [CollatzResearch.WordTrace]
  refine ⟨240635152722938884487202329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160423435148625922991468219 240635152722938884487202329)
  ·
    refine ⟨180476364542204163365401747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240635152722938884487202329 180476364542204163365401747)
    ·
      refine ⟨270714546813306245048102621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180476364542204163365401747 270714546813306245048102621)
      ·
        refine ⟨101517955054989841893038483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 270714546813306245048102621 101517955054989841893038483)
        ·
          refine ⟨152276932582484762839557725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101517955054989841893038483 152276932582484762839557725)
          ·
            refine ⟨57103849718431786064834147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 152276932582484762839557725 57103849718431786064834147)
            ·
              refine ⟨85655774577647679097251221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57103849718431786064834147 85655774577647679097251221)
              ·
                refine ⟨4015114433327234957683651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 85655774577647679097251221 4015114433327234957683651)
                ·
                  refine ⟨6022671649990852436525477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4015114433327234957683651 6022671649990852436525477)
                  ·
                    refine ⟨1129250934373284831848527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6022671649990852436525477 1129250934373284831848527)
                    ·
                      rfl

theorem cell23_6597625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 6, 1, 4].length) (baseStart_6597625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6597625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6597625 prefixEnd_6597625 := by exact prefixLift 6597625
  have htrace : WordTrace (prefixWord ++ tailWord_6597625) baseStart_6597625 baseEnd_6597625 := by
    simpa [prefixWord, tailWord_6597625, baseEnd_6597625] using wordTrace_append hprefix tailTrace_6597625
  have hstable : (prefixWord ++ tailWord_6597625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6597625).length < 2 ^ (prefixWord ++ tailWord_6597625).sum := by decide
  have hdescent : baseEnd_6597625 < baseStart_6597625 := by decide
  rcases family_descends (prefixWord ++ tailWord_6597625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6597675 : List Nat := [1, 1, 1, 1, 2, 1, 7, 2, 2, 3, 2]
def baseStart_6597675 : Nat := 118140960795 + 6597675 * 2 ^ 59
def prefixEnd_6597675 : Nat := 4983230072969 + 3 ^ 40 * 6597675 * 2
def baseEnd_6597675 : Nat := 3387778477152579299920351

theorem tailTrace_6597675 : CollatzResearch.WordTrace tailWord_6597675 prefixEnd_6597675 3387778477152579299920351 := by
  unfold tailWord_6597675
  simp only [CollatzResearch.WordTrace]
  refine ⟨240636976372757743026522479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160424650915171828684348319 240636976372757743026522479)
  ·
    refine ⟨360955464559136614539783719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240636976372757743026522479 360955464559136614539783719)
    ·
      refine ⟨541433196838704921809675579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360955464559136614539783719 541433196838704921809675579)
      ·
        refine ⟨812149795258057382714513369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 541433196838704921809675579 812149795258057382714513369)
        ·
          refine ⟨609112346443543037035885027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 812149795258057382714513369 609112346443543037035885027)
          ·
            refine ⟨913668519665314555553827541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 609112346443543037035885027 913668519665314555553827541)
            ·
              refine ⟨21414105929655809895792833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 913668519665314555553827541 21414105929655809895792833)
              ·
                refine ⟨16060579447241857421844625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21414105929655809895792833 16060579447241857421844625)
                ·
                  refine ⟨12045434585431393066383469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16060579447241857421844625 12045434585431393066383469)
                  ·
                    refine ⟨4517037969536772399893801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12045434585431393066383469 4517037969536772399893801)
                    ·
                      refine ⟨3387778477152579299920351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4517037969536772399893801 3387778477152579299920351)
                      ·
                        rfl

theorem cell23_6597675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 2, 2, 3, 2].length) (baseStart_6597675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6597675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6597675 prefixEnd_6597675 := by exact prefixLift 6597675
  have htrace : WordTrace (prefixWord ++ tailWord_6597675) baseStart_6597675 baseEnd_6597675 := by
    simpa [prefixWord, tailWord_6597675, baseEnd_6597675] using wordTrace_append hprefix tailTrace_6597675
  have hstable : (prefixWord ++ tailWord_6597675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6597675).length < 2 ^ (prefixWord ++ tailWord_6597675).sum := by decide
  have hdescent : baseEnd_6597675 < baseStart_6597675 := by decide
  rcases family_descends (prefixWord ++ tailWord_6597675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6597702 : List Nat := [6, 1, 1, 1, 1, 3, 1, 1, 3, 5]
def baseStart_6597702 : Nat := 118140960795 + 6597702 * 2 ^ 59
def prefixEnd_6597702 : Nat := 4983230072969 + 3 ^ 40 * 6597702 * 2
def baseEnd_6597702 : Nat := 1129264113710083564760909

theorem tailTrace_6597702 : CollatzResearch.WordTrace tailWord_6597702 prefixEnd_6597702 1129264113710083564760909 := by
  unfold tailWord_6597702
  simp only [CollatzResearch.WordTrace]
  refine ⟨7519936285739372707429855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 160425307429106617758503573 7519936285739372707429855)
  ·
    refine ⟨11279904428609059061144783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7519936285739372707429855 11279904428609059061144783)
    ·
      refine ⟨16919856642913588591717175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11279904428609059061144783 16919856642913588591717175)
      ·
        refine ⟨25379784964370382887575763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16919856642913588591717175 25379784964370382887575763)
        ·
          refine ⟨38069677446555574331363645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25379784964370382887575763 38069677446555574331363645)
          ·
            refine ⟨14276129042458340374261367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38069677446555574331363645 14276129042458340374261367)
            ·
              refine ⟨21414193563687510561392051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14276129042458340374261367 21414193563687510561392051)
              ·
                refine ⟨32121290345531265842088077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21414193563687510561392051 32121290345531265842088077)
                ·
                  refine ⟨12045483879574224690783029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32121290345531265842088077 12045483879574224690783029)
                  ·
                    refine ⟨1129264113710083564760909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12045483879574224690783029 1129264113710083564760909)
                    ·
                      rfl

theorem cell23_6597702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_6597702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6597702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6597702 prefixEnd_6597702 := by exact prefixLift 6597702
  have htrace : WordTrace (prefixWord ++ tailWord_6597702) baseStart_6597702 baseEnd_6597702 := by
    simpa [prefixWord, tailWord_6597702, baseEnd_6597702] using wordTrace_append hprefix tailTrace_6597702
  have hstable : (prefixWord ++ tailWord_6597702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6597702).length < 2 ^ (prefixWord ++ tailWord_6597702).sum := by decide
  have hdescent : baseEnd_6597702 < baseStart_6597702 := by decide
  rcases family_descends (prefixWord ++ tailWord_6597702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6597709 : List Nat := [1, 6, 1, 1, 1, 3, 2, 1, 2, 3, 2]
def baseStart_6597709 : Nat := 118140960795 + 6597709 * 2 ^ 59
def prefixEnd_6597709 : Nat := 4983230072969 + 3 ^ 40 * 6597709 * 2
def baseEnd_6597709 : Nat := 3387795935494832166895195

theorem tailTrace_6597709 : CollatzResearch.WordTrace tailWord_6597709 prefixEnd_6597709 3387795935494832166895195 := by
  unfold tailWord_6597709
  simp only [CollatzResearch.WordTrace]
  refine ⟨240638216454634566833260181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160425477636423044555506787 240638216454634566833260181)
  ·
    refine ⟨11279916396310995320309071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 240638216454634566833260181 11279916396310995320309071)
    ·
      refine ⟨16919874594466492980463607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11279916396310995320309071 16919874594466492980463607)
      ·
        refine ⟨25379811891699739470695411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16919874594466492980463607 25379811891699739470695411)
        ·
          refine ⟨38069717837549609206043117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25379811891699739470695411 38069717837549609206043117)
          ·
            refine ⟨14276144189081103452266169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38069717837549609206043117 14276144189081103452266169)
            ·
              refine ⟨10707108141810827589199627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14276144189081103452266169 10707108141810827589199627)
              ·
                refine ⟨16060662212716241383799441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10707108141810827589199627 16060662212716241383799441)
                ·
                  refine ⟨12045496659537181037849581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16060662212716241383799441 12045496659537181037849581)
                  ·
                    refine ⟨4517061247326442889193593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12045496659537181037849581 4517061247326442889193593)
                    ·
                      refine ⟨3387795935494832166895195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4517061247326442889193593 3387795935494832166895195)
                      ·
                        rfl

theorem cell23_6597709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 1, 2, 3, 2].length) (baseStart_6597709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6597709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6597709 prefixEnd_6597709 := by exact prefixLift 6597709
  have htrace : WordTrace (prefixWord ++ tailWord_6597709) baseStart_6597709 baseEnd_6597709 := by
    simpa [prefixWord, tailWord_6597709, baseEnd_6597709] using wordTrace_append hprefix tailTrace_6597709
  have hstable : (prefixWord ++ tailWord_6597709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6597709).length < 2 ^ (prefixWord ++ tailWord_6597709).sum := by decide
  have hdescent : baseEnd_6597709 < baseStart_6597709 := by decide
  rcases family_descends (prefixWord ++ tailWord_6597709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6597726 : List Nat := [4, 4, 1, 1, 1, 1, 2, 2, 2, 3, 2]
def baseStart_6597726 : Nat := 118140960795 + 6597726 * 2 ^ 59
def prefixEnd_6597726 : Nat := 4983230072969 + 3 ^ 40 * 6597726 * 2
def baseEnd_6597726 : Nat := 3387804664665958600382617

theorem tailTrace_6597726 : CollatzResearch.WordTrace tailWord_6597726 prefixEnd_6597726 3387804664665958600382617 := by
  unfold tailWord_6597726
  simp only [CollatzResearch.WordTrace]
  refine ⟨30079854561946622342078629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160425890997048652491086021 30079854561946622342078629)
  ·
    refine ⟨5639972730364991689139743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30079854561946622342078629 5639972730364991689139743)
    ·
      refine ⟨8459959095547487533709615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5639972730364991689139743 8459959095547487533709615)
      ·
        refine ⟨12689938643321231300564423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8459959095547487533709615 12689938643321231300564423)
        ·
          refine ⟨19034907964981846950846635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12689938643321231300564423 19034907964981846950846635)
          ·
            refine ⟨28552361947472770426269953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19034907964981846950846635 28552361947472770426269953)
            ·
              refine ⟨21414271460604577819702465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28552361947472770426269953 21414271460604577819702465)
              ·
                refine ⟨16060703595453433364776849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21414271460604577819702465 16060703595453433364776849)
                ·
                  refine ⟨12045527696590075023582637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16060703595453433364776849 12045527696590075023582637)
                  ·
                    refine ⟨4517072886221278133843489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12045527696590075023582637 4517072886221278133843489)
                    ·
                      refine ⟨3387804664665958600382617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4517072886221278133843489 3387804664665958600382617)
                      ·
                        rfl

theorem cell23_6597726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_6597726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6597726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6597726 prefixEnd_6597726 := by exact prefixLift 6597726
  have htrace : WordTrace (prefixWord ++ tailWord_6597726) baseStart_6597726 baseEnd_6597726 := by
    simpa [prefixWord, tailWord_6597726, baseEnd_6597726] using wordTrace_append hprefix tailTrace_6597726
  have hstable : (prefixWord ++ tailWord_6597726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6597726).length < 2 ^ (prefixWord ++ tailWord_6597726).sum := by decide
  have hdescent : baseEnd_6597726 < baseStart_6597726 := by decide
  rcases family_descends (prefixWord ++ tailWord_6597726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6597795 : List Nat := [1, 1, 1, 4, 1, 1, 1, 4, 3, 4, 2]
def baseStart_6597795 : Nat := 118140960795 + 6597795 * 2 ^ 59
def prefixEnd_6597795 : Nat := 4983230072969 + 3 ^ 40 * 6597795 * 2
def baseEnd_6597795 : Nat := 3387840094831118830419799

theorem tailTrace_6597795 : CollatzResearch.WordTrace tailWord_6597795 prefixEnd_6597795 3387840094831118830419799 := by
  unfold tailWord_6597795
  simp only [CollatzResearch.WordTrace]
  refine ⟨240641353132323003520890839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160427568754882002347260559 240641353132323003520890839)
  ·
    refine ⟨360962029698484505281336259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240641353132323003520890839 360962029698484505281336259)
    ·
      refine ⟨541443044547726757922004389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360962029698484505281336259 541443044547726757922004389)
      ·
        refine ⟨101520570852698767110375823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 541443044547726757922004389 101520570852698767110375823)
        ·
          refine ⟨152280856279048150665563735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101520570852698767110375823 152280856279048150665563735)
          ·
            refine ⟨228421284418572225998345603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152280856279048150665563735 228421284418572225998345603)
            ·
              refine ⟨342631926627858338997518405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228421284418572225998345603 342631926627858338997518405)
              ·
                refine ⟨64243486242723438562034701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 342631926627858338997518405 64243486242723438562034701)
                ·
                  refine ⟨24091307341021289460763013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64243486242723438562034701 24091307341021289460763013)
                  ·
                    refine ⟨4517120126441491773893065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24091307341021289460763013 4517120126441491773893065)
                    ·
                      refine ⟨3387840094831118830419799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4517120126441491773893065 3387840094831118830419799)
                      ·
                        rfl

theorem cell23_6597795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 3, 4, 2].length) (baseStart_6597795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6597795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6597795 prefixEnd_6597795 := by exact prefixLift 6597795
  have htrace : WordTrace (prefixWord ++ tailWord_6597795) baseStart_6597795 baseEnd_6597795 := by
    simpa [prefixWord, tailWord_6597795, baseEnd_6597795] using wordTrace_append hprefix tailTrace_6597795
  have hstable : (prefixWord ++ tailWord_6597795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6597795).length < 2 ^ (prefixWord ++ tailWord_6597795).sum := by decide
  have hdescent : baseEnd_6597795 < baseStart_6597795 := by decide
  rcases family_descends (prefixWord ++ tailWord_6597795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6597835 : List Nat := [1, 1, 1, 1, 3, 2, 2, 7, 5]
def baseStart_6597835 : Nat := 118140960795 + 6597835 * 2 ^ 59
def prefixEnd_6597835 : Nat := 4983230072969 + 3 ^ 40 * 6597835 * 2
def baseEnd_6597835 : Nat := 376428959339699852657735

theorem tailTrace_6597835 : CollatzResearch.WordTrace tailWord_6597835 prefixEnd_6597835 376428959339699852657735 := by
  unfold tailWord_6597835
  simp only [CollatzResearch.WordTrace]
  refine ⟨240642812052178090352346959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160428541368118726901564639 240642812052178090352346959)
  ·
    refine ⟨360964218078267135528520439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240642812052178090352346959 360964218078267135528520439)
    ·
      refine ⟨541446327117400703292780659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360964218078267135528520439 541446327117400703292780659)
      ·
        refine ⟨812169490676101054939170989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 541446327117400703292780659 812169490676101054939170989)
        ·
          refine ⟨304563559003537895602189121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 812169490676101054939170989 304563559003537895602189121)
          ·
            refine ⟨228422669252653421701641841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 304563559003537895602189121 228422669252653421701641841)
            ·
              refine ⟨171317001939490066276231381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228422669252653421701641841 171317001939490066276231381)
              ·
                refine ⟨4015242232956798428349173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 171317001939490066276231381 4015242232956798428349173)
                ·
                  refine ⟨376428959339699852657735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4015242232956798428349173 376428959339699852657735)
                  ·
                    rfl

theorem cell23_6597835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 7, 5].length) (baseStart_6597835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6597835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6597835 prefixEnd_6597835 := by exact prefixLift 6597835
  have htrace : WordTrace (prefixWord ++ tailWord_6597835) baseStart_6597835 baseEnd_6597835 := by
    simpa [prefixWord, tailWord_6597835, baseEnd_6597835] using wordTrace_append hprefix tailTrace_6597835
  have hstable : (prefixWord ++ tailWord_6597835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6597835).length < 2 ^ (prefixWord ++ tailWord_6597835).sum := by decide
  have hdescent : baseEnd_6597835 < baseStart_6597835 := by decide
  rcases family_descends (prefixWord ++ tailWord_6597835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6597902 : List Nat := [4, 1, 1, 2, 1, 3, 2, 2, 2, 1, 4]
def baseStart_6597902 : Nat := 118140960795 + 6597902 * 2 ^ 59
def prefixEnd_6597902 : Nat := 4983230072969 + 3 ^ 40 * 6597902 * 2
def baseEnd_6597902 : Nat := 3387895037261149911781807

theorem tailTrace_6597902 : CollatzResearch.WordTrace tailWord_6597902 prefixEnd_6597902 3387895037261149911781807 := by
  unfold tailWord_6597902
  simp only [CollatzResearch.WordTrace]
  refine ⟨30080656967866920099379495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160430170495290240530023973 30080656967866920099379495)
  ·
    refine ⟨45120985451800380149069243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30080656967866920099379495 45120985451800380149069243)
    ·
      refine ⟨67681478177700570223603865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45120985451800380149069243 67681478177700570223603865)
      ·
        refine ⟨50761108633275427667702899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67681478177700570223603865 50761108633275427667702899)
        ·
          refine ⟨76141662949913141501554349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50761108633275427667702899 76141662949913141501554349)
          ·
            refine ⟨28553123606217428063082881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76141662949913141501554349 28553123606217428063082881)
            ·
              refine ⟨21414842704663071047312161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28553123606217428063082881 21414842704663071047312161)
              ·
                refine ⟨16061132028497303285484121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21414842704663071047312161 16061132028497303285484121)
                ·
                  refine ⟨12045849021372977464113091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16061132028497303285484121 12045849021372977464113091)
                  ·
                    refine ⟨18068773532059466196169637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12045849021372977464113091 18068773532059466196169637)
                    ·
                      refine ⟨3387895037261149911781807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18068773532059466196169637 3387895037261149911781807)
                      ·
                        rfl

theorem cell23_6597902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_6597902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6597902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6597902 prefixEnd_6597902 := by exact prefixLift 6597902
  have htrace : WordTrace (prefixWord ++ tailWord_6597902) baseStart_6597902 baseEnd_6597902 := by
    simpa [prefixWord, tailWord_6597902, baseEnd_6597902] using wordTrace_append hprefix tailTrace_6597902
  have hstable : (prefixWord ++ tailWord_6597902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6597902).length < 2 ^ (prefixWord ++ tailWord_6597902).sum := by decide
  have hdescent : baseEnd_6597902 < baseStart_6597902 := by decide
  rcases family_descends (prefixWord ++ tailWord_6597902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6597919 : List Nat := [1, 1, 2, 4, 4, 1, 1, 1, 2, 4, 2]
def baseStart_6597919 : Nat := 118140960795 + 6597919 * 2 ^ 59
def prefixEnd_6597919 : Nat := 4983230072969 + 3 ^ 40 * 6597919 * 2
def baseEnd_6597919 : Nat := 3387903766432276345269229

theorem tailTrace_6597919 : CollatzResearch.WordTrace tailWord_6597919 prefixEnd_6597919 3387903766432276345269229 := by
  unfold tailWord_6597919
  simp only [CollatzResearch.WordTrace]
  refine ⟨240645875783873772698404811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160430583855915848465603207 240645875783873772698404811)
  ·
    refine ⟨360968813675810659047607217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240645875783873772698404811 360968813675810659047607217)
    ·
      refine ⟨270726610256857994285705413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 360968813675810659047607217 270726610256857994285705413)
      ·
        refine ⟨50761239423160873928569765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 270726610256857994285705413 50761239423160873928569765)
        ·
          refine ⟨9517732391842663861606831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50761239423160873928569765 9517732391842663861606831)
          ·
            refine ⟨14276598587763995792410247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9517732391842663861606831 14276598587763995792410247)
            ·
              refine ⟨21414897881645993688615371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14276598587763995792410247 21414897881645993688615371)
              ·
                refine ⟨32122346822468990532923057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21414897881645993688615371 32122346822468990532923057)
                ·
                  refine ⟨24091760116851742899692293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32122346822468990532923057 24091760116851742899692293)
                  ·
                    refine ⟨4517205021909701793692305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24091760116851742899692293 4517205021909701793692305)
                    ·
                      refine ⟨3387903766432276345269229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4517205021909701793692305 3387903766432276345269229)
                      ·
                        rfl

theorem cell23_6597919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 1, 2, 4, 2].length) (baseStart_6597919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6597919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6597919 prefixEnd_6597919 := by exact prefixLift 6597919
  have htrace : WordTrace (prefixWord ++ tailWord_6597919) baseStart_6597919 baseEnd_6597919 := by
    simpa [prefixWord, tailWord_6597919, baseEnd_6597919] using wordTrace_append hprefix tailTrace_6597919
  have hstable : (prefixWord ++ tailWord_6597919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6597919).length < 2 ^ (prefixWord ++ tailWord_6597919).sum := by decide
  have hdescent : baseEnd_6597919 < baseStart_6597919 := by decide
  rcases family_descends (prefixWord ++ tailWord_6597919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6597939 : List Nat := [1, 1, 1, 2, 5, 4, 1, 1, 2, 2, 3]
def baseStart_6597939 : Nat := 118140960795 + 6597939 * 2 ^ 59
def prefixEnd_6597939 : Nat := 4983230072969 + 3 ^ 40 * 6597939 * 2
def baseEnd_6597939 : Nat := 3387914036045366267019137

theorem tailTrace_6597939 : CollatzResearch.WordTrace tailWord_6597939 prefixEnd_6597939 3387914036045366267019137 := by
  unfold tailWord_6597939
  simp only [CollatzResearch.WordTrace]
  refine ⟨240646605243801316114132871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160431070162534210742755247 240646605243801316114132871)
  ·
    refine ⟨360969907865701974171199307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240646605243801316114132871 360969907865701974171199307)
    ·
      refine ⟨541454861798552961256798961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360969907865701974171199307 541454861798552961256798961)
      ·
        refine ⟨406091146348914720942599221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 541454861798552961256798961 406091146348914720942599221)
        ·
          refine ⟨38071044970210755088368677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 406091146348914720942599221 38071044970210755088368677)
          ·
            refine ⟨7138320931914516579069127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38071044970210755088368677 7138320931914516579069127)
            ·
              refine ⟨10707481397871774868603691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7138320931914516579069127 10707481397871774868603691)
              ·
                refine ⟨16061222096807662302905537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10707481397871774868603691 16061222096807662302905537)
                ·
                  refine ⟨12045916572605746727179153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16061222096807662302905537 12045916572605746727179153)
                  ·
                    refine ⟨9034437429454310045384365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12045916572605746727179153 9034437429454310045384365)
                    ·
                      refine ⟨3387914036045366267019137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9034437429454310045384365 3387914036045366267019137)
                      ·
                        rfl

theorem cell23_6597939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 1, 2, 2, 3].length) (baseStart_6597939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6597939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6597939 prefixEnd_6597939 := by exact prefixLift 6597939
  have htrace : WordTrace (prefixWord ++ tailWord_6597939) baseStart_6597939 baseEnd_6597939 := by
    simpa [prefixWord, tailWord_6597939, baseEnd_6597939] using wordTrace_append hprefix tailTrace_6597939
  have hstable : (prefixWord ++ tailWord_6597939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6597939).length < 2 ^ (prefixWord ++ tailWord_6597939).sum := by decide
  have hdescent : baseEnd_6597939 < baseStart_6597939 := by decide
  rcases family_descends (prefixWord ++ tailWord_6597939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6597952 : List Nat := [2, 1, 1, 2, 2, 1, 3, 2, 5, 1, 3]
def baseStart_6597952 : Nat := 118140960795 + 6597952 * 2 ^ 59
def prefixEnd_6597952 : Nat := 4983230072969 + 3 ^ 40 * 6597952 * 2
def baseEnd_6597952 : Nat := 3387920711293874716156577

theorem tailTrace_6597952 : CollatzResearch.WordTrace tailWord_6597952 prefixEnd_6597952 3387920711293874716156577 := by
  unfold tailWord_6597952
  simp only [CollatzResearch.WordTrace]
  refine ⟨120323539696377109667178055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160431386261836146222904073 120323539696377109667178055)
  ·
    refine ⟨180485309544565664500767083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120323539696377109667178055 180485309544565664500767083)
    ·
      refine ⟨270727964316848496751150625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180485309544565664500767083 270727964316848496751150625)
      ·
        refine ⟨203045973237636372563362969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270727964316848496751150625 203045973237636372563362969)
        ·
          refine ⟨152284479928227279422522227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203045973237636372563362969 152284479928227279422522227)
          ·
            refine ⟨228426719892340919133783341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152284479928227279422522227 228426719892340919133783341)
            ·
              refine ⟨85660019959627844675168753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 228426719892340919133783341 85660019959627844675168753)
              ·
                refine ⟨64245014969720883506376565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85660019959627844675168753 64245014969720883506376565)
                ·
                  refine ⟨6022970153411332828722803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64245014969720883506376565 6022970153411332828722803)
                  ·
                    refine ⟨9034455230116999243084205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6022970153411332828722803 9034455230116999243084205)
                    ·
                      refine ⟨3387920711293874716156577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9034455230116999243084205 3387920711293874716156577)
                      ·
                        rfl

theorem cell23_6597952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 5, 1, 3].length) (baseStart_6597952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6597952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6597952 prefixEnd_6597952 := by exact prefixLift 6597952
  have htrace : WordTrace (prefixWord ++ tailWord_6597952) baseStart_6597952 baseEnd_6597952 := by
    simpa [prefixWord, tailWord_6597952, baseEnd_6597952] using wordTrace_append hprefix tailTrace_6597952
  have hstable : (prefixWord ++ tailWord_6597952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6597952).length < 2 ^ (prefixWord ++ tailWord_6597952).sum := by decide
  have hdescent : baseEnd_6597952 < baseStart_6597952 := by decide
  rcases family_descends (prefixWord ++ tailWord_6597952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6597969 : List Nat := [1, 2, 2, 1, 4, 1, 4, 1, 3, 1, 3]
def baseStart_6597969 : Nat := 118140960795 + 6597969 * 2 ^ 59
def prefixEnd_6597969 : Nat := 4983230072969 + 3 ^ 40 * 6597969 * 2
def baseEnd_6597969 : Nat := 3387929440465001149643999

theorem tailTrace_6597969 : CollatzResearch.WordTrace tailWord_6597969 prefixEnd_6597969 3387929440465001149643999 := by
  unfold tailWord_6597969
  simp only [CollatzResearch.WordTrace]
  refine ⟨240647699433692631237724961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160431799622461754158483307 240647699433692631237724961)
  ·
    refine ⟨180485774575269473428293721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240647699433692631237724961 180485774575269473428293721)
    ·
      refine ⟨135364330931452105071220291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180485774575269473428293721 135364330931452105071220291)
      ·
        refine ⟨203046496397178157606830437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135364330931452105071220291 203046496397178157606830437)
        ·
          refine ⟨38071218074470904551280707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 203046496397178157606830437 38071218074470904551280707)
          ·
            refine ⟨57106827111706356826921061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38071218074470904551280707 57106827111706356826921061)
            ·
              refine ⟨10707530083444941905047699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57106827111706356826921061 10707530083444941905047699)
              ·
                refine ⟨16061295125167412857571549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10707530083444941905047699 16061295125167412857571549)
                ·
                  refine ⟨6022985671937779821589331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16061295125167412857571549 6022985671937779821589331)
                  ·
                    refine ⟨9034478507906669732383997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6022985671937779821589331 9034478507906669732383997)
                    ·
                      refine ⟨3387929440465001149643999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9034478507906669732383997 3387929440465001149643999)
                      ·
                        rfl

theorem cell23_6597969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 1, 3, 1, 3].length) (baseStart_6597969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6597969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6597969 prefixEnd_6597969 := by exact prefixLift 6597969
  have htrace : WordTrace (prefixWord ++ tailWord_6597969) baseStart_6597969 baseEnd_6597969 := by
    simpa [prefixWord, tailWord_6597969, baseEnd_6597969] using wordTrace_append hprefix tailTrace_6597969
  have hstable : (prefixWord ++ tailWord_6597969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6597969).length < 2 ^ (prefixWord ++ tailWord_6597969).sum := by decide
  have hdescent : baseEnd_6597969 < baseStart_6597969 := by decide
  rcases family_descends (prefixWord ++ tailWord_6597969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6598002 : List Nat := [3, 2, 1, 2, 1, 2, 1, 1, 6, 4]
def baseStart_6598002 : Nat := 118140960795 + 6598002 * 2 ^ 59
def prefixEnd_6598002 : Nat := 4983230072969 + 3 ^ 40 * 6598002 * 2
def baseEnd_6598002 : Nat := 1129315461775533173510449

theorem tailTrace_6598002 : CollatzResearch.WordTrace tailWord_6598002 prefixEnd_6598002 1129315461775533173510449 := by
  unfold tailWord_6598002
  simp only [CollatzResearch.WordTrace]
  refine ⟨60162225760643269468419065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160432602028382051915784173 60162225760643269468419065)
  ·
    refine ⟨45121669320482452101314299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60162225760643269468419065 45121669320482452101314299)
    ·
      refine ⟨67682503980723678151971449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45121669320482452101314299 67682503980723678151971449)
      ·
        refine ⟨50761877985542758613978587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67682503980723678151971449 50761877985542758613978587)
        ·
          refine ⟨76142816978314137920967881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50761877985542758613978587 76142816978314137920967881)
          ·
            refine ⟨57107112733735603440725911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76142816978314137920967881 57107112733735603440725911)
            ·
              refine ⟨85660669100603405161088867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57107112733735603440725911 85660669100603405161088867)
              ·
                refine ⟨128491003650905107741633301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85660669100603405161088867 128491003650905107741633301)
                ·
                  refine ⟨6023015796136176925389061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 128491003650905107741633301 6023015796136176925389061)
                  ·
                    refine ⟨1129315461775533173510449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6023015796136176925389061 1129315461775533173510449)
                    ·
                      rfl

theorem cell23_6598002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 6, 4].length) (baseStart_6598002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6598002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6598002 prefixEnd_6598002 := by exact prefixLift 6598002
  have htrace : WordTrace (prefixWord ++ tailWord_6598002) baseStart_6598002 baseEnd_6598002 := by
    simpa [prefixWord, tailWord_6598002, baseEnd_6598002] using wordTrace_append hprefix tailTrace_6598002
  have hstable : (prefixWord ++ tailWord_6598002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6598002).length < 2 ^ (prefixWord ++ tailWord_6598002).sum := by decide
  have hdescent : baseEnd_6598002 < baseStart_6598002 := by decide
  rcases family_descends (prefixWord ++ tailWord_6598002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6598009 : List Nat := [1, 2, 1, 3, 2, 1, 2, 2, 5, 2, 2]
def baseStart_6598009 : Nat := 118140960795 + 6598009 * 2 ^ 59
def prefixEnd_6598009 : Nat := 4983230072969 + 3 ^ 40 * 6598009 * 2
def baseEnd_6598009 : Nat := 3387949979691180993143815

theorem tailTrace_6598009 : CollatzResearch.WordTrace tailWord_6598009 prefixEnd_6598009 3387949979691180993143815 := by
  unfold tailWord_6598009
  simp only [CollatzResearch.WordTrace]
  refine ⟨240649158353547718069181081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160432772235698478712787387 240649158353547718069181081)
  ·
    refine ⟨180486868765160788551885811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240649158353547718069181081 180486868765160788551885811)
    ·
      refine ⟨270730303147741182827828717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180486868765160788551885811 270730303147741182827828717)
      ·
        refine ⟨101523863680402943560435769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 270730303147741182827828717 101523863680402943560435769)
        ·
          refine ⟨76142897760302207670326827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101523863680402943560435769 76142897760302207670326827)
          ·
            refine ⟨114214346640453311505490241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76142897760302207670326827 114214346640453311505490241)
            ·
              refine ⟨85660759980339983629117681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114214346640453311505490241 85660759980339983629117681)
              ·
                refine ⟨64245569985254987721838261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85660759980339983629117681 64245569985254987721838261)
                ·
                  refine ⟨6023022186117655098922337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64245569985254987721838261 6023022186117655098922337)
                  ·
                    refine ⟨4517266639588241324191753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6023022186117655098922337 4517266639588241324191753)
                    ·
                      refine ⟨3387949979691180993143815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4517266639588241324191753 3387949979691180993143815)
                      ·
                        rfl

theorem cell23_6598009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 2, 5, 2, 2].length) (baseStart_6598009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6598009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6598009 prefixEnd_6598009 := by exact prefixLift 6598009
  have htrace : WordTrace (prefixWord ++ tailWord_6598009) baseStart_6598009 baseEnd_6598009 := by
    simpa [prefixWord, tailWord_6598009, baseEnd_6598009] using wordTrace_append hprefix tailTrace_6598009
  have hstable : (prefixWord ++ tailWord_6598009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6598009).length < 2 ^ (prefixWord ++ tailWord_6598009).sum := by decide
  have hdescent : baseEnd_6598009 < baseStart_6598009 := by decide
  rcases family_descends (prefixWord ++ tailWord_6598009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6598012 : List Nat := [2, 2, 2, 1, 1, 1, 6, 1, 1, 1, 5]
def baseStart_6598012 : Nat := 118140960795 + 6598012 * 2 ^ 59
def prefixEnd_6598012 : Nat := 4983230072969 + 3 ^ 40 * 6598012 * 2
def baseEnd_6598012 : Nat := 3387951520133144481406301

theorem tailTrace_6598012 : CollatzResearch.WordTrace tailWord_6598012 prefixEnd_6598012 3387951520133144481406301 := by
  unfold tailWord_6598012
  simp only [CollatzResearch.WordTrace]
  refine ⟨120324633886268424790770145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160432845181691233054360193 120324633886268424790770145)
  ·
    refine ⟨90243475414701318593077609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120324633886268424790770145 90243475414701318593077609)
    ·
      refine ⟨67682606561025988944808207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90243475414701318593077609 67682606561025988944808207)
      ·
        refine ⟨101523909841538983417212311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67682606561025988944808207 101523909841538983417212311)
        ·
          refine ⟨152285864762308475125818467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101523909841538983417212311 152285864762308475125818467)
          ·
            refine ⟨228428797143462712688727701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152285864762308475125818467 228428797143462712688727701)
            ·
              refine ⟨10707599866099814657284111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 228428797143462712688727701 10707599866099814657284111)
              ·
                refine ⟨16061399799149721985926167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10707599866099814657284111 16061399799149721985926167)
                ·
                  refine ⟨24092099698724582978889251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16061399799149721985926167 24092099698724582978889251)
                  ·
                    refine ⟨36138149548086874468333877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24092099698724582978889251 36138149548086874468333877)
                    ·
                      refine ⟨3387951520133144481406301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36138149548086874468333877 3387951520133144481406301)
                      ·
                        rfl

theorem cell23_6598012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 1, 1, 1, 5].length) (baseStart_6598012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6598012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6598012 prefixEnd_6598012 := by exact prefixLift 6598012
  have htrace : WordTrace (prefixWord ++ tailWord_6598012) baseStart_6598012 baseEnd_6598012 := by
    simpa [prefixWord, tailWord_6598012, baseEnd_6598012] using wordTrace_append hprefix tailTrace_6598012
  have hstable : (prefixWord ++ tailWord_6598012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6598012).length < 2 ^ (prefixWord ++ tailWord_6598012).sum := by decide
  have hdescent : baseEnd_6598012 < baseStart_6598012 := by decide
  rcases family_descends (prefixWord ++ tailWord_6598012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6598036 : List Nat := [2, 4, 2, 1, 2, 2, 1, 3, 2, 4]
def baseStart_6598036 : Nat := 118140960795 + 6598036 * 2 ^ 59
def prefixEnd_6598036 : Nat := 4983230072969 + 3 ^ 40 * 6598036 * 2
def baseEnd_6598036 : Nat := 1129321281222950795835397

theorem tailTrace_6598036 : CollatzResearch.WordTrace tailWord_6598036 prefixEnd_6598036 1129321281222950795835397 := by
  unfold tailWord_6598036
  simp only [CollatzResearch.WordTrace]
  refine ⟨120325071562224950840206981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160433428749633267786942641 120325071562224950840206981)
  ·
    refine ⟨22560950917917178282538809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120325071562224950840206981 22560950917917178282538809)
    ·
      refine ⟨16920713188437883711904107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22560950917917178282538809 16920713188437883711904107)
      ·
        refine ⟨25381069782656825567856161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16920713188437883711904107 25381069782656825567856161)
        ·
          refine ⟨19035802336992619175892121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25381069782656825567856161 19035802336992619175892121)
          ·
            refine ⟨14276851752744464381919091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19035802336992619175892121 14276851752744464381919091)
            ·
              refine ⟨21415277629116696572878637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14276851752744464381919091 21415277629116696572878637)
              ·
                refine ⟨8030729110918761214829489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21415277629116696572878637 8030729110918761214829489)
                ·
                  refine ⟨6023046833189070911122117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8030729110918761214829489 6023046833189070911122117)
                  ·
                    refine ⟨1129321281222950795835397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6023046833189070911122117 1129321281222950795835397)
                    ·
                      rfl

theorem cell23_6598036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_6598036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6598036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6598036 prefixEnd_6598036 := by exact prefixLift 6598036
  have htrace : WordTrace (prefixWord ++ tailWord_6598036) baseStart_6598036 baseEnd_6598036 := by
    simpa [prefixWord, tailWord_6598036, baseEnd_6598036] using wordTrace_append hprefix tailTrace_6598036
  have hstable : (prefixWord ++ tailWord_6598036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6598036).length < 2 ^ (prefixWord ++ tailWord_6598036).sum := by decide
  have hdescent : baseEnd_6598036 < baseStart_6598036 := by decide
  rcases family_descends (prefixWord ++ tailWord_6598036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6598056 : List Nat := [2, 1, 6, 1, 2, 1, 1, 2, 1, 2, 4]
def baseStart_6598056 : Nat := 118140960795 + 6598056 * 2 ^ 59
def prefixEnd_6598056 : Nat := 4983230072969 + 3 ^ 40 * 6598056 * 2
def baseEnd_6598056 : Nat := 3387974113281942309256099

theorem tailTrace_6598056 : CollatzResearch.WordTrace tailWord_6598056 prefixEnd_6598056 3387974113281942309256099 := by
  unfold tailWord_6598056
  simp only [CollatzResearch.WordTrace]
  refine ⟨120325436292188722548071011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160433915056251630064094681 120325436292188722548071011)
  ·
    refine ⟨180488154438283083822106517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120325436292188722548071011 180488154438283083822106517)
    ·
      refine ⟨8460382239294519554161243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 180488154438283083822106517 8460382239294519554161243)
      ·
        refine ⟨12690573358941779331241865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8460382239294519554161243 12690573358941779331241865)
        ·
          refine ⟨9517930019206334498431399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12690573358941779331241865 9517930019206334498431399)
          ·
            refine ⟨14276895028809501747647099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9517930019206334498431399 14276895028809501747647099)
            ·
              refine ⟨21415342543214252621470649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14276895028809501747647099 21415342543214252621470649)
              ·
                refine ⟨16061506907410689466102987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21415342543214252621470649 16061506907410689466102987)
                ·
                  refine ⟨24092260361116034199154481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16061506907410689466102987 24092260361116034199154481)
                  ·
                    refine ⟨18069195270837025649365861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24092260361116034199154481 18069195270837025649365861)
                    ·
                      refine ⟨3387974113281942309256099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18069195270837025649365861 3387974113281942309256099)
                      ·
                        rfl

theorem cell23_6598056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_6598056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6598056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6598056 prefixEnd_6598056 := by exact prefixLift 6598056
  have htrace : WordTrace (prefixWord ++ tailWord_6598056) baseStart_6598056 baseEnd_6598056 := by
    simpa [prefixWord, tailWord_6598056, baseEnd_6598056] using wordTrace_append hprefix tailTrace_6598056
  have hstable : (prefixWord ++ tailWord_6598056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6598056).length < 2 ^ (prefixWord ++ tailWord_6598056).sum := by decide
  have hdescent : baseEnd_6598056 < baseStart_6598056 := by decide
  rcases family_descends (prefixWord ++ tailWord_6598056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6598092 : List Nat := [2, 2, 1, 4, 2, 1, 1, 1, 1, 8]
def baseStart_6598092 : Nat := 118140960795 + 6598092 * 2 ^ 59
def prefixEnd_6598092 : Nat := 4983230072969 + 3 ^ 40 * 6598092 * 2
def baseEnd_6598092 : Nat := 1129330866195168056135311

theorem tailTrace_6598092 : CollatzResearch.WordTrace tailWord_6598092 prefixEnd_6598092 1129330866195168056135311 := by
  unfold tailWord_6598092
  simp only [CollatzResearch.WordTrace]
  refine ⟨120326092806123511622226265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160434790408164682162968353 120326092806123511622226265)
  ·
    refine ⟨90244569604592633716669699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120326092806123511622226265 90244569604592633716669699)
    ·
      refine ⟨135366854406888950575004549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90244569604592633716669699 135366854406888950575004549)
      ·
        refine ⟨25381285201291678232813353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135366854406888950575004549 25381285201291678232813353)
        ·
          refine ⟨19035963900968758674610015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25381285201291678232813353 19035963900968758674610015)
          ·
            refine ⟨28553945851453138011915023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19035963900968758674610015 28553945851453138011915023)
            ·
              refine ⟨42830918777179707017872535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28553945851453138011915023 42830918777179707017872535)
              ·
                refine ⟨64246378165769560526808803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42830918777179707017872535 64246378165769560526808803)
                ·
                  refine ⟨96369567248654340790213205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64246378165769560526808803 96369567248654340790213205)
                  ·
                    refine ⟨1129330866195168056135311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 96369567248654340790213205 1129330866195168056135311)
                    ·
                      rfl

theorem cell23_6598092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 1, 8].length) (baseStart_6598092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6598092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6598092 prefixEnd_6598092 := by exact prefixLift 6598092
  have htrace : WordTrace (prefixWord ++ tailWord_6598092) baseStart_6598092 baseEnd_6598092 := by
    simpa [prefixWord, tailWord_6598092, baseEnd_6598092] using wordTrace_append hprefix tailTrace_6598092
  have hstable : (prefixWord ++ tailWord_6598092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6598092).length < 2 ^ (prefixWord ++ tailWord_6598092).sum := by decide
  have hdescent : baseEnd_6598092 < baseStart_6598092 := by decide
  rcases family_descends (prefixWord ++ tailWord_6598092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
