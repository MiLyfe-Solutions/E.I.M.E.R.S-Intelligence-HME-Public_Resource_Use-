import V185TrunkScan23Chunk1153

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6835629 : List Nat := [1, 5, 2, 2, 1, 1, 3, 3, 1, 1, 3]
def baseStart_6835629 : Nat := 118140960795 + 6835629 * 2 ^ 59
def prefixEnd_6835629 : Nat := 4983230072969 + 3 ^ 40 * 6835629 * 2
def baseEnd_6835629 : Nat := 3509963252812541303801021

theorem tailTrace_6835629 : CollatzResearch.WordTrace tailWord_6835629 prefixEnd_6835629 3509963252812541303801021 := by
  unfold tailWord_6835629
  simp only [CollatzResearch.WordTrace]
  refine ⟨249315871752691040334261941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166210581168460693556174627 249315871752691040334261941)
  ·
    refine ⟨23373362976814785031337057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 249315871752691040334261941 23373362976814785031337057)
    ·
      refine ⟨17530022232611088773502793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23373362976814785031337057 17530022232611088773502793)
      ·
        refine ⟨13147516674458316580127095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17530022232611088773502793 13147516674458316580127095)
        ·
          refine ⟨19721275011687474870190643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13147516674458316580127095 19721275011687474870190643)
          ·
            refine ⟨29581912517531212305285965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19721275011687474870190643 29581912517531212305285965)
            ·
              refine ⟨11093217194074204614482237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29581912517531212305285965 11093217194074204614482237)
              ·
                refine ⟨4159956447777826730430839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11093217194074204614482237 4159956447777826730430839)
                ·
                  refine ⟨6239934671666740095646259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4159956447777826730430839 6239934671666740095646259)
                  ·
                    refine ⟨9359902007500110143469389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6239934671666740095646259 9359902007500110143469389)
                    ·
                      refine ⟨3509963252812541303801021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9359902007500110143469389 3509963252812541303801021)
                      ·
                        rfl

theorem cell23_6835629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_6835629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6835629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6835629 prefixEnd_6835629 := by exact prefixLift 6835629
  have htrace : WordTrace (prefixWord ++ tailWord_6835629) baseStart_6835629 baseEnd_6835629 := by
    simpa [prefixWord, tailWord_6835629, baseEnd_6835629] using wordTrace_append hprefix tailTrace_6835629
  have hstable : (prefixWord ++ tailWord_6835629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6835629).length < 2 ^ (prefixWord ++ tailWord_6835629).sum := by decide
  have hdescent : baseEnd_6835629 < baseStart_6835629 := by decide
  rcases family_descends (prefixWord ++ tailWord_6835629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6835631 : List Nat := [1, 1, 2, 1, 2, 2, 1, 6, 1, 2, 4]
def baseStart_6835631 : Nat := 118140960795 + 6835631 * 2 ^ 59
def prefixEnd_6835631 : Nat := 4983230072969 + 3 ^ 40 * 6835631 * 2
def baseEnd_6835631 : Nat := 3509964279773850295976011

theorem tailTrace_6835631 : CollatzResearch.WordTrace tailWord_6835631 prefixEnd_6835631 3509964279773850295976011 := by
  unfold tailWord_6835631
  simp only [CollatzResearch.WordTrace]
  refine ⟨249315944698683794675834747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166210629799122529783889831 249315944698683794675834747)
  ·
    refine ⟨373973917048025692013752121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249315944698683794675834747 373973917048025692013752121)
    ·
      refine ⟨280480437786019269010314091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 373973917048025692013752121 280480437786019269010314091)
      ·
        refine ⟨420720656679028903515471137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280480437786019269010314091 420720656679028903515471137)
        ·
          refine ⟨315540492509271677636603353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 420720656679028903515471137 315540492509271677636603353)
          ·
            refine ⟨236655369381953758227452515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 315540492509271677636603353 236655369381953758227452515)
            ·
              refine ⟨354983054072930637341178773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 236655369381953758227452515 354983054072930637341178773)
              ·
                refine ⟨16639830659668623625367755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 354983054072930637341178773 16639830659668623625367755)
                ·
                  refine ⟨24959745989502935438051633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16639830659668623625367755 24959745989502935438051633)
                  ·
                    refine ⟨18719809492127201578538725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24959745989502935438051633 18719809492127201578538725)
                    ·
                      refine ⟨3509964279773850295976011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18719809492127201578538725 3509964279773850295976011)
                      ·
                        rfl

theorem cell23_6835631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 6, 1, 2, 4].length) (baseStart_6835631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6835631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6835631 prefixEnd_6835631 := by exact prefixLift 6835631
  have htrace : WordTrace (prefixWord ++ tailWord_6835631) baseStart_6835631 baseEnd_6835631 := by
    simpa [prefixWord, tailWord_6835631, baseEnd_6835631] using wordTrace_append hprefix tailTrace_6835631
  have hstable : (prefixWord ++ tailWord_6835631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6835631).length < 2 ^ (prefixWord ++ tailWord_6835631).sum := by decide
  have hdescent : baseEnd_6835631 < baseStart_6835631 := by decide
  rcases family_descends (prefixWord ++ tailWord_6835631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6835685 : List Nat := [1, 3, 1, 5, 1, 2, 1, 2, 1, 3, 3]
def baseStart_6835685 : Nat := 118140960795 + 6835685 * 2 ^ 59
def prefixEnd_6835685 : Nat := 4983230072969 + 3 ^ 40 * 6835685 * 2
def baseEnd_6835685 : Nat := 3509992007729193084700763

theorem tailTrace_6835685 : CollatzResearch.WordTrace tailWord_6835685 prefixEnd_6835685 3509992007729193084700763 := by
  unfold tailWord_6835685
  simp only [CollatzResearch.WordTrace]
  refine ⟨249317914240488161898300509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166211942826992107932200339 249317914240488161898300509)
  ·
    refine ⟨93494217840183060711862691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249317914240488161898300509 93494217840183060711862691)
    ·
      refine ⟨140241326760274591067794037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93494217840183060711862691 140241326760274591067794037)
      ·
        refine ⟨13147624383775742912605691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 140241326760274591067794037 13147624383775742912605691)
        ·
          refine ⟨19721436575663614368908537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13147624383775742912605691 19721436575663614368908537)
          ·
            refine ⟨14791077431747710776681403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19721436575663614368908537 14791077431747710776681403)
            ·
              refine ⟨22186616147621566165022105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14791077431747710776681403 22186616147621566165022105)
              ·
                refine ⟨16639962110716174623766579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22186616147621566165022105 16639962110716174623766579)
                ·
                  refine ⟨24959943166074261935649869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16639962110716174623766579 24959943166074261935649869)
                  ·
                    refine ⟨9359978687277848225868701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24959943166074261935649869 9359978687277848225868701)
                    ·
                      refine ⟨3509992007729193084700763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9359978687277848225868701 3509992007729193084700763)
                      ·
                        rfl

theorem cell23_6835685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_6835685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6835685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6835685 prefixEnd_6835685 := by exact prefixLift 6835685
  have htrace : WordTrace (prefixWord ++ tailWord_6835685) baseStart_6835685 baseEnd_6835685 := by
    simpa [prefixWord, tailWord_6835685, baseEnd_6835685] using wordTrace_append hprefix tailTrace_6835685
  have hstable : (prefixWord ++ tailWord_6835685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6835685).length < 2 ^ (prefixWord ++ tailWord_6835685).sum := by decide
  have hdescent : baseEnd_6835685 < baseStart_6835685 := by decide
  rcases family_descends (prefixWord ++ tailWord_6835685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6835695 : List Nat := [1, 1, 2, 1, 4, 1, 2, 5, 1, 3, 2]
def baseStart_6835695 : Nat := 118140960795 + 6835695 * 2 ^ 59
def prefixEnd_6835695 : Nat := 4983230072969 + 3 ^ 40 * 6835695 * 2
def baseEnd_6835695 : Nat := 3509997142535738045575717

theorem tailTrace_6835695 : CollatzResearch.WordTrace tailWord_6835695 prefixEnd_6835695 3509997142535738045575717 := by
  unfold tailWord_6835695
  simp only [CollatzResearch.WordTrace]
  refine ⟨249318278970451933606164539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166212185980301289070776359 249318278970451933606164539)
  ·
    refine ⟨373977418455677900409246809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249318278970451933606164539 373977418455677900409246809)
    ·
      refine ⟨280483063841758425306935107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 373977418455677900409246809 280483063841758425306935107)
      ·
        refine ⟨420724595762637637960402661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280483063841758425306935107 420724595762637637960402661)
        ·
          refine ⟨78885861705494557117575499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 420724595762637637960402661 78885861705494557117575499)
          ·
            refine ⟨118328792558241835676363249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78885861705494557117575499 118328792558241835676363249)
            ·
              refine ⟨88746594418681376757272437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118328792558241835676363249 88746594418681376757272437)
              ·
                refine ⟨8319993226751379070994291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 88746594418681376757272437 8319993226751379070994291)
                ·
                  refine ⟨12479989840127068606491437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8319993226751379070994291 12479989840127068606491437)
                  ·
                    refine ⟨4679996190047650727434289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12479989840127068606491437 4679996190047650727434289)
                    ·
                      refine ⟨3509997142535738045575717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4679996190047650727434289 3509997142535738045575717)
                      ·
                        rfl

theorem cell23_6835695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 5, 1, 3, 2].length) (baseStart_6835695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6835695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6835695 prefixEnd_6835695 := by exact prefixLift 6835695
  have htrace : WordTrace (prefixWord ++ tailWord_6835695) baseStart_6835695 baseEnd_6835695 := by
    simpa [prefixWord, tailWord_6835695, baseEnd_6835695] using wordTrace_append hprefix tailTrace_6835695
  have hstable : (prefixWord ++ tailWord_6835695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6835695).length < 2 ^ (prefixWord ++ tailWord_6835695).sum := by decide
  have hdescent : baseEnd_6835695 < baseStart_6835695 := by decide
  rcases family_descends (prefixWord ++ tailWord_6835695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6835702 : List Nat := [5, 1, 1, 1, 2, 2, 1, 4, 2, 1, 3]
def baseStart_6835702 : Nat := 118140960795 + 6835702 * 2 ^ 59
def prefixEnd_6835702 : Nat := 4983230072969 + 3 ^ 40 * 6835702 * 2
def baseEnd_6835702 : Nat := 3510000736900319518188185

theorem tailTrace_6835702 : CollatzResearch.WordTrace tailWord_6835702 prefixEnd_6835702 3510000736900319518188185 := by
  unfold tailWord_6835702
  simp only [CollatzResearch.WordTrace]
  refine ⟨15582408392589160862604335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 166212356187617715867779573 15582408392589160862604335)
  ·
    refine ⟨23373612588883741293906503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15582408392589160862604335 23373612588883741293906503)
    ·
      refine ⟨35060418883325611940859755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23373612588883741293906503 35060418883325611940859755)
      ·
        refine ⟨52590628324988417911289633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35060418883325611940859755 52590628324988417911289633)
        ·
          refine ⟨39442971243741313433467225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52590628324988417911289633 39442971243741313433467225)
          ·
            refine ⟨29582228432805985075100419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39442971243741313433467225 29582228432805985075100419)
            ·
              refine ⟨44373342649208977612650629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29582228432805985075100419 44373342649208977612650629)
              ·
                refine ⟨8320001746726683302371993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44373342649208977612650629 8320001746726683302371993)
                ·
                  refine ⟨6240001310045012476778995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8320001746726683302371993 6240001310045012476778995)
                  ·
                    refine ⟨9360001965067518715168493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6240001310045012476778995 9360001965067518715168493)
                    ·
                      refine ⟨3510000736900319518188185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9360001965067518715168493 3510000736900319518188185)
                      ·
                        rfl

theorem cell23_6835702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 4, 2, 1, 3].length) (baseStart_6835702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6835702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6835702 prefixEnd_6835702 := by exact prefixLift 6835702
  have htrace : WordTrace (prefixWord ++ tailWord_6835702) baseStart_6835702 baseEnd_6835702 := by
    simpa [prefixWord, tailWord_6835702, baseEnd_6835702] using wordTrace_append hprefix tailTrace_6835702
  have hstable : (prefixWord ++ tailWord_6835702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6835702).length < 2 ^ (prefixWord ++ tailWord_6835702).sum := by decide
  have hdescent : baseEnd_6835702 < baseStart_6835702 := by decide
  rcases family_descends (prefixWord ++ tailWord_6835702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6835711 : List Nat := [1, 1, 2, 2, 1, 2, 2, 2, 4, 1, 5]
def baseStart_6835711 : Nat := 118140960795 + 6835711 * 2 ^ 59
def prefixEnd_6835711 : Nat := 4983230072969 + 3 ^ 40 * 6835711 * 2
def baseEnd_6835711 : Nat := 3510005358226209982975643

theorem tailTrace_6835711 : CollatzResearch.WordTrace tailWord_6835711 prefixEnd_6835711 3510005358226209982975643 := by
  unfold tailWord_6835711
  simp only [CollatzResearch.WordTrace]
  refine ⟨249318862538393968338746987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166212575025595978892497991 249318862538393968338746987)
  ·
    refine ⟨373978293807590952508120481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249318862538393968338746987 373978293807590952508120481)
    ·
      refine ⟨280483720355693214381090361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 373978293807590952508120481 280483720355693214381090361)
      ·
        refine ⟨210362790266769910785817771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280483720355693214381090361 210362790266769910785817771)
        ·
          refine ⟨315544185400154866178726657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210362790266769910785817771 315544185400154866178726657)
          ·
            refine ⟨236658139050116149634044993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 315544185400154866178726657 236658139050116149634044993)
            ·
              refine ⟨177493604287587112225533745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 236658139050116149634044993 177493604287587112225533745)
              ·
                refine ⟨133120203215690334169150309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 177493604287587112225533745 133120203215690334169150309)
                ·
                  refine ⟨24960038102941937656715683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 133120203215690334169150309 24960038102941937656715683)
                  ·
                    refine ⟨37440057154412906485073525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24960038102941937656715683 37440057154412906485073525)
                    ·
                      refine ⟨3510005358226209982975643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37440057154412906485073525 3510005358226209982975643)
                      ·
                        rfl

theorem cell23_6835711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 4, 1, 5].length) (baseStart_6835711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6835711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6835711 prefixEnd_6835711 := by exact prefixLift 6835711
  have htrace : WordTrace (prefixWord ++ tailWord_6835711) baseStart_6835711 baseEnd_6835711 := by
    simpa [prefixWord, tailWord_6835711, baseEnd_6835711] using wordTrace_append hprefix tailTrace_6835711
  have hstable : (prefixWord ++ tailWord_6835711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6835711).length < 2 ^ (prefixWord ++ tailWord_6835711).sum := by decide
  have hdescent : baseEnd_6835711 < baseStart_6835711 := by decide
  rcases family_descends (prefixWord ++ tailWord_6835711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6835731 : List Nat := [1, 1, 1, 2, 1, 6, 1, 1, 9]
def baseStart_6835731 : Nat := 118140960795 + 6835731 * 2 ^ 59
def prefixEnd_6835731 : Nat := 4983230072969 + 3 ^ 40 * 6835731 * 2
def baseEnd_6835731 : Nat := 390001736426588878302839

theorem tailTrace_6835731 : CollatzResearch.WordTrace tailWord_6835731 prefixEnd_6835731 390001736426588878302839 := by
  unfold tailWord_6835731
  simp only [CollatzResearch.WordTrace]
  refine ⟨249319591998321511754475047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166213061332214341169650031 249319591998321511754475047)
  ·
    refine ⟨373979387997482267631712571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249319591998321511754475047 373979387997482267631712571)
    ·
      refine ⟨560969081996223401447568857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373979387997482267631712571 560969081996223401447568857)
      ·
        refine ⟨420726811497167551085676643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 560969081996223401447568857 420726811497167551085676643)
        ·
          refine ⟨631090217245751326628514965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 420726811497167551085676643 631090217245751326628514965)
          ·
            refine ⟨29582353933394593435711639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 631090217245751326628514965 29582353933394593435711639)
            ·
              refine ⟨44373530900091890153567459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29582353933394593435711639 44373530900091890153567459)
              ·
                refine ⟨66560296350137835230351189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44373530900091890153567459 66560296350137835230351189)
                ·
                  refine ⟨390001736426588878302839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 66560296350137835230351189 390001736426588878302839)
                  ·
                    rfl

theorem cell23_6835731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 9].length) (baseStart_6835731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6835731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6835731 prefixEnd_6835731 := by exact prefixLift 6835731
  have htrace : WordTrace (prefixWord ++ tailWord_6835731) baseStart_6835731 baseEnd_6835731 := by
    simpa [prefixWord, tailWord_6835731, baseEnd_6835731] using wordTrace_append hprefix tailTrace_6835731
  have hstable : (prefixWord ++ tailWord_6835731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6835731).length < 2 ^ (prefixWord ++ tailWord_6835731).sum := by decide
  have hdescent : baseEnd_6835731 < baseStart_6835731 := by decide
  rcases family_descends (prefixWord ++ tailWord_6835731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6835765 : List Nat := [1, 3, 3, 1, 1, 3, 2, 4, 5]
def baseStart_6835765 : Nat := 118140960795 + 6835765 * 2 ^ 59
def prefixEnd_6835765 : Nat := 4983230072969 + 3 ^ 40 * 6835765 * 2
def baseEnd_6835765 : Nat := 390003676242394752411155

theorem tailTrace_6835765 : CollatzResearch.WordTrace tailWord_6835765 prefixEnd_6835765 390003676242394752411155 := by
  unfold tailWord_6835765
  simp only [CollatzResearch.WordTrace]
  refine ⟨249320832080198335561212749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166213888053465557040808499 249320832080198335561212749)
  ·
    refine ⟨93495312030074375835454781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249320832080198335561212749 93495312030074375835454781)
    ·
      refine ⟨35060742011277890938295543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93495312030074375835454781 35060742011277890938295543)
      ·
        refine ⟨52591113016916836407443315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35060742011277890938295543 52591113016916836407443315)
        ·
          refine ⟨78886669525375254611164973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52591113016916836407443315 78886669525375254611164973)
          ·
            refine ⟨29582501072015720479186865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78886669525375254611164973 29582501072015720479186865)
            ·
              refine ⟨22186875804011790359390149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29582501072015720479186865 22186875804011790359390149)
              ·
                refine ⟨4160039213252210692385653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22186875804011790359390149 4160039213252210692385653)
                ·
                  refine ⟨390003676242394752411155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4160039213252210692385653 390003676242394752411155)
                  ·
                    rfl

theorem cell23_6835765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 4, 5].length) (baseStart_6835765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6835765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6835765 prefixEnd_6835765 := by exact prefixLift 6835765
  have htrace : WordTrace (prefixWord ++ tailWord_6835765) baseStart_6835765 baseEnd_6835765 := by
    simpa [prefixWord, tailWord_6835765, baseEnd_6835765] using wordTrace_append hprefix tailTrace_6835765
  have hstable : (prefixWord ++ tailWord_6835765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6835765).length < 2 ^ (prefixWord ++ tailWord_6835765).sum := by decide
  have hdescent : baseEnd_6835765 < baseStart_6835765 := by decide
  rcases family_descends (prefixWord ++ tailWord_6835765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6835791 : List Nat := [1, 1, 2, 1, 1, 2, 3, 1, 1, 10]
def baseStart_6835791 : Nat := 118140960795 + 6835791 * 2 ^ 59
def prefixEnd_6835791 : Nat := 4983230072969 + 3 ^ 40 * 6835791 * 2
def baseEnd_6835791 : Nat := 1170015478892856556658425

theorem tailTrace_6835791 : CollatzResearch.WordTrace tailWord_6835791 prefixEnd_6835791 1170015478892856556658425 := by
  unfold tailWord_6835791
  simp only [CollatzResearch.WordTrace]
  refine ⟨249321780378104142001659227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166214520252069428001106151 249321780378104142001659227)
  ·
    refine ⟨373982670567156213002488841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249321780378104142001659227 373982670567156213002488841)
    ·
      refine ⟨280487002925367159751866631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 373982670567156213002488841 280487002925367159751866631)
      ·
        refine ⟨420730504388050739627799947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280487002925367159751866631 420730504388050739627799947)
        ·
          refine ⟨631095756582076109441699921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 420730504388050739627799947 631095756582076109441699921)
          ·
            refine ⟨473321817436557082081274941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 631095756582076109441699921 473321817436557082081274941)
            ·
              refine ⟨177495681538708905780478103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 473321817436557082081274941 177495681538708905780478103)
              ·
                refine ⟨266243522308063358670717155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177495681538708905780478103 266243522308063358670717155)
                ·
                  refine ⟨399365283462095038006075733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 266243522308063358670717155 399365283462095038006075733)
                  ·
                    refine ⟨1170015478892856556658425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 399365283462095038006075733 1170015478892856556658425)
                    ·
                      rfl

theorem cell23_6835791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 10].length) (baseStart_6835791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6835791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6835791 prefixEnd_6835791 := by exact prefixLift 6835791
  have htrace : WordTrace (prefixWord ++ tailWord_6835791) baseStart_6835791 baseEnd_6835791 := by
    simpa [prefixWord, tailWord_6835791, baseEnd_6835791] using wordTrace_append hprefix tailTrace_6835791
  have hstable : (prefixWord ++ tailWord_6835791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6835791).length < 2 ^ (prefixWord ++ tailWord_6835791).sum := by decide
  have hdescent : baseEnd_6835791 < baseStart_6835791 := by decide
  rcases family_descends (prefixWord ++ tailWord_6835791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6835815 : List Nat := [1, 1, 5, 1, 1, 1, 2, 1, 4, 4, 2]
def baseStart_6835815 : Nat := 118140960795 + 6835815 * 2 ^ 59
def prefixEnd_6835815 : Nat := 4983230072969 + 3 ^ 40 * 6835815 * 2
def baseEnd_6835815 : Nat := 3510058760214277576075165

theorem tailTrace_6835815 : CollatzResearch.WordTrace tailWord_6835815 prefixEnd_6835815 3510058760214277576075165 := by
  unfold tailWord_6835815
  simp only [CollatzResearch.WordTrace]
  refine ⟨249322655730017194100532899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166215103820011462733688599 249322655730017194100532899)
  ·
    refine ⟨373983983595025791150799349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249322655730017194100532899 373983983595025791150799349)
    ·
      refine ⟨35060998462033667920387439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 373983983595025791150799349 35060998462033667920387439)
      ·
        refine ⟨52591497693050501880581159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35060998462033667920387439 52591497693050501880581159)
        ·
          refine ⟨78887246539575752820871739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52591497693050501880581159 78887246539575752820871739)
          ·
            refine ⟨118330869809363629231307609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78887246539575752820871739 118330869809363629231307609)
            ·
              refine ⟨88748152357022721923480707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118330869809363629231307609 88748152357022721923480707)
              ·
                refine ⟨133122228535534082885221061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88748152357022721923480707 133122228535534082885221061)
                ·
                  refine ⟨24960417850412640540978949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 133122228535534082885221061 24960417850412640540978949)
                  ·
                    refine ⟨4680078346952370101433553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24960417850412640540978949 4680078346952370101433553)
                    ·
                      refine ⟨3510058760214277576075165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4680078346952370101433553 3510058760214277576075165)
                      ·
                        rfl

theorem cell23_6835815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 4, 4, 2].length) (baseStart_6835815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6835815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6835815 prefixEnd_6835815 := by exact prefixLift 6835815
  have htrace : WordTrace (prefixWord ++ tailWord_6835815) baseStart_6835815 baseEnd_6835815 := by
    simpa [prefixWord, tailWord_6835815, baseEnd_6835815] using wordTrace_append hprefix tailTrace_6835815
  have hstable : (prefixWord ++ tailWord_6835815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6835815).length < 2 ^ (prefixWord ++ tailWord_6835815).sum := by decide
  have hdescent : baseEnd_6835815 < baseStart_6835815 := by decide
  rcases family_descends (prefixWord ++ tailWord_6835815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6835865 : List Nat := [1, 2, 1, 2, 1, 2, 2, 1, 7, 1, 3]
def baseStart_6835865 : Nat := 118140960795 + 6835865 * 2 ^ 59
def prefixEnd_6835865 : Nat := 4983230072969 + 3 ^ 40 * 6835865 * 2
def baseEnd_6835865 : Nat := 3510084434247002380449935

theorem tailTrace_6835865 : CollatzResearch.WordTrace tailWord_6835865 prefixEnd_6835865 3510084434247002380449935 := by
  unfold tailWord_6835865
  simp only [CollatzResearch.WordTrace]
  refine ⟨249324479379836052639853049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166216319586557368426568699 249324479379836052639853049)
  ·
    refine ⟨186993359534877039479889787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249324479379836052639853049 186993359534877039479889787)
    ·
      refine ⟨280490039302315559219834681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186993359534877039479889787 280490039302315559219834681)
      ·
        refine ⟨210367529476736669414876011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280490039302315559219834681 210367529476736669414876011)
        ·
          refine ⟨315551294215105004122314017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210367529476736669414876011 315551294215105004122314017)
          ·
            refine ⟨236663470661328753091735513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 315551294215105004122314017 236663470661328753091735513)
            ·
              refine ⟨177497602995996564818801635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 236663470661328753091735513 177497602995996564818801635)
              ·
                refine ⟨266246404493994847228202453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177497602995996564818801635 266246404493994847228202453)
                ·
                  refine ⟨6240150105328004231910995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 266246404493994847228202453 6240150105328004231910995)
                  ·
                    refine ⟨9360225157992006347866493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6240150105328004231910995 9360225157992006347866493)
                    ·
                      refine ⟨3510084434247002380449935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9360225157992006347866493 3510084434247002380449935)
                      ·
                        rfl

theorem cell23_6835865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 7, 1, 3].length) (baseStart_6835865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6835865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6835865 prefixEnd_6835865 := by exact prefixLift 6835865
  have htrace : WordTrace (prefixWord ++ tailWord_6835865) baseStart_6835865 baseEnd_6835865 := by
    simpa [prefixWord, tailWord_6835865, baseEnd_6835865] using wordTrace_append hprefix tailTrace_6835865
  have hstable : (prefixWord ++ tailWord_6835865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6835865).length < 2 ^ (prefixWord ++ tailWord_6835865).sum := by decide
  have hdescent : baseEnd_6835865 < baseStart_6835865 := by decide
  rcases family_descends (prefixWord ++ tailWord_6835865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6835876 : List Nat := [2, 3, 1, 2, 2, 4, 2, 2, 1, 4]
def baseStart_6835876 : Nat := 118140960795 + 6835876 * 2 ^ 59
def prefixEnd_6835876 : Nat := 4983230072969 + 3 ^ 40 * 6835876 * 2
def baseEnd_6835876 : Nat := 1170030027511400612470795

theorem tailTrace_6835876 : CollatzResearch.WordTrace tailWord_6835876 prefixEnd_6835876 1170030027511400612470795 := by
  unfold tailWord_6835876
  simp only [CollatzResearch.WordTrace]
  refine ⟨124662440291398100759251741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166216587055197467679002321 124662440291398100759251741)
  ·
    refine ⟨46748415109274287784719403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124662440291398100759251741 46748415109274287784719403)
    ·
      refine ⟨70122622663911431677079105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46748415109274287784719403 70122622663911431677079105)
      ·
        refine ⟨52591966997933573757809329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70122622663911431677079105 52591966997933573757809329)
        ·
          refine ⟨39443975248450180318356997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52591966997933573757809329 39443975248450180318356997)
          ·
            refine ⟨7395745359084408809691937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39443975248450180318356997 7395745359084408809691937)
            ·
              refine ⟨5546809019313306607268953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7395745359084408809691937 5546809019313306607268953)
              ·
                refine ⟨4160106764484979955451715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5546809019313306607268953 4160106764484979955451715)
                ·
                  refine ⟨6240160146727469933177573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4160106764484979955451715 6240160146727469933177573)
                  ·
                    refine ⟨1170030027511400612470795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6240160146727469933177573 1170030027511400612470795)
                    ·
                      rfl

theorem cell23_6835876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 2, 2, 1, 4].length) (baseStart_6835876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6835876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6835876 prefixEnd_6835876 := by exact prefixLift 6835876
  have htrace : WordTrace (prefixWord ++ tailWord_6835876) baseStart_6835876 baseEnd_6835876 := by
    simpa [prefixWord, tailWord_6835876, baseEnd_6835876] using wordTrace_append hprefix tailTrace_6835876
  have hstable : (prefixWord ++ tailWord_6835876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6835876).length < 2 ^ (prefixWord ++ tailWord_6835876).sum := by decide
  have hdescent : baseEnd_6835876 < baseStart_6835876 := by decide
  rcases family_descends (prefixWord ++ tailWord_6835876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6835885 : List Nat := [1, 5, 2, 1, 1, 1, 1, 1, 5, 5]
def baseStart_6835885 : Nat := 118140960795 + 6835885 * 2 ^ 59
def prefixEnd_6835885 : Nat := 4983230072969 + 3 ^ 40 * 6835885 * 2
def baseEnd_6835885 : Nat := 1170031567953364100733281

theorem tailTrace_6835885 : CollatzResearch.WordTrace tailWord_6835885 prefixEnd_6835885 1170031567953364100733281 := by
  unfold tailWord_6835885
  simp only [CollatzResearch.WordTrace]
  refine ⟨249325208839763596055581109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166216805893175730703720739 249325208839763596055581109)
  ·
    refine ⟨23374238328727837130210729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 249325208839763596055581109 23374238328727837130210729)
    ·
      refine ⟨17530678746545877847658047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23374238328727837130210729 17530678746545877847658047)
      ·
        refine ⟨26296018119818816771487071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17530678746545877847658047 26296018119818816771487071)
        ·
          refine ⟨39444027179728225157230607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26296018119818816771487071 39444027179728225157230607)
          ·
            refine ⟨59166040769592337735845911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39444027179728225157230607 59166040769592337735845911)
            ·
              refine ⟨88749061154388506603768867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59166040769592337735845911 88749061154388506603768867)
              ·
                refine ⟨133123591731582759905653301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88749061154388506603768867 133123591731582759905653301)
                ·
                  refine ⟨12480336724835883741154997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 133123591731582759905653301 12480336724835883741154997)
                  ·
                    refine ⟨1170031567953364100733281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12480336724835883741154997 1170031567953364100733281)
                    ·
                      rfl

theorem cell23_6835885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_6835885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6835885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6835885 prefixEnd_6835885 := by exact prefixLift 6835885
  have htrace : WordTrace (prefixWord ++ tailWord_6835885) baseStart_6835885 baseEnd_6835885 := by
    simpa [prefixWord, tailWord_6835885, baseEnd_6835885] using wordTrace_append hprefix tailTrace_6835885
  have hstable : (prefixWord ++ tailWord_6835885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6835885).length < 2 ^ (prefixWord ++ tailWord_6835885).sum := by decide
  have hdescent : baseEnd_6835885 < baseStart_6835885 := by decide
  rcases family_descends (prefixWord ++ tailWord_6835885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6835928 : List Nat := [2, 1, 2, 2, 3, 1, 12]
def baseStart_6835928 : Nat := 118140960795 + 6835928 * 2 ^ 59
def prefixEnd_6835928 : Nat := 4983230072969 + 3 ^ 40 * 6835928 * 2
def baseEnd_6835928 : Nat := 43334775105286859678545

theorem tailTrace_6835928 : CollatzResearch.WordTrace tailWord_6835928 prefixEnd_6835928 43334775105286859678545 := by
  unfold tailWord_6835928
  simp only [CollatzResearch.WordTrace]
  refine ⟨124663388589303907199698219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166217851452405209599597625 124663388589303907199698219)
  ·
    refine ⟨186995082883955860799547329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124663388589303907199698219 186995082883955860799547329)
    ·
      refine ⟨140246312162966895599660497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186995082883955860799547329 140246312162966895599660497)
      ·
        refine ⟨105184734122225171699745373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140246312162966895599660497 105184734122225171699745373)
        ·
          refine ⟨39444275295834439387404515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105184734122225171699745373 39444275295834439387404515)
          ·
            refine ⟨59166412943751659081106773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39444275295834439387404515 59166412943751659081106773)
            ·
              refine ⟨43334775105286859678545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 59166412943751659081106773 43334775105286859678545)
              ·
                rfl

theorem cell23_6835928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 12].length) (baseStart_6835928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6835928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6835928 prefixEnd_6835928 := by exact prefixLift 6835928
  have htrace : WordTrace (prefixWord ++ tailWord_6835928) baseStart_6835928 baseEnd_6835928 := by
    simpa [prefixWord, tailWord_6835928, baseEnd_6835928] using wordTrace_append hprefix tailTrace_6835928
  have hstable : (prefixWord ++ tailWord_6835928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6835928).length < 2 ^ (prefixWord ++ tailWord_6835928).sum := by decide
  have hdescent : baseEnd_6835928 < baseStart_6835928 := by decide
  rcases family_descends (prefixWord ++ tailWord_6835928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6835956 : List Nat := [2, 6, 1, 1, 1, 1, 1, 4, 1, 1, 4]
def baseStart_6835956 : Nat := 118140960795 + 6835956 * 2 ^ 59
def prefixEnd_6835956 : Nat := 4983230072969 + 3 ^ 40 * 6835956 * 2
def baseEnd_6835956 : Nat := 3510131160986561524412017

theorem tailTrace_6835956 : CollatzResearch.WordTrace tailWord_6835956 prefixEnd_6835956 3510131160986561524412017 := by
  unfold tailWord_6835956
  simp only [CollatzResearch.WordTrace]
  refine ⟨124663899211253187590707861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166218532281670916787610481 124663899211253187590707861)
  ·
    refine ⟨5843620275527493168314431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 124663899211253187590707861 5843620275527493168314431)
    ·
      refine ⟨8765430413291239752471647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5843620275527493168314431 8765430413291239752471647)
      ·
        refine ⟨13148145619936859628707471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8765430413291239752471647 13148145619936859628707471)
        ·
          refine ⟨19722218429905289443061207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13148145619936859628707471 19722218429905289443061207)
          ·
            refine ⟨29583327644857934164591811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19722218429905289443061207 29583327644857934164591811)
            ·
              refine ⟨44374991467286901246887717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29583327644857934164591811 44374991467286901246887717)
              ·
                refine ⟨8320310900116293983791447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44374991467286901246887717 8320310900116293983791447)
                ·
                  refine ⟨12480466350174440975687171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8320310900116293983791447 12480466350174440975687171)
                  ·
                    refine ⟨18720699525261661463530757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12480466350174440975687171 18720699525261661463530757)
                    ·
                      refine ⟨3510131160986561524412017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18720699525261661463530757 3510131160986561524412017)
                      ·
                        rfl

theorem cell23_6835956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_6835956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6835956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6835956 prefixEnd_6835956 := by exact prefixLift 6835956
  have htrace : WordTrace (prefixWord ++ tailWord_6835956) baseStart_6835956 baseEnd_6835956 := by
    simpa [prefixWord, tailWord_6835956, baseEnd_6835956] using wordTrace_append hprefix tailTrace_6835956
  have hstable : (prefixWord ++ tailWord_6835956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6835956).length < 2 ^ (prefixWord ++ tailWord_6835956).sum := by decide
  have hdescent : baseEnd_6835956 < baseStart_6835956 := by decide
  rcases family_descends (prefixWord ++ tailWord_6835956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6836015 : List Nat := [1, 1, 2, 1, 2, 1, 2, 4, 2, 4, 3]
def baseStart_6836015 : Nat := 118140960795 + 6836015 * 2 ^ 59
def prefixEnd_6836015 : Nat := 4983230072969 + 3 ^ 40 * 6836015 * 2
def baseEnd_6836015 : Nat := 3510161456345176793574245

theorem tailTrace_6836015 : CollatzResearch.WordTrace tailWord_6836015 prefixEnd_6836015 3510161456345176793574245 := by
  unfold tailWord_6836015
  simp only [CollatzResearch.WordTrace]
  refine ⟨249329950329292628257813499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166219966886195085505208999 249329950329292628257813499)
  ·
    refine ⟨373994925493938942386720249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249329950329292628257813499 373994925493938942386720249)
    ·
      refine ⟨280496194120454206790040187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 373994925493938942386720249 280496194120454206790040187)
      ·
        refine ⟨420744291180681310185060281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280496194120454206790040187 420744291180681310185060281)
        ·
          refine ⟨315558218385510982638795211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 420744291180681310185060281 315558218385510982638795211)
          ·
            refine ⟨473337327578266473958192817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315558218385510982638795211 473337327578266473958192817)
            ·
              refine ⟨355002995683699855468644613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 473337327578266473958192817 355002995683699855468644613)
              ·
                refine ⟨66563061690693722900370865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 355002995683699855468644613 66563061690693722900370865)
                ·
                  refine ⟨49922296268020292175278149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66563061690693722900370865 49922296268020292175278149)
                  ·
                    refine ⟨9360430550253804782864653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49922296268020292175278149 9360430550253804782864653)
                    ·
                      refine ⟨3510161456345176793574245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9360430550253804782864653 3510161456345176793574245)
                      ·
                        rfl

theorem cell23_6836015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 2, 4, 3].length) (baseStart_6836015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6836015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6836015 prefixEnd_6836015 := by exact prefixLift 6836015
  have htrace : WordTrace (prefixWord ++ tailWord_6836015) baseStart_6836015 baseEnd_6836015 := by
    simpa [prefixWord, tailWord_6836015, baseEnd_6836015] using wordTrace_append hprefix tailTrace_6836015
  have hstable : (prefixWord ++ tailWord_6836015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6836015).length < 2 ^ (prefixWord ++ tailWord_6836015).sum := by decide
  have hdescent : baseEnd_6836015 < baseStart_6836015 := by decide
  rcases family_descends (prefixWord ++ tailWord_6836015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6836029 : List Nat := [1, 4, 1, 4, 1, 1, 1, 1, 3, 4, 2]
def baseStart_6836029 : Nat := 118140960795 + 6836029 * 2 ^ 59
def prefixEnd_6836029 : Nat := 4983230072969 + 3 ^ 40 * 6836029 * 2
def baseEnd_6836029 : Nat := 3510168645074339738799181

theorem tailTrace_6836029 : CollatzResearch.WordTrace tailWord_6836029 prefixEnd_6836029 3510168645074339738799181 := by
  unfold tailWord_6836029
  simp only [CollatzResearch.WordTrace]
  refine ⟨249330460951241908648823141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166220307300827939099215427 249330460951241908648823141)
  ·
    refine ⟨46749461428357857871654339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 249330460951241908648823141 46749461428357857871654339)
    ·
      refine ⟨70124192142536786807481509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46749461428357857871654339 70124192142536786807481509)
      ·
        refine ⟨13148286026725647526402783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70124192142536786807481509 13148286026725647526402783)
        ·
          refine ⟨19722429040088471289604175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13148286026725647526402783 19722429040088471289604175)
          ·
            refine ⟨29583643560132706934406263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19722429040088471289604175 29583643560132706934406263)
            ·
              refine ⟨44375465340199060401609395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29583643560132706934406263 44375465340199060401609395)
              ·
                refine ⟨66563198010298590602414093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44375465340199060401609395 66563198010298590602414093)
                ·
                  refine ⟨24961199253861971475905285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66563198010298590602414093 24961199253861971475905285)
                  ·
                    refine ⟨4680224860099119651732241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24961199253861971475905285 4680224860099119651732241)
                    ·
                      refine ⟨3510168645074339738799181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4680224860099119651732241 3510168645074339738799181)
                      ·
                        rfl

theorem cell23_6836029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_6836029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6836029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6836029 prefixEnd_6836029 := by exact prefixLift 6836029
  have htrace : WordTrace (prefixWord ++ tailWord_6836029) baseStart_6836029 baseEnd_6836029 := by
    simpa [prefixWord, tailWord_6836029, baseEnd_6836029] using wordTrace_append hprefix tailTrace_6836029
  have hstable : (prefixWord ++ tailWord_6836029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6836029).length < 2 ^ (prefixWord ++ tailWord_6836029).sum := by decide
  have hdescent : baseEnd_6836029 < baseStart_6836029 := by decide
  rcases family_descends (prefixWord ++ tailWord_6836029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6836065 : List Nat := [1, 2, 3, 1, 1, 1, 4, 2, 1, 7]
def baseStart_6836065 : Nat := 118140960795 + 6836065 * 2 ^ 59
def prefixEnd_6836065 : Nat := 4983230072969 + 3 ^ 40 * 6836065 * 2
def baseEnd_6836065 : Nat := 1170062376792633865983005

theorem tailTrace_6836065 : CollatzResearch.WordTrace tailWord_6836065 prefixEnd_6836065 1170062376792633865983005 := by
  unfold tailWord_6836065
  simp only [CollatzResearch.WordTrace]
  refine ⟨249331773979111486797133649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166221182652740991198089099 249331773979111486797133649)
  ·
    refine ⟨186998830484333615097850237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249331773979111486797133649 186998830484333615097850237)
    ·
      refine ⟨70124561431625105661693839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186998830484333615097850237 70124561431625105661693839)
      ·
        refine ⟨105186842147437658492540759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70124561431625105661693839 105186842147437658492540759)
        ·
          refine ⟨157780263221156487738811139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105186842147437658492540759 157780263221156487738811139)
          ·
            refine ⟨236670394831734731608216709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157780263221156487738811139 236670394831734731608216709)
            ·
              refine ⟨44375699030950262176540633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 236670394831734731608216709 44375699030950262176540633)
              ·
                refine ⟨33281774273212696632405475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44375699030950262176540633 33281774273212696632405475)
                ·
                  refine ⟨49922661409819044948608213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33281774273212696632405475 49922661409819044948608213)
                  ·
                    refine ⟨1170062376792633865983005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49922661409819044948608213 1170062376792633865983005)
                    ·
                      rfl

theorem cell23_6836065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 2, 1, 7].length) (baseStart_6836065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6836065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6836065 prefixEnd_6836065 := by exact prefixLift 6836065
  have htrace : WordTrace (prefixWord ++ tailWord_6836065) baseStart_6836065 baseEnd_6836065 := by
    simpa [prefixWord, tailWord_6836065, baseEnd_6836065] using wordTrace_append hprefix tailTrace_6836065
  have hstable : (prefixWord ++ tailWord_6836065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6836065).length < 2 ^ (prefixWord ++ tailWord_6836065).sum := by decide
  have hdescent : baseEnd_6836065 < baseStart_6836065 := by decide
  rcases family_descends (prefixWord ++ tailWord_6836065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6836097 : List Nat := [1, 2, 4, 4, 2, 1, 1, 2, 2, 2, 2]
def baseStart_6836097 : Nat := 118140960795 + 6836097 * 2 ^ 59
def prefixEnd_6836097 : Nat := 4983230072969 + 3 ^ 40 * 6836097 * 2
def baseEnd_6836097 : Nat := 3510203561758845472748869

theorem tailTrace_6836097 : CollatzResearch.WordTrace tailWord_6836097 prefixEnd_6836097 3510203561758845472748869 := by
  unfold tailWord_6836097
  simp only [CollatzResearch.WordTrace]
  refine ⟨249332941114995556262298545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166221960743330370841532363 249332941114995556262298545)
  ·
    refine ⟨186999705836246667196723909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249332941114995556262298545 186999705836246667196723909)
    ·
      refine ⟨35062444844296250099385733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 186999705836246667196723909 35062444844296250099385733)
      ·
        refine ⟨6574208408305546893634825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35062444844296250099385733 6574208408305546893634825)
        ·
          refine ⟨4930656306229160170226119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6574208408305546893634825 4930656306229160170226119)
          ·
            refine ⟨7395984459343740255339179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4930656306229160170226119 7395984459343740255339179)
            ·
              refine ⟨11093976689015610383008769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7395984459343740255339179 11093976689015610383008769)
              ·
                refine ⟨8320482516761707787256577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11093976689015610383008769 8320482516761707787256577)
                ·
                  refine ⟨6240361887571280840442433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8320482516761707787256577 6240361887571280840442433)
                  ·
                    refine ⟨4680271415678460630331825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6240361887571280840442433 4680271415678460630331825)
                    ·
                      refine ⟨3510203561758845472748869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4680271415678460630331825 3510203561758845472748869)
                      ·
                        rfl

theorem cell23_6836097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_6836097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6836097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6836097 prefixEnd_6836097 := by exact prefixLift 6836097
  have htrace : WordTrace (prefixWord ++ tailWord_6836097) baseStart_6836097 baseEnd_6836097 := by
    simpa [prefixWord, tailWord_6836097, baseEnd_6836097] using wordTrace_append hprefix tailTrace_6836097
  have hstable : (prefixWord ++ tailWord_6836097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6836097).length < 2 ^ (prefixWord ++ tailWord_6836097).sum := by decide
  have hdescent : baseEnd_6836097 < baseStart_6836097 := by decide
  rcases family_descends (prefixWord ++ tailWord_6836097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6836112 : List Nat := [2, 1, 1, 1, 1, 1, 2, 7, 3, 4]
def baseStart_6836112 : Nat := 118140960795 + 6836112 * 2 ^ 59
def prefixEnd_6836112 : Nat := 4983230072969 + 3 ^ 40 * 6836112 * 2
def baseEnd_6836112 : Nat := 1170070421322887638020433

theorem tailTrace_6836112 : CollatzResearch.WordTrace tailWord_6836112 prefixEnd_6836112 1170070421322887638020433 := by
  unfold tailWord_6836112
  simp only [CollatzResearch.WordTrace]
  refine ⟨124666744104970606912047295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166222325473294142549396393 124666744104970606912047295)
  ·
    refine ⟨187000116157455910368070943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124666744104970606912047295 187000116157455910368070943)
    ·
      refine ⟨280500174236183865552106415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187000116157455910368070943 280500174236183865552106415)
      ·
        refine ⟨420750261354275798328159623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280500174236183865552106415 420750261354275798328159623)
        ·
          refine ⟨631125392031413697492239435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 420750261354275798328159623 631125392031413697492239435)
          ·
            refine ⟨946688088047120546238359153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 631125392031413697492239435 946688088047120546238359153)
            ·
              refine ⟨710016066035340409678769365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 946688088047120546238359153 710016066035340409678769365)
              ·
                refine ⟨16641001547703290851846157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 710016066035340409678769365 16641001547703290851846157)
                ·
                  refine ⟨6240375580388734069442309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16641001547703290851846157 6240375580388734069442309)
                  ·
                    refine ⟨1170070421322887638020433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6240375580388734069442309 1170070421322887638020433)
                    ·
                      rfl

theorem cell23_6836112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 7, 3, 4].length) (baseStart_6836112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6836112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6836112 prefixEnd_6836112 := by exact prefixLift 6836112
  have htrace : WordTrace (prefixWord ++ tailWord_6836112) baseStart_6836112 baseEnd_6836112 := by
    simpa [prefixWord, tailWord_6836112, baseEnd_6836112] using wordTrace_append hprefix tailTrace_6836112
  have hstable : (prefixWord ++ tailWord_6836112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6836112).length < 2 ^ (prefixWord ++ tailWord_6836112).sum := by decide
  have hdescent : baseEnd_6836112 < baseStart_6836112 := by decide
  rcases family_descends (prefixWord ++ tailWord_6836112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6836119 : List Nat := [1, 1, 3, 3, 1, 3, 2, 1, 2, 4, 2]
def baseStart_6836119 : Nat := 118140960795 + 6836119 * 2 ^ 59
def prefixEnd_6836119 : Nat := 4983230072969 + 3 ^ 40 * 6836119 * 2
def baseEnd_6836119 : Nat := 3510214858333244386673767

theorem tailTrace_6836119 : CollatzResearch.WordTrace tailWord_6836119 prefixEnd_6836119 3510214858333244386673767 := by
  unfold tailWord_6836119
  simp only [CollatzResearch.WordTrace]
  refine ⟨249333743520915854019599411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166222495680610569346399607 249333743520915854019599411)
  ·
    refine ⟨374000615281373781029399117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249333743520915854019599411 374000615281373781029399117)
    ·
      refine ⟨140250230730515167886024669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 374000615281373781029399117 140250230730515167886024669)
      ·
        refine ⟨52593836523943187957259251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140250230730515167886024669 52593836523943187957259251)
        ·
          refine ⟨78890754785914781935888877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52593836523943187957259251 78890754785914781935888877)
          ·
            refine ⟨29584033044718043225958329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78890754785914781935888877 29584033044718043225958329)
            ·
              refine ⟨22188024783538532419468747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29584033044718043225958329 22188024783538532419468747)
              ·
                refine ⟨33282037175307798629203121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22188024783538532419468747 33282037175307798629203121)
                ·
                  refine ⟨24961527881480848971902341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33282037175307798629203121 24961527881480848971902341)
                  ·
                    refine ⟨4680286477777659182231689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24961527881480848971902341 4680286477777659182231689)
                    ·
                      refine ⟨3510214858333244386673767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4680286477777659182231689 3510214858333244386673767)
                      ·
                        rfl

theorem cell23_6836119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 1, 2, 4, 2].length) (baseStart_6836119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6836119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6836119 prefixEnd_6836119 := by exact prefixLift 6836119
  have htrace : WordTrace (prefixWord ++ tailWord_6836119) baseStart_6836119 baseEnd_6836119 := by
    simpa [prefixWord, tailWord_6836119, baseEnd_6836119] using wordTrace_append hprefix tailTrace_6836119
  have hstable : (prefixWord ++ tailWord_6836119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6836119).length < 2 ^ (prefixWord ++ tailWord_6836119).sum := by decide
  have hdescent : baseEnd_6836119 < baseStart_6836119 := by decide
  rcases family_descends (prefixWord ++ tailWord_6836119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6836196 : List Nat := [2, 3, 1, 1, 1, 1, 6, 1, 2, 3, 2]
def baseStart_6836196 : Nat := 118140960795 + 6836196 * 2 ^ 59
def prefixEnd_6836196 : Nat := 4983230072969 + 3 ^ 40 * 6836196 * 2
def baseEnd_6836196 : Nat := 3510254396343640585410913

theorem tailTrace_6836196 : CollatzResearch.WordTrace tailWord_6836196 prefixEnd_6836196 3510254396343640585410913 := by
  unfold tailWord_6836196
  simp only [CollatzResearch.WordTrace]
  refine ⟨124668275970818448085076221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166224367961091264113434961 124668275970818448085076221)
  ·
    refine ⟨46750603489056918031903583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124668275970818448085076221 46750603489056918031903583)
    ·
      refine ⟨70125905233585377047855375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46750603489056918031903583 70125905233585377047855375)
      ·
        refine ⟨105188857850378065571783063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70125905233585377047855375 105188857850378065571783063)
        ·
          refine ⟨157783286775567098357674595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105188857850378065571783063 157783286775567098357674595)
          ·
            refine ⟨236674930163350647536511893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157783286775567098357674595 236674930163350647536511893)
            ·
              refine ⟨11094137351407061603273995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 236674930163350647536511893 11094137351407061603273995)
              ·
                refine ⟨16641206027110592404910993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11094137351407061603273995 16641206027110592404910993)
                ·
                  refine ⟨12480904520332944303683245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16641206027110592404910993 12480904520332944303683245)
                  ·
                    refine ⟨4680339195124854113881217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12480904520332944303683245 4680339195124854113881217)
                    ·
                      refine ⟨3510254396343640585410913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4680339195124854113881217 3510254396343640585410913)
                      ·
                        rfl

theorem cell23_6836196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 1, 2, 3, 2].length) (baseStart_6836196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6836196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6836196 prefixEnd_6836196 := by exact prefixLift 6836196
  have htrace : WordTrace (prefixWord ++ tailWord_6836196) baseStart_6836196 baseEnd_6836196 := by
    simpa [prefixWord, tailWord_6836196, baseEnd_6836196] using wordTrace_append hprefix tailTrace_6836196
  have hstable : (prefixWord ++ tailWord_6836196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6836196).length < 2 ^ (prefixWord ++ tailWord_6836196).sum := by decide
  have hdescent : baseEnd_6836196 < baseStart_6836196 := by decide
  rcases family_descends (prefixWord ++ tailWord_6836196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6836219 : List Nat := [1, 1, 1, 1, 1, 3, 5, 4, 2, 4]
def baseStart_6836219 : Nat := 118140960795 + 6836219 * 2 ^ 59
def prefixEnd_6836219 : Nat := 4983230072969 + 3 ^ 40 * 6836219 * 2
def baseEnd_6836219 : Nat := 1170088735466231331807769

theorem tailTrace_6836219 : CollatzResearch.WordTrace tailWord_6836219 prefixEnd_6836219 1170088735466231331807769 := by
  unfold tailWord_6836219
  simp only [CollatzResearch.WordTrace]
  refine ⟨249337390820553571098239711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166224927213702380732159807 249337390820553571098239711)
  ·
    refine ⟨374006086230830356647359567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249337390820553571098239711 374006086230830356647359567)
    ·
      refine ⟨561009129346245534971039351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374006086230830356647359567 561009129346245534971039351)
      ·
        refine ⟨841513694019368302456559027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 561009129346245534971039351 841513694019368302456559027)
        ·
          refine ⟨1262270541029052453684838541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 841513694019368302456559027 1262270541029052453684838541)
          ·
            refine ⟨473351452885894670131814453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1262270541029052453684838541 473351452885894670131814453)
            ·
              refine ⟨44376698708052625324857605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 473351452885894670131814453 44376698708052625324857605)
              ·
                refine ⟨8320631007759867248410801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44376698708052625324857605 8320631007759867248410801)
                ·
                  refine ⟨6240473255819900436308101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8320631007759867248410801 6240473255819900436308101)
                  ·
                    refine ⟨1170088735466231331807769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6240473255819900436308101 1170088735466231331807769)
                    ·
                      rfl

theorem cell23_6836219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 4, 2, 4].length) (baseStart_6836219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6836219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6836219 prefixEnd_6836219 := by exact prefixLift 6836219
  have htrace : WordTrace (prefixWord ++ tailWord_6836219) baseStart_6836219 baseEnd_6836219 := by
    simpa [prefixWord, tailWord_6836219, baseEnd_6836219] using wordTrace_append hprefix tailTrace_6836219
  have hstable : (prefixWord ++ tailWord_6836219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6836219).length < 2 ^ (prefixWord ++ tailWord_6836219).sum := by decide
  have hdescent : baseEnd_6836219 < baseStart_6836219 := by decide
  rcases family_descends (prefixWord ++ tailWord_6836219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6836229 : List Nat := [1, 3, 1, 1, 2, 4, 1, 2, 3, 2, 3]
def baseStart_6836229 : Nat := 118140960795 + 6836229 * 2 ^ 59
def prefixEnd_6836229 : Nat := 4983230072969 + 3 ^ 40 * 6836229 * 2
def baseEnd_6836229 : Nat := 3510271341205238956298261

theorem tailTrace_6836229 : CollatzResearch.WordTrace tailWord_6836229 prefixEnd_6836229 3510271341205238956298261 := by
  unfold tailWord_6836229
  simp only [CollatzResearch.WordTrace]
  refine ⟨249337755550517342806103741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166225170367011561870735827 249337755550517342806103741)
  ·
    refine ⟨93501658331444003552288903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249337755550517342806103741 93501658331444003552288903)
    ·
      refine ⟨140252487497166005328433355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93501658331444003552288903 140252487497166005328433355)
      ·
        refine ⟨210378731245749007992650033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140252487497166005328433355 210378731245749007992650033)
        ·
          refine ⟨157784048434311755994487525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210378731245749007992650033 157784048434311755994487525)
          ·
            refine ⟨29584509081433454248966411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 157784048434311755994487525 29584509081433454248966411)
            ·
              refine ⟨44376763622150181373449617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29584509081433454248966411 44376763622150181373449617)
              ·
                refine ⟨33282572716612636030087213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44376763622150181373449617 33282572716612636030087213)
                ·
                  refine ⟨12480964768729738511282705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33282572716612636030087213 12480964768729738511282705)
                  ·
                    refine ⟨9360723576547303883462029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12480964768729738511282705 9360723576547303883462029)
                    ·
                      refine ⟨3510271341205238956298261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9360723576547303883462029 3510271341205238956298261)
                      ·
                        rfl

theorem cell23_6836229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 2, 3, 2, 3].length) (baseStart_6836229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6836229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6836229 prefixEnd_6836229 := by exact prefixLift 6836229
  have htrace : WordTrace (prefixWord ++ tailWord_6836229) baseStart_6836229 baseEnd_6836229 := by
    simpa [prefixWord, tailWord_6836229, baseEnd_6836229] using wordTrace_append hprefix tailTrace_6836229
  have hstable : (prefixWord ++ tailWord_6836229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6836229).length < 2 ^ (prefixWord ++ tailWord_6836229).sum := by decide
  have hdescent : baseEnd_6836229 < baseStart_6836229 := by decide
  rcases family_descends (prefixWord ++ tailWord_6836229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6836237 : List Nat := [1, 7, 1, 2, 1, 1, 1, 2, 3, 1, 3]
def baseStart_6836237 : Nat := 118140960795 + 6836237 * 2 ^ 59
def prefixEnd_6836237 : Nat := 4983230072969 + 3 ^ 40 * 6836237 * 2
def baseEnd_6836237 : Nat := 3510275449050474924998225

theorem tailTrace_6836237 : CollatzResearch.WordTrace tailWord_6836237 prefixEnd_6836237 3510275449050474924998225 := by
  unfold tailWord_6836237
  simp only [CollatzResearch.WordTrace]
  refine ⟨249338047334488360172394965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166225364889658906781596643 249338047334488360172394965)
  ·
    refine ⟨5843860484402070941540507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 249338047334488360172394965 5843860484402070941540507)
    ·
      refine ⟨8765790726603106412310761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5843860484402070941540507 8765790726603106412310761)
      ·
        refine ⟨6574343044952329809233071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8765790726603106412310761 6574343044952329809233071)
        ·
          refine ⟨9861514567428494713849607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6574343044952329809233071 9861514567428494713849607)
          ·
            refine ⟨14792271851142742070774411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9861514567428494713849607 14792271851142742070774411)
            ·
              refine ⟨22188407776714113106161617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14792271851142742070774411 22188407776714113106161617)
              ·
                refine ⟨16641305832535584829621213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22188407776714113106161617 16641305832535584829621213)
                ·
                  refine ⟨6240489687200844311107955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16641305832535584829621213 6240489687200844311107955)
                  ·
                    refine ⟨9360734530801266466661933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6240489687200844311107955 9360734530801266466661933)
                    ·
                      refine ⟨3510275449050474924998225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9360734530801266466661933 3510275449050474924998225)
                      ·
                        rfl

theorem cell23_6836237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_6836237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6836237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6836237 prefixEnd_6836237 := by exact prefixLift 6836237
  have htrace : WordTrace (prefixWord ++ tailWord_6836237) baseStart_6836237 baseEnd_6836237 := by
    simpa [prefixWord, tailWord_6836237, baseEnd_6836237] using wordTrace_append hprefix tailTrace_6836237
  have hstable : (prefixWord ++ tailWord_6836237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6836237).length < 2 ^ (prefixWord ++ tailWord_6836237).sum := by decide
  have hdescent : baseEnd_6836237 < baseStart_6836237 := by decide
  rcases family_descends (prefixWord ++ tailWord_6836237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6836259 : List Nat := [1, 1, 1, 4, 3, 1, 1, 4, 1, 3, 3]
def baseStart_6836259 : Nat := 118140960795 + 6836259 * 2 ^ 59
def prefixEnd_6836259 : Nat := 4983230072969 + 3 ^ 40 * 6836259 * 2
def baseEnd_6836259 : Nat := 3510286745624873838923123

theorem tailTrace_6836259 : CollatzResearch.WordTrace tailWord_6836259 prefixEnd_6836259 3510286745624873838923123 := by
  unfold tailWord_6836259
  simp only [CollatzResearch.WordTrace]
  refine ⟨249338849740408657929695831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166225899826939105286463887 249338849740408657929695831)
  ·
    refine ⟨374008274610612986894543747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249338849740408657929695831 374008274610612986894543747)
    ·
      refine ⟨561012411915919480341815621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374008274610612986894543747 561012411915919480341815621)
      ·
        refine ⟨105189827234234902564090429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 561012411915919480341815621 105189827234234902564090429)
        ·
          refine ⟨39446185212838088461533911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105189827234234902564090429 39446185212838088461533911)
          ·
            refine ⟨59169277819257132692300867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39446185212838088461533911 59169277819257132692300867)
            ·
              refine ⟨88753916728885699038451301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59169277819257132692300867 88753916728885699038451301)
              ·
                refine ⟨16641359386666068569709619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88753916728885699038451301 16641359386666068569709619)
                ·
                  refine ⟨24962039079999102854564429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16641359386666068569709619 24962039079999102854564429)
                  ·
                    refine ⟨9360764654999663570461661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24962039079999102854564429 9360764654999663570461661)
                    ·
                      refine ⟨3510286745624873838923123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9360764654999663570461661 3510286745624873838923123)
                      ·
                        rfl

theorem cell23_6836259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 4, 1, 3, 3].length) (baseStart_6836259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6836259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6836259 prefixEnd_6836259 := by exact prefixLift 6836259
  have htrace : WordTrace (prefixWord ++ tailWord_6836259) baseStart_6836259 baseEnd_6836259 := by
    simpa [prefixWord, tailWord_6836259, baseEnd_6836259] using wordTrace_append hprefix tailTrace_6836259
  have hstable : (prefixWord ++ tailWord_6836259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6836259).length < 2 ^ (prefixWord ++ tailWord_6836259).sum := by decide
  have hdescent : baseEnd_6836259 < baseStart_6836259 := by decide
  rcases family_descends (prefixWord ++ tailWord_6836259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6836260 : List Nat := [2, 3, 1, 4, 2, 2, 2, 1, 1, 1, 4]
def baseStart_6836260 : Nat := 118140960795 + 6836260 * 2 ^ 59
def prefixEnd_6836260 : Nat := 4983230072969 + 3 ^ 40 * 6836260 * 2
def baseEnd_6836260 : Nat := 3510287259105528335010619

theorem tailTrace_6836260 : CollatzResearch.WordTrace tailWord_6836260 prefixEnd_6836260 3510287259105528335010619 := by
  unfold tailWord_6836260
  simp only [CollatzResearch.WordTrace]
  refine ⟨124669443106702517550241117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166225924142270023400321489 124669443106702517550241117)
  ·
    refine ⟨46751041165013444081340419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124669443106702517550241117 46751041165013444081340419)
    ·
      refine ⟨70126561747520166122010629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46751041165013444081340419 70126561747520166122010629)
      ·
        refine ⟨13148730327660031147876993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70126561747520166122010629 13148730327660031147876993)
        ·
          refine ⟨9861547745745023360907745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13148730327660031147876993 9861547745745023360907745)
          ·
            refine ⟨7396160809308767520680809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9861547745745023360907745 7396160809308767520680809)
            ·
              refine ⟨5547120606981575640510607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7396160809308767520680809 5547120606981575640510607)
              ·
                refine ⟨8320680910472363460765911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5547120606981575640510607 8320680910472363460765911)
                ·
                  refine ⟨12481021365708545191148867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8320680910472363460765911 12481021365708545191148867)
                  ·
                    refine ⟨18721532048562817786723301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12481021365708545191148867 18721532048562817786723301)
                    ·
                      refine ⟨3510287259105528335010619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18721532048562817786723301 3510287259105528335010619)
                      ·
                        rfl

theorem cell23_6836260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_6836260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6836260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6836260 prefixEnd_6836260 := by exact prefixLift 6836260
  have htrace : WordTrace (prefixWord ++ tailWord_6836260) baseStart_6836260 baseEnd_6836260 := by
    simpa [prefixWord, tailWord_6836260, baseEnd_6836260] using wordTrace_append hprefix tailTrace_6836260
  have hstable : (prefixWord ++ tailWord_6836260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6836260).length < 2 ^ (prefixWord ++ tailWord_6836260).sum := by decide
  have hdescent : baseEnd_6836260 < baseStart_6836260 := by decide
  rcases family_descends (prefixWord ++ tailWord_6836260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6836310 : List Nat := [5, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3]
def baseStart_6836310 : Nat := 118140960795 + 6836310 * 2 ^ 59
def prefixEnd_6836310 : Nat := 4983230072969 + 3 ^ 40 * 6836310 * 2
def baseEnd_6836310 : Nat := 3510312933138253139385389

theorem tailTrace_6836310 : CollatzResearch.WordTrace tailWord_6836310 prefixEnd_6836310 3510312933138253139385389 := by
  unfold tailWord_6836310
  simp only [CollatzResearch.WordTrace]
  refine ⟨15583794366451493352487649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 166227139908815929093201589 15583794366451493352487649)
  ·
    refine ⟨11687845774838620014365737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15583794366451493352487649 11687845774838620014365737)
    ·
      refine ⟨8765884331128965010774303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11687845774838620014365737 8765884331128965010774303)
      ·
        refine ⟨13148826496693447516161455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8765884331128965010774303 13148826496693447516161455)
        ·
          refine ⟨19723239745040171274242183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13148826496693447516161455 19723239745040171274242183)
          ·
            refine ⟨29584859617560256911363275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19723239745040171274242183 29584859617560256911363275)
            ·
              refine ⟨44377289426340385367044913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29584859617560256911363275 44377289426340385367044913)
              ·
                refine ⟨33282967069755289025283685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44377289426340385367044913 33282967069755289025283685)
                ·
                  refine ⟨6240556325579116692240691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33282967069755289025283685 6240556325579116692240691)
                  ·
                    refine ⟨9360834488368675038361037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6240556325579116692240691 9360834488368675038361037)
                    ·
                      refine ⟨3510312933138253139385389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9360834488368675038361037 3510312933138253139385389)
                      ·
                        rfl

theorem cell23_6836310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_6836310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6836310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6836310 prefixEnd_6836310 := by exact prefixLift 6836310
  have htrace : WordTrace (prefixWord ++ tailWord_6836310) baseStart_6836310 baseEnd_6836310 := by
    simpa [prefixWord, tailWord_6836310, baseEnd_6836310] using wordTrace_append hprefix tailTrace_6836310
  have hstable : (prefixWord ++ tailWord_6836310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6836310).length < 2 ^ (prefixWord ++ tailWord_6836310).sum := by decide
  have hdescent : baseEnd_6836310 < baseStart_6836310 := by decide
  rcases family_descends (prefixWord ++ tailWord_6836310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6836333 : List Nat := [1, 5, 1, 1, 2, 1, 1, 3, 4, 2, 2]
def baseStart_6836333 : Nat := 118140960795 + 6836333 * 2 ^ 59
def prefixEnd_6836333 : Nat := 4983230072969 + 3 ^ 40 * 6836333 * 2
def baseEnd_6836333 : Nat := 3510324743193306549397783

theorem tailTrace_6836333 : CollatzResearch.WordTrace tailWord_6836333 prefixEnd_6836333 3510324743193306549397783 := by
  unfold tailWord_6836333
  simp only [CollatzResearch.WordTrace]
  refine ⟨249341548742140568567889653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166227699161427045711926435 249341548742140568567889653)
  ·
    refine ⟨23375770194575678303239655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 249341548742140568567889653 23375770194575678303239655)
    ·
      refine ⟨35063655291863517454859483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23375770194575678303239655 35063655291863517454859483)
      ·
        refine ⟨52595482937795276182289225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35063655291863517454859483 52595482937795276182289225)
        ·
          refine ⟨39446612203346457136716919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52595482937795276182289225 39446612203346457136716919)
          ·
            refine ⟨59169918305019685705075379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39446612203346457136716919 59169918305019685705075379)
            ·
              refine ⟨88754877457529528557613069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59169918305019685705075379 88754877457529528557613069)
              ·
                refine ⟨33283079046573573209104901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88754877457529528557613069 33283079046573573209104901)
                ·
                  refine ⟨6240577321232544976707169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33283079046573573209104901 6240577321232544976707169)
                  ·
                    refine ⟨4680432990924408732530377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6240577321232544976707169 4680432990924408732530377)
                    ·
                      refine ⟨3510324743193306549397783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4680432990924408732530377 3510324743193306549397783)
                      ·
                        rfl

theorem cell23_6836333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 3, 4, 2, 2].length) (baseStart_6836333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6836333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6836333 prefixEnd_6836333 := by exact prefixLift 6836333
  have htrace : WordTrace (prefixWord ++ tailWord_6836333) baseStart_6836333 baseEnd_6836333 := by
    simpa [prefixWord, tailWord_6836333, baseEnd_6836333] using wordTrace_append hprefix tailTrace_6836333
  have hstable : (prefixWord ++ tailWord_6836333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6836333).length < 2 ^ (prefixWord ++ tailWord_6836333).sum := by decide
  have hdescent : baseEnd_6836333 < baseStart_6836333 := by decide
  rcases family_descends (prefixWord ++ tailWord_6836333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6836416 : List Nat := [2, 1, 1, 2, 5, 1, 1, 1, 5, 4]
def baseStart_6836416 : Nat := 118140960795 + 6836416 * 2 ^ 59
def prefixEnd_6836416 : Nat := 4983230072969 + 3 ^ 40 * 6836416 * 2
def baseEnd_6836416 : Nat := 1170122454029209908219967

theorem tailTrace_6836416 : CollatzResearch.WordTrace tailWord_6836416 prefixEnd_6836416 1170122454029209908219967 := by
  unfold tailWord_6836416
  simp only [CollatzResearch.WordTrace]
  refine ⟨124672288000419936871580551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166229717333893249162107401 124672288000419936871580551)
  ·
    refine ⟨187008432000629905307370827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124672288000419936871580551 187008432000629905307370827)
    ·
      refine ⟨280512648000944857961056241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187008432000629905307370827 280512648000944857961056241)
      ·
        refine ⟨210384486000708643470792181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280512648000944857961056241 210384486000708643470792181)
        ·
          refine ⟨19723545562566435325386767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 210384486000708643470792181 19723545562566435325386767)
          ·
            refine ⟨29585318343849652988080151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19723545562566435325386767 29585318343849652988080151)
            ·
              refine ⟨44377977515774479482120227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29585318343849652988080151 44377977515774479482120227)
              ·
                refine ⟨66566966273661719223180341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44377977515774479482120227 66566966273661719223180341)
                ·
                  refine ⟨6240653088155786177173157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66566966273661719223180341 6240653088155786177173157)
                  ·
                    refine ⟨1170122454029209908219967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6240653088155786177173157 1170122454029209908219967)
                    ·
                      rfl

theorem cell23_6836416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 5, 4].length) (baseStart_6836416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6836416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6836416 prefixEnd_6836416 := by exact prefixLift 6836416
  have htrace : WordTrace (prefixWord ++ tailWord_6836416) baseStart_6836416 baseEnd_6836416 := by
    simpa [prefixWord, tailWord_6836416, baseEnd_6836416] using wordTrace_append hprefix tailTrace_6836416
  have hstable : (prefixWord ++ tailWord_6836416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6836416).length < 2 ^ (prefixWord ++ tailWord_6836416).sum := by decide
  have hdescent : baseEnd_6836416 < baseStart_6836416 := by decide
  rcases family_descends (prefixWord ++ tailWord_6836416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6836426 : List Nat := [3, 1, 2, 1, 3, 1, 3, 1, 1, 4, 3]
def baseStart_6836426 : Nat := 118140960795 + 6836426 * 2 ^ 59
def prefixEnd_6836426 : Nat := 4983230072969 + 3 ^ 40 * 6836426 * 2
def baseEnd_6836426 : Nat := 3510372496894174685534855

theorem tailTrace_6836426 : CollatzResearch.WordTrace tailWord_6836426 prefixEnd_6836426 3510372496894174685534855 := by
  unfold tailWord_6836426
  simp only [CollatzResearch.WordTrace]
  refine ⟨62336235182700911362756283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166229960487202430300683421 62336235182700911362756283)
  ·
    refine ⟨93504352774051367044134425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62336235182700911362756283 93504352774051367044134425)
    ·
      refine ⟨70128264580538525283100819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93504352774051367044134425 70128264580538525283100819)
      ·
        refine ⟨105192396870807787924651229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70128264580538525283100819 105192396870807787924651229)
        ·
          refine ⟨39447148826552920471744211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105192396870807787924651229 39447148826552920471744211)
          ·
            refine ⟨59170723239829380707616317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39447148826552920471744211 59170723239829380707616317)
            ·
              refine ⟨22189021214936017765356119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59170723239829380707616317 22189021214936017765356119)
              ·
                refine ⟨33283531822404026648034179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22189021214936017765356119 33283531822404026648034179)
                ·
                  refine ⟨49925297733606039972051269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33283531822404026648034179 49925297733606039972051269)
                  ·
                    refine ⟨9360993325051132494759613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49925297733606039972051269 9360993325051132494759613)
                    ·
                      refine ⟨3510372496894174685534855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9360993325051132494759613 3510372496894174685534855)
                      ·
                        rfl

theorem cell23_6836426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 1, 1, 4, 3].length) (baseStart_6836426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6836426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6836426 prefixEnd_6836426 := by exact prefixLift 6836426
  have htrace : WordTrace (prefixWord ++ tailWord_6836426) baseStart_6836426 baseEnd_6836426 := by
    simpa [prefixWord, tailWord_6836426, baseEnd_6836426] using wordTrace_append hprefix tailTrace_6836426
  have hstable : (prefixWord ++ tailWord_6836426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6836426).length < 2 ^ (prefixWord ++ tailWord_6836426).sum := by decide
  have hdescent : baseEnd_6836426 < baseStart_6836426 := by decide
  rcases family_descends (prefixWord ++ tailWord_6836426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6836433 : List Nat := [1, 2, 2, 1, 2, 2, 3, 5, 1, 4]
def baseStart_6836433 : Nat := 118140960795 + 6836433 * 2 ^ 59
def prefixEnd_6836433 : Nat := 4983230072969 + 3 ^ 40 * 6836433 * 2
def baseEnd_6836433 : Nat := 1170125363752918719382441

theorem tailTrace_6836433 : CollatzResearch.WordTrace tailWord_6836433 prefixEnd_6836433 1170125363752918719382441 := by
  unfold tailWord_6836433
  simp only [CollatzResearch.WordTrace]
  refine ⟨249345196041778285646529953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166230130694518857097686635 249345196041778285646529953)
  ·
    refine ⟨187008897031333714234897465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249345196041778285646529953 187008897031333714234897465)
    ·
      refine ⟨140256672773500285676173099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187008897031333714234897465 140256672773500285676173099)
      ·
        refine ⟨210385009160250428514259649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140256672773500285676173099 210385009160250428514259649)
        ·
          refine ⟨157788756870187821385694737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210385009160250428514259649 157788756870187821385694737)
          ·
            refine ⟨118341567652640866039271053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157788756870187821385694737 118341567652640866039271053)
            ·
              refine ⟨44378087869740324764726645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118341567652640866039271053 44378087869740324764726645)
              ·
                refine ⟨4160445737788155446693123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44378087869740324764726645 4160445737788155446693123)
                ·
                  refine ⟨6240668606682233170039685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4160445737788155446693123 6240668606682233170039685)
                  ·
                    refine ⟨1170125363752918719382441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6240668606682233170039685 1170125363752918719382441)
                    ·
                      rfl

theorem cell23_6836433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 5, 1, 4].length) (baseStart_6836433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6836433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6836433 prefixEnd_6836433 := by exact prefixLift 6836433
  have htrace : WordTrace (prefixWord ++ tailWord_6836433) baseStart_6836433 baseEnd_6836433 := by
    simpa [prefixWord, tailWord_6836433, baseEnd_6836433] using wordTrace_append hprefix tailTrace_6836433
  have hstable : (prefixWord ++ tailWord_6836433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6836433).length < 2 ^ (prefixWord ++ tailWord_6836433).sum := by decide
  have hdescent : baseEnd_6836433 < baseStart_6836433 := by decide
  rcases family_descends (prefixWord ++ tailWord_6836433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6836449 : List Nat := [1, 2, 3, 1, 3, 1, 1, 1, 1, 1, 8]
def baseStart_6836449 : Nat := 118140960795 + 6836449 * 2 ^ 59
def prefixEnd_6836449 : Nat := 4983230072969 + 3 ^ 40 * 6836449 * 2
def baseEnd_6836449 : Nat := 3510384306949228095547249

theorem tailTrace_6836449 : CollatzResearch.WordTrace tailWord_6836449 prefixEnd_6836449 3510384306949228095547249 := by
  unfold tailWord_6836449
  simp only [CollatzResearch.WordTrace]
  refine ⟨249345779609720320379112401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166230519739813546919408267 249345779609720320379112401)
  ·
    refine ⟨187009334707290240284334301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249345779609720320379112401 187009334707290240284334301)
    ·
      refine ⟨70128500515233840106625363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187009334707290240284334301 70128500515233840106625363)
      ·
        refine ⟨105192750772850760159938045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70128500515233840106625363 105192750772850760159938045)
        ·
          refine ⟨39447281539819035059976767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105192750772850760159938045 39447281539819035059976767)
          ·
            refine ⟨59170922309728552589965151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39447281539819035059976767 59170922309728552589965151)
            ·
              refine ⟨88756383464592828884947727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59170922309728552589965151 88756383464592828884947727)
              ·
                refine ⟨133134575196889243327421591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88756383464592828884947727 133134575196889243327421591)
                ·
                  refine ⟨199701862795333864991132387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133134575196889243327421591 199701862795333864991132387)
                  ·
                    refine ⟨299552794193000797486698581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 199701862795333864991132387 299552794193000797486698581)
                    ·
                      refine ⟨3510384306949228095547249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 299552794193000797486698581 3510384306949228095547249)
                      ·
                        rfl

theorem cell23_6836449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 1, 8].length) (baseStart_6836449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6836449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6836449 prefixEnd_6836449 := by exact prefixLift 6836449
  have htrace : WordTrace (prefixWord ++ tailWord_6836449) baseStart_6836449 baseEnd_6836449 := by
    simpa [prefixWord, tailWord_6836449, baseEnd_6836449] using wordTrace_append hprefix tailTrace_6836449
  have hstable : (prefixWord ++ tailWord_6836449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6836449).length < 2 ^ (prefixWord ++ tailWord_6836449).sum := by decide
  have hdescent : baseEnd_6836449 < baseStart_6836449 := by decide
  rcases family_descends (prefixWord ++ tailWord_6836449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6836463 : List Nat := [1, 1, 2, 1, 6, 2, 3, 1, 6]
def baseStart_6836463 : Nat := 118140960795 + 6836463 * 2 ^ 59
def prefixEnd_6836463 : Nat := 4983230072969 + 3 ^ 40 * 6836463 * 2
def baseEnd_6836463 : Nat := 390043499519821226752465

theorem tailTrace_6836463 : CollatzResearch.WordTrace tailWord_6836463 prefixEnd_6836463 390043499519821226752465 := by
  unfold tailWord_6836463
  simp only [CollatzResearch.WordTrace]
  refine ⟨249346290231669600770122043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166230860154446400513414695 249346290231669600770122043)
  ·
    refine ⟨374019435347504401155183065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249346290231669600770122043 374019435347504401155183065)
    ·
      refine ⟨280514576510628300866387299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 374019435347504401155183065 280514576510628300866387299)
      ·
        refine ⟨420771864765942451299580949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280514576510628300866387299 420771864765942451299580949)
        ·
          refine ⟨19723681160903552404667857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 420771864765942451299580949 19723681160903552404667857)
          ·
            refine ⟨14792760870677664303500893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19723681160903552404667857 14792760870677664303500893)
            ·
              refine ⟨5547285326504124113812835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14792760870677664303500893 5547285326504124113812835)
              ·
                refine ⟨8320927989756186170719253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5547285326504124113812835 8320927989756186170719253)
                ·
                  refine ⟨390043499519821226752465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8320927989756186170719253 390043499519821226752465)
                  ·
                    rfl

theorem cell23_6836463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 3, 1, 6].length) (baseStart_6836463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6836463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6836463 prefixEnd_6836463 := by exact prefixLift 6836463
  have htrace : WordTrace (prefixWord ++ tailWord_6836463) baseStart_6836463 baseEnd_6836463 := by
    simpa [prefixWord, tailWord_6836463, baseEnd_6836463] using wordTrace_append hprefix tailTrace_6836463
  have hstable : (prefixWord ++ tailWord_6836463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6836463).length < 2 ^ (prefixWord ++ tailWord_6836463).sum := by decide
  have hdescent : baseEnd_6836463 < baseStart_6836463 := by decide
  rcases family_descends (prefixWord ++ tailWord_6836463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6836483 : List Nat := [1, 1, 1, 3, 2, 3, 2, 3, 2, 3, 2]
def baseStart_6836483 : Nat := 118140960795 + 6836483 * 2 ^ 59
def prefixEnd_6836483 : Nat := 4983230072969 + 3 ^ 40 * 6836483 * 2
def baseEnd_6836483 : Nat := 3510401765291480962522093

theorem tailTrace_6836483 : CollatzResearch.WordTrace tailWord_6836483 prefixEnd_6836483 3510401765291480962522093 := by
  unfold tailWord_6836483
  simp only [CollatzResearch.WordTrace]
  refine ⟨249347019691597144185850103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166231346461064762790566735 249347019691597144185850103)
  ·
    refine ⟨374020529537395716278775155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249347019691597144185850103 374020529537395716278775155)
    ·
      refine ⟨561030794306093574418162733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374020529537395716278775155 561030794306093574418162733)
      ·
        refine ⟨210386547864785090406811025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 561030794306093574418162733 210386547864785090406811025)
        ·
          refine ⟨157789910898588817805108269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210386547864785090406811025 157789910898588817805108269)
          ·
            refine ⟨59171216586970806676915601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157789910898588817805108269 59171216586970806676915601)
            ·
              refine ⟨44378412440228105007686701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59171216586970806676915601 44378412440228105007686701)
              ·
                refine ⟨16641904665085539377882513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44378412440228105007686701 16641904665085539377882513)
                ·
                  refine ⟨12481428498814154533411885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16641904665085539377882513 12481428498814154533411885)
                  ·
                    refine ⟨4680535687055307950029457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12481428498814154533411885 4680535687055307950029457)
                    ·
                      refine ⟨3510401765291480962522093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4680535687055307950029457 3510401765291480962522093)
                      ·
                        rfl

theorem cell23_6836483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 3, 2, 3, 2].length) (baseStart_6836483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6836483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6836483 prefixEnd_6836483 := by exact prefixLift 6836483
  have htrace : WordTrace (prefixWord ++ tailWord_6836483) baseStart_6836483 baseEnd_6836483 := by
    simpa [prefixWord, tailWord_6836483, baseEnd_6836483] using wordTrace_append hprefix tailTrace_6836483
  have hstable : (prefixWord ++ tailWord_6836483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6836483).length < 2 ^ (prefixWord ++ tailWord_6836483).sum := by decide
  have hdescent : baseEnd_6836483 < baseStart_6836483 := by decide
  rcases family_descends (prefixWord ++ tailWord_6836483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6836484 : List Nat := [2, 3, 2, 2, 4, 1, 1, 3, 1, 4]
def baseStart_6836484 : Nat := 118140960795 + 6836484 * 2 ^ 59
def prefixEnd_6836484 : Nat := 4983230072969 + 3 ^ 40 * 6836484 * 2
def baseEnd_6836484 : Nat := 1170134092924045152869863

theorem tailTrace_6836484 : CollatzResearch.WordTrace tailWord_6836484 prefixEnd_6836484 1170134092924045152869863 := by
  unfold tailWord_6836484
  simp only [CollatzResearch.WordTrace]
  refine ⟨124673528082296760678318253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166231370776395680904424337 124673528082296760678318253)
  ·
    refine ⟨46752573030861285254369345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124673528082296760678318253 46752573030861285254369345)
    ·
      refine ⟨35064429773145963940777009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46752573030861285254369345 35064429773145963940777009)
      ·
        refine ⟨26298322329859472955582757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35064429773145963940777009 26298322329859472955582757)
        ·
          refine ⟨4930935436848651179171767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26298322329859472955582757 4930935436848651179171767)
          ·
            refine ⟨7396403155272976768757651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4930935436848651179171767 7396403155272976768757651)
            ·
              refine ⟨11094604732909465153136477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7396403155272976768757651 11094604732909465153136477)
              ·
                refine ⟨4160476774841049432426179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11094604732909465153136477 4160476774841049432426179)
                ·
                  refine ⟨6240715162261574148639269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4160476774841049432426179 6240715162261574148639269)
                  ·
                    refine ⟨1170134092924045152869863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6240715162261574148639269 1170134092924045152869863)
                    ·
                      rfl

theorem cell23_6836484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 3, 1, 4].length) (baseStart_6836484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6836484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6836484 prefixEnd_6836484 := by exact prefixLift 6836484
  have htrace : WordTrace (prefixWord ++ tailWord_6836484) baseStart_6836484 baseEnd_6836484 := by
    simpa [prefixWord, tailWord_6836484, baseEnd_6836484] using wordTrace_append hprefix tailTrace_6836484
  have hstable : (prefixWord ++ tailWord_6836484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6836484).length < 2 ^ (prefixWord ++ tailWord_6836484).sum := by decide
  have hdescent : baseEnd_6836484 < baseStart_6836484 := by decide
  rcases family_descends (prefixWord ++ tailWord_6836484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6836533 : List Nat := [1, 3, 3, 1, 2, 1, 3, 1, 3, 2, 3]
def baseStart_6836533 : Nat := 118140960795 + 6836533 * 2 ^ 59
def prefixEnd_6836533 : Nat := 4983230072969 + 3 ^ 40 * 6836533 * 2
def baseEnd_6836533 : Nat := 3510427439324205766896863

theorem tailTrace_6836533 : CollatzResearch.WordTrace tailWord_6836533 prefixEnd_6836533 3510427439324205766896863 := by
  unfold tailWord_6836533
  simp only [CollatzResearch.WordTrace]
  refine ⟨249348843341416002725170253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166232562227610668483446835 249348843341416002725170253)
  ·
    refine ⟨93505816253031001021938845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249348843341416002725170253 93505816253031001021938845)
    ·
      refine ⟨35064681094886625383227067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93505816253031001021938845 35064681094886625383227067)
      ·
        refine ⟨52597021642329938074840601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35064681094886625383227067 52597021642329938074840601)
        ·
          refine ⟨39447766231747453556130451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52597021642329938074840601 39447766231747453556130451)
          ·
            refine ⟨59171649347621180334195677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39447766231747453556130451 59171649347621180334195677)
            ·
              refine ⟨22189368505357942625323379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59171649347621180334195677 22189368505357942625323379)
              ·
                refine ⟨33284052758036913937985069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22189368505357942625323379 33284052758036913937985069)
                ·
                  refine ⟨12481519784263842726744401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33284052758036913937985069 12481519784263842726744401)
                  ·
                    refine ⟨9361139838197882045058301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12481519784263842726744401 9361139838197882045058301)
                    ·
                      refine ⟨3510427439324205766896863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9361139838197882045058301 3510427439324205766896863)
                      ·
                        rfl

theorem cell23_6836533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 1, 3, 2, 3].length) (baseStart_6836533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6836533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6836533 prefixEnd_6836533 := by exact prefixLift 6836533
  have htrace : WordTrace (prefixWord ++ tailWord_6836533) baseStart_6836533 baseEnd_6836533 := by
    simpa [prefixWord, tailWord_6836533, baseEnd_6836533] using wordTrace_append hprefix tailTrace_6836533
  have hstable : (prefixWord ++ tailWord_6836533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6836533).length < 2 ^ (prefixWord ++ tailWord_6836533).sum := by decide
  have hdescent : baseEnd_6836533 < baseStart_6836533 := by decide
  rcases family_descends (prefixWord ++ tailWord_6836533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6836564 : List Nat := [2, 4, 1, 1, 2, 3, 1, 4, 1, 2, 2]
def baseStart_6836564 : Nat := 118140960795 + 6836564 * 2 ^ 59
def prefixEnd_6836564 : Nat := 4983230072969 + 3 ^ 40 * 6836564 * 2
def baseEnd_6836564 : Nat := 3510443357224495145609221

theorem tailTrace_6836564 : CollatzResearch.WordTrace tailWord_6836564 prefixEnd_6836564 3510443357224495145609221 := by
  unfold tailWord_6836564
  simp only [CollatzResearch.WordTrace]
  refine ⟨124674987002151847509774373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166233316002869130013032497 124674987002151847509774373)
  ·
    refine ⟨23376560062903471408082695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124674987002151847509774373 23376560062903471408082695)
    ·
      refine ⟨35064840094355207112124043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23376560062903471408082695 35064840094355207112124043)
      ·
        refine ⟨52597260141532810668186065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35064840094355207112124043 52597260141532810668186065)
        ·
          refine ⟨39447945106149608001139549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52597260141532810668186065 39447945106149608001139549)
          ·
            refine ⟨14792979414806103000427331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39447945106149608001139549 14792979414806103000427331)
            ·
              refine ⟨22189469122209154500640997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14792979414806103000427331 22189469122209154500640997)
              ·
                refine ⟨4160525460414216468870187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22189469122209154500640997 4160525460414216468870187)
                ·
                  refine ⟨6240788190621324703305281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4160525460414216468870187 6240788190621324703305281)
                  ·
                    refine ⟨4680591142965993527478961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6240788190621324703305281 4680591142965993527478961)
                    ·
                      refine ⟨3510443357224495145609221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4680591142965993527478961 3510443357224495145609221)
                      ·
                        rfl

theorem cell23_6836564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 4, 1, 2, 2].length) (baseStart_6836564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6836564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6836564 prefixEnd_6836564 := by exact prefixLift 6836564
  have htrace : WordTrace (prefixWord ++ tailWord_6836564) baseStart_6836564 baseEnd_6836564 := by
    simpa [prefixWord, tailWord_6836564, baseEnd_6836564] using wordTrace_append hprefix tailTrace_6836564
  have hstable : (prefixWord ++ tailWord_6836564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6836564).length < 2 ^ (prefixWord ++ tailWord_6836564).sum := by decide
  have hdescent : baseEnd_6836564 < baseStart_6836564 := by decide
  rcases family_descends (prefixWord ++ tailWord_6836564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6836580 : List Nat := [2, 3, 1, 1, 3, 1, 1, 5, 2, 1, 3]
def baseStart_6836580 : Nat := 118140960795 + 6836580 * 2 ^ 59
def prefixEnd_6836580 : Nat := 4983230072969 + 3 ^ 40 * 6836580 * 2
def baseEnd_6836580 : Nat := 3510451572914967083009147

theorem tailTrace_6836580 : CollatzResearch.WordTrace tailWord_6836580 prefixEnd_6836580 3510451572914967083009147 := by
  unfold tailWord_6836580
  simp only [CollatzResearch.WordTrace]
  refine ⟨124675278786122864876065597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166233705048163819834754129 124675278786122864876065597)
  ·
    refine ⟨46753229544796074328524599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124675278786122864876065597 46753229544796074328524599)
    ·
      refine ⟨70129844317194111492786899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46753229544796074328524599 70129844317194111492786899)
      ·
        refine ⟨105194766475791167239180349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70129844317194111492786899 105194766475791167239180349)
        ·
          refine ⟨39448037428421687714692631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105194766475791167239180349 39448037428421687714692631)
          ·
            refine ⟨59172056142632531572038947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39448037428421687714692631 59172056142632531572038947)
            ·
              refine ⟨88758084213948797358058421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59172056142632531572038947 88758084213948797358058421)
              ·
                refine ⟨8321070395057699752317977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 88758084213948797358058421 8321070395057699752317977)
                ·
                  refine ⟨6240802796293274814238483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8321070395057699752317977 6240802796293274814238483)
                  ·
                    refine ⟨9361204194439912221357725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6240802796293274814238483 9361204194439912221357725)
                    ·
                      refine ⟨3510451572914967083009147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9361204194439912221357725 3510451572914967083009147)
                      ·
                        rfl

theorem cell23_6836580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 5, 2, 1, 3].length) (baseStart_6836580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6836580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6836580 prefixEnd_6836580 := by exact prefixLift 6836580
  have htrace : WordTrace (prefixWord ++ tailWord_6836580) baseStart_6836580 baseEnd_6836580 := by
    simpa [prefixWord, tailWord_6836580, baseEnd_6836580] using wordTrace_append hprefix tailTrace_6836580
  have hstable : (prefixWord ++ tailWord_6836580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6836580).length < 2 ^ (prefixWord ++ tailWord_6836580).sum := by decide
  have hdescent : baseEnd_6836580 < baseStart_6836580 := by decide
  rcases family_descends (prefixWord ++ tailWord_6836580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6836598 : List Nat := [5, 1, 1, 4, 1, 1, 2, 3, 1, 2, 2]
def baseStart_6836598 : Nat := 118140960795 + 6836598 * 2 ^ 59
def prefixEnd_6836598 : Nat := 4983230072969 + 3 ^ 40 * 6836598 * 2
def baseEnd_6836598 : Nat := 3510460815566748012584065

theorem tailTrace_6836598 : CollatzResearch.WordTrace tailWord_6836598 prefixEnd_6836598 3510460815566748012584065 := by
  unfold tailWord_6836598
  simp only [CollatzResearch.WordTrace]
  refine ⟨15584450880386282426642903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 166234142724120345884190965 15584450880386282426642903)
  ·
    refine ⟨23376676320579423639964355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15584450880386282426642903 23376676320579423639964355)
    ·
      refine ⟨35065014480869135459946533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23376676320579423639964355 35065014480869135459946533)
      ·
        refine ⟨6574690215162962898739975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35065014480869135459946533 6574690215162962898739975)
        ·
          refine ⟨9862035322744444348109963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6574690215162962898739975 9862035322744444348109963)
          ·
            refine ⟨14793052984116666522164945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9862035322744444348109963 14793052984116666522164945)
            ·
              refine ⟨11094789738087499891623709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14793052984116666522164945 11094789738087499891623709)
              ·
                refine ⟨4160546151782812459358891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11094789738087499891623709 4160546151782812459358891)
                ·
                  refine ⟨6240819227674218689038337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4160546151782812459358891 6240819227674218689038337)
                  ·
                    refine ⟨4680614420755664016778753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6240819227674218689038337 4680614420755664016778753)
                    ·
                      refine ⟨3510460815566748012584065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4680614420755664016778753 3510460815566748012584065)
                      ·
                        rfl

theorem cell23_6836598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_6836598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6836598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6836598 prefixEnd_6836598 := by exact prefixLift 6836598
  have htrace : WordTrace (prefixWord ++ tailWord_6836598) baseStart_6836598 baseEnd_6836598 := by
    simpa [prefixWord, tailWord_6836598, baseEnd_6836598] using wordTrace_append hprefix tailTrace_6836598
  have hstable : (prefixWord ++ tailWord_6836598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6836598).length < 2 ^ (prefixWord ++ tailWord_6836598).sum := by decide
  have hdescent : baseEnd_6836598 < baseStart_6836598 := by decide
  rcases family_descends (prefixWord ++ tailWord_6836598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6836666 : List Nat := [3, 1, 1, 1, 2, 1, 1, 2, 3, 1, 7]
def baseStart_6836666 : Nat := 118140960795 + 6836666 * 2 ^ 59
def prefixEnd_6836666 : Nat := 4983230072969 + 3 ^ 40 * 6836666 * 2
def baseEnd_6836666 : Nat := 3510495732251253746533751

theorem tailTrace_6836666 : CollatzResearch.WordTrace tailWord_6836666 prefixEnd_6836666 3510495732251253746533751 := by
  unfold tailWord_6836666
  simp only [CollatzResearch.WordTrace]
  refine ⟨62338423562483541609940463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166235796166622777626507901 62338423562483541609940463)
  ·
    refine ⟨93507635343725312414910695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62338423562483541609940463 93507635343725312414910695)
    ·
      refine ⟨140261453015587968622366043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93507635343725312414910695 140261453015587968622366043)
      ·
        refine ⟨210392179523381952933549065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140261453015587968622366043 210392179523381952933549065)
        ·
          refine ⟨157794134642536464700161799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210392179523381952933549065 157794134642536464700161799)
          ·
            refine ⟨236691201963804697050242699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157794134642536464700161799 236691201963804697050242699)
            ·
              refine ⟨355036802945707045575364049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 236691201963804697050242699 355036802945707045575364049)
              ·
                refine ⟨266277602209280284181523037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 355036802945707045575364049 266277602209280284181523037)
                ·
                  refine ⟨99854100828480106568071139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 266277602209280284181523037 99854100828480106568071139)
                  ·
                    refine ⟨149781151242720159852106709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 99854100828480106568071139 149781151242720159852106709)
                    ·
                      refine ⟨3510495732251253746533751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 149781151242720159852106709 3510495732251253746533751)
                      ·
                        rfl

theorem cell23_6836666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 3, 1, 7].length) (baseStart_6836666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6836666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6836666 prefixEnd_6836666 := by exact prefixLift 6836666
  have htrace : WordTrace (prefixWord ++ tailWord_6836666) baseStart_6836666 baseEnd_6836666 := by
    simpa [prefixWord, tailWord_6836666, baseEnd_6836666] using wordTrace_append hprefix tailTrace_6836666
  have hstable : (prefixWord ++ tailWord_6836666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6836666).length < 2 ^ (prefixWord ++ tailWord_6836666).sum := by decide
  have hdescent : baseEnd_6836666 < baseStart_6836666 := by decide
  rcases family_descends (prefixWord ++ tailWord_6836666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6836750 : List Nat := [4, 1, 1, 2, 3, 1, 2, 3, 6]
def baseStart_6836750 : Nat := 118140960795 + 6836750 * 2 ^ 59
def prefixEnd_6836750 : Nat := 4983230072969 + 3 ^ 40 * 6836750 * 2
def baseEnd_6836750 : Nat := 390059873847359046431485

theorem tailTrace_6836750 : CollatzResearch.WordTrace tailWord_6836750 prefixEnd_6836750 390059873847359046431485 := by
  unfold tailWord_6836750
  simp only [CollatzResearch.WordTrace]
  refine ⟨31169594747703731098227463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166237838654419899190546469 31169594747703731098227463)
  ·
    refine ⟨46754392121555596647341195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31169594747703731098227463 46754392121555596647341195)
    ·
      refine ⟨70131588182333394971011793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46754392121555596647341195 70131588182333394971011793)
      ·
        refine ⟨52598691136750046228258845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70131588182333394971011793 52598691136750046228258845)
        ·
          refine ⟨19724509176281267335597067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52598691136750046228258845 19724509176281267335597067)
          ·
            refine ⟨29586763764421901003395601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19724509176281267335597067 29586763764421901003395601)
            ·
              refine ⟨22190072823316425752546701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29586763764421901003395601 22190072823316425752546701)
              ·
                refine ⟨8321277308743659657205013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22190072823316425752546701 8321277308743659657205013)
                ·
                  refine ⟨390059873847359046431485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8321277308743659657205013 390059873847359046431485)
                  ·
                    rfl

theorem cell23_6836750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 3, 6].length) (baseStart_6836750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6836750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6836750 prefixEnd_6836750 := by exact prefixLift 6836750
  have htrace : WordTrace (prefixWord ++ tailWord_6836750) baseStart_6836750 baseEnd_6836750 := by
    simpa [prefixWord, tailWord_6836750, baseEnd_6836750] using wordTrace_append hprefix tailTrace_6836750
  have hstable : (prefixWord ++ tailWord_6836750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6836750).length < 2 ^ (prefixWord ++ tailWord_6836750).sum := by decide
  have hdescent : baseEnd_6836750 < baseStart_6836750 := by decide
  rcases family_descends (prefixWord ++ tailWord_6836750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6836794 : List Nat := [3, 1, 1, 1, 3, 3, 2, 4, 1, 1, 3]
def baseStart_6836794 : Nat := 118140960795 + 6836794 * 2 ^ 59
def prefixEnd_6836794 : Nat := 4983230072969 + 3 ^ 40 * 6836794 * 2
def baseEnd_6836794 : Nat := 3510561457775029245733163

theorem tailTrace_6836794 : CollatzResearch.WordTrace tailWord_6836794 prefixEnd_6836794 3510561457775029245733163 := by
  unfold tailWord_6836794
  simp only [CollatzResearch.WordTrace]
  refine ⟨62339590698367611075105359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166238908528980296200280957 62339590698367611075105359)
  ·
    refine ⟨93509386047551416612658039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62339590698367611075105359 93509386047551416612658039)
    ·
      refine ⟨140264079071327124918987059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93509386047551416612658039 140264079071327124918987059)
      ·
        refine ⟨210396118606990687378480589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140264079071327124918987059 210396118606990687378480589)
        ·
          refine ⟨78898544477621507766930221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 210396118606990687378480589 78898544477621507766930221)
          ·
            refine ⟨29586954179108065412598833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78898544477621507766930221 29586954179108065412598833)
            ·
              refine ⟨22190215634331049059449125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29586954179108065412598833 22190215634331049059449125)
              ·
                refine ⟨4160665431437071698646711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22190215634331049059449125 4160665431437071698646711)
                ·
                  refine ⟨6240998147155607547970067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4160665431437071698646711 6240998147155607547970067)
                  ·
                    refine ⟨9361497220733411321955101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6240998147155607547970067 9361497220733411321955101)
                    ·
                      refine ⟨3510561457775029245733163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9361497220733411321955101 3510561457775029245733163)
                      ·
                        rfl

theorem cell23_6836794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 4, 1, 1, 3].length) (baseStart_6836794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6836794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6836794 prefixEnd_6836794 := by exact prefixLift 6836794
  have htrace : WordTrace (prefixWord ++ tailWord_6836794) baseStart_6836794 baseEnd_6836794 := by
    simpa [prefixWord, tailWord_6836794, baseEnd_6836794] using wordTrace_append hprefix tailTrace_6836794
  have hstable : (prefixWord ++ tailWord_6836794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6836794).length < 2 ^ (prefixWord ++ tailWord_6836794).sum := by decide
  have hdescent : baseEnd_6836794 < baseStart_6836794 := by decide
  rcases family_descends (prefixWord ++ tailWord_6836794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6836810 : List Nat := [3, 1, 2, 1, 1, 4, 3, 1, 1, 6]
def baseStart_6836810 : Nat := 118140960795 + 6836810 * 2 ^ 59
def prefixEnd_6836810 : Nat := 4983230072969 + 3 ^ 40 * 6836810 * 2
def baseEnd_6836810 : Nat := 1170189891155167061044363

theorem tailTrace_6836810 : CollatzResearch.WordTrace tailWord_6836810 prefixEnd_6836810 1170189891155167061044363 := by
  unfold tailWord_6836810
  simp only [CollatzResearch.WordTrace]
  refine ⟨62339736590353119758250971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166239297574274986022002589 62339736590353119758250971)
  ·
    refine ⟨93509604885529679637376457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62339736590353119758250971 93509604885529679637376457)
    ·
      refine ⟨70132203664147259728032343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93509604885529679637376457 70132203664147259728032343)
      ·
        refine ⟨105198305496220889592048515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70132203664147259728032343 105198305496220889592048515)
        ·
          refine ⟨157797458244331334388072773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105198305496220889592048515 157797458244331334388072773)
          ·
            refine ⟨29587023420812125197763645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 157797458244331334388072773 29587023420812125197763645)
            ·
              refine ⟨11095133782804546949161367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29587023420812125197763645 11095133782804546949161367)
              ·
                refine ⟨16642700674206820423742051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11095133782804546949161367 16642700674206820423742051)
                ·
                  refine ⟨24964051011310230635613077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16642700674206820423742051 24964051011310230635613077)
                  ·
                    refine ⟨1170189891155167061044363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24964051011310230635613077 1170189891155167061044363)
                    ·
                      rfl

theorem cell23_6836810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 1, 1, 6].length) (baseStart_6836810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6836810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6836810 prefixEnd_6836810 := by exact prefixLift 6836810
  have htrace : WordTrace (prefixWord ++ tailWord_6836810) baseStart_6836810 baseEnd_6836810 := by
    simpa [prefixWord, tailWord_6836810, baseEnd_6836810] using wordTrace_append hprefix tailTrace_6836810
  have hstable : (prefixWord ++ tailWord_6836810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6836810).length < 2 ^ (prefixWord ++ tailWord_6836810).sum := by decide
  have hdescent : baseEnd_6836810 < baseStart_6836810 := by decide
  rcases family_descends (prefixWord ++ tailWord_6836810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6836817 : List Nat := [1, 2, 2, 1, 3, 4, 2, 2, 1, 1, 4]
def baseStart_6836817 : Nat := 118140960795 + 6836817 * 2 ^ 59
def prefixEnd_6836817 : Nat := 4983230072969 + 3 ^ 40 * 6836817 * 2
def baseEnd_6836817 : Nat := 3510573267830082655745557

theorem tailTrace_6836817 : CollatzResearch.WordTrace tailWord_6836817 prefixEnd_6836817 3510573267830082655745557 := by
  unfold tailWord_6836817
  simp only [CollatzResearch.WordTrace]
  refine ⟨249359201672387119228508705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166239467781591412819005803 249359201672387119228508705)
  ·
    refine ⟨187019401254290339421381529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249359201672387119228508705 187019401254290339421381529)
    ·
      refine ⟨140264550940717754566036147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187019401254290339421381529 140264550940717754566036147)
      ·
        refine ⟨210396826411076631849054221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140264550940717754566036147 210396826411076631849054221)
        ·
          refine ⟨78898809904153736943395333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 210396826411076631849054221 78898809904153736943395333)
          ·
            refine ⟨14793526857028825676886625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78898809904153736943395333 14793526857028825676886625)
            ·
              refine ⟨11095145142771619257664969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14793526857028825676886625 11095145142771619257664969)
              ·
                refine ⟨8321358857078714443248727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11095145142771619257664969 8321358857078714443248727)
                ·
                  refine ⟨12482038285618071664873091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8321358857078714443248727 12482038285618071664873091)
                  ·
                    refine ⟨18723057428427107497309637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12482038285618071664873091 18723057428427107497309637)
                    ·
                      refine ⟨3510573267830082655745557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18723057428427107497309637 3510573267830082655745557)
                      ·
                        rfl

theorem cell23_6836817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 2, 1, 1, 4].length) (baseStart_6836817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6836817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6836817 prefixEnd_6836817 := by exact prefixLift 6836817
  have htrace : WordTrace (prefixWord ++ tailWord_6836817) baseStart_6836817 baseEnd_6836817 := by
    simpa [prefixWord, tailWord_6836817, baseEnd_6836817] using wordTrace_append hprefix tailTrace_6836817
  have hstable : (prefixWord ++ tailWord_6836817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6836817).length < 2 ^ (prefixWord ++ tailWord_6836817).sum := by decide
  have hdescent : baseEnd_6836817 < baseStart_6836817 := by decide
  rcases family_descends (prefixWord ++ tailWord_6836817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6836823 : List Nat := [1, 1, 3, 2, 2, 2, 3, 9]
def baseStart_6836823 : Nat := 118140960795 + 6836823 * 2 ^ 59
def prefixEnd_6836823 : Nat := 4983230072969 + 3 ^ 40 * 6836823 * 2
def baseEnd_6836823 : Nat := 130021346248667023417427

theorem tailTrace_6836823 : CollatzResearch.WordTrace tailWord_6836823 prefixEnd_6836823 130021346248667023417427 := by
  unfold tailWord_6836823
  simp only [CollatzResearch.WordTrace]
  refine ⟨249359420510365382253227123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166239613673576921502151415 249359420510365382253227123)
  ·
    refine ⟨374039130765548073379840685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249359420510365382253227123 374039130765548073379840685)
    ·
      refine ⟨140264674037080527517440257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 374039130765548073379840685 140264674037080527517440257)
      ·
        refine ⟨105198505527810395638080193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140264674037080527517440257 105198505527810395638080193)
        ·
          refine ⟨78898879145857796728560145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105198505527810395638080193 78898879145857796728560145)
          ·
            refine ⟨59174159359393347546420109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78898879145857796728560145 59174159359393347546420109)
            ·
              refine ⟨22190309759772505329907541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59174159359393347546420109 22190309759772505329907541)
              ·
                refine ⟨130021346248667023417427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22190309759772505329907541 130021346248667023417427)
                ·
                  rfl

theorem cell23_6836823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 9].length) (baseStart_6836823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6836823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6836823 prefixEnd_6836823 := by exact prefixLift 6836823
  have htrace : WordTrace (prefixWord ++ tailWord_6836823) baseStart_6836823 baseEnd_6836823 := by
    simpa [prefixWord, tailWord_6836823, baseEnd_6836823] using wordTrace_append hprefix tailTrace_6836823
  have hstable : (prefixWord ++ tailWord_6836823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6836823).length < 2 ^ (prefixWord ++ tailWord_6836823).sum := by decide
  have hdescent : baseEnd_6836823 < baseStart_6836823 := by decide
  rcases family_descends (prefixWord ++ tailWord_6836823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6836828 : List Nat := [2, 2, 4, 1, 3, 2, 1, 3, 1, 1, 3]
def baseStart_6836828 : Nat := 118140960795 + 6836828 * 2 ^ 59
def prefixEnd_6836828 : Nat := 4983230072969 + 3 ^ 40 * 6836828 * 2
def baseEnd_6836828 : Nat := 3510578916117282112708007

theorem tailTrace_6836828 : CollatzResearch.WordTrace tailWord_6836828 prefixEnd_6836828 3510578916117282112708007 := by
  unfold tailWord_6836828
  simp only [CollatzResearch.WordTrace]
  refine ⟨124679801437673634053579569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166239735250231512071439425 124679801437673634053579569)
  ·
    refine ⟨93509851078255225540184677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124679801437673634053579569 93509851078255225540184677)
    ·
      refine ⟨17533097077172854788784627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93509851078255225540184677 17533097077172854788784627)
      ·
        refine ⟨26299645615759282183176941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17533097077172854788784627 26299645615759282183176941)
        ·
          refine ⟨9862367105909730818691353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26299645615759282183176941 9862367105909730818691353)
          ·
            refine ⟨7396775329432298114018515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9862367105909730818691353 7396775329432298114018515)
            ·
              refine ⟨11095162994148447171027773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7396775329432298114018515 11095162994148447171027773)
              ·
                refine ⟨4160686122805667689135415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11095162994148447171027773 4160686122805667689135415)
                ·
                  refine ⟨6241029184208501533703123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4160686122805667689135415 6241029184208501533703123)
                  ·
                    refine ⟨9361543776312752300554685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6241029184208501533703123 9361543776312752300554685)
                    ·
                      refine ⟨3510578916117282112708007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9361543776312752300554685 3510578916117282112708007)
                      ·
                        rfl

theorem cell23_6836828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 3, 1, 1, 3].length) (baseStart_6836828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6836828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6836828 prefixEnd_6836828 := by exact prefixLift 6836828
  have htrace : WordTrace (prefixWord ++ tailWord_6836828) baseStart_6836828 baseEnd_6836828 := by
    simpa [prefixWord, tailWord_6836828, baseEnd_6836828] using wordTrace_append hprefix tailTrace_6836828
  have hstable : (prefixWord ++ tailWord_6836828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6836828).length < 2 ^ (prefixWord ++ tailWord_6836828).sum := by decide
  have hdescent : baseEnd_6836828 < baseStart_6836828 := by decide
  rcases family_descends (prefixWord ++ tailWord_6836828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6836837 : List Nat := [1, 3, 1, 3, 4, 1, 2, 1, 1, 1, 5]
def baseStart_6836837 : Nat := 118140960795 + 6836837 * 2 ^ 59
def prefixEnd_6836837 : Nat := 4983230072969 + 3 ^ 40 * 6836837 * 2
def baseEnd_6836837 : Nat := 3510583537443172577495465

theorem tailTrace_6836837 : CollatzResearch.WordTrace tailWord_6836837 prefixEnd_6836837 3510583537443172577495465 := by
  unfold tailWord_6836837
  simp only [CollatzResearch.WordTrace]
  refine ⟨249359931132314662644236765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166239954088209775096157843 249359931132314662644236765)
  ·
    refine ⟨93509974174617998491588787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249359931132314662644236765 93509974174617998491588787)
    ·
      refine ⟨140264961261926997737383181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93509974174617998491588787 140264961261926997737383181)
      ·
        refine ⟨52599360473222624151518693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140264961261926997737383181 52599360473222624151518693)
        ·
          refine ⟨9862380088729242028409755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52599360473222624151518693 9862380088729242028409755)
          ·
            refine ⟨14793570133093863042614633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9862380088729242028409755 14793570133093863042614633)
            ·
              refine ⟨11095177599820397281960975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14793570133093863042614633 11095177599820397281960975)
              ·
                refine ⟨16642766399730595922941463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11095177599820397281960975 16642766399730595922941463)
                ·
                  refine ⟨24964149599595893884412195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16642766399730595922941463 24964149599595893884412195)
                  ·
                    refine ⟨37446224399393840826618293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24964149599595893884412195 37446224399393840826618293)
                    ·
                      refine ⟨3510583537443172577495465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37446224399393840826618293 3510583537443172577495465)
                      ·
                        rfl

theorem cell23_6836837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 1, 1, 1, 5].length) (baseStart_6836837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6836837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6836837 prefixEnd_6836837 := by exact prefixLift 6836837
  have htrace : WordTrace (prefixWord ++ tailWord_6836837) baseStart_6836837 baseEnd_6836837 := by
    simpa [prefixWord, tailWord_6836837, baseEnd_6836837] using wordTrace_append hprefix tailTrace_6836837
  have hstable : (prefixWord ++ tailWord_6836837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6836837).length < 2 ^ (prefixWord ++ tailWord_6836837).sum := by decide
  have hdescent : baseEnd_6836837 < baseStart_6836837 := by decide
  rcases family_descends (prefixWord ++ tailWord_6836837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6836861 : List Nat := [1, 4, 1, 1, 5, 2, 2, 1, 2, 4]
def baseStart_6836861 : Nat := 118140960795 + 6836861 * 2 ^ 59
def prefixEnd_6836861 : Nat := 4983230072969 + 3 ^ 40 * 6836861 * 2
def baseEnd_6836861 : Nat := 1170198620326293494531785

theorem tailTrace_6836861 : CollatzResearch.WordTrace tailWord_6836861 prefixEnd_6836861 1170198620326293494531785 := by
  unfold tailWord_6836861
  simp only [CollatzResearch.WordTrace]
  refine ⟨249360806484227714743110437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166240537656151809828740291 249360806484227714743110437)
  ·
    refine ⟨46755151215792696514333207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 249360806484227714743110437 46755151215792696514333207)
    ·
      refine ⟨70132726823689044771499811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46755151215792696514333207 70132726823689044771499811)
      ·
        refine ⟨105199090235533567157249717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70132726823689044771499811 105199090235533567157249717)
        ·
          refine ⟨9862414709581271920992161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 105199090235533567157249717 9862414709581271920992161)
          ·
            refine ⟨7396811032185953940744121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9862414709581271920992161 7396811032185953940744121)
            ·
              refine ⟨5547608274139465455558091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7396811032185953940744121 5547608274139465455558091)
              ·
                refine ⟨8321412411209198183337137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5547608274139465455558091 8321412411209198183337137)
                ·
                  refine ⟨6241059308406898637502853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8321412411209198183337137 6241059308406898637502853)
                  ·
                    refine ⟨1170198620326293494531785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6241059308406898637502853 1170198620326293494531785)
                    ·
                      rfl

theorem cell23_6836861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 2, 1, 2, 4].length) (baseStart_6836861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6836861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6836861 prefixEnd_6836861 := by exact prefixLift 6836861
  have htrace : WordTrace (prefixWord ++ tailWord_6836861) baseStart_6836861 baseEnd_6836861 := by
    simpa [prefixWord, tailWord_6836861, baseEnd_6836861] using wordTrace_append hprefix tailTrace_6836861
  have hstable : (prefixWord ++ tailWord_6836861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6836861).length < 2 ^ (prefixWord ++ tailWord_6836861).sum := by decide
  have hdescent : baseEnd_6836861 < baseStart_6836861 := by decide
  rcases family_descends (prefixWord ++ tailWord_6836861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6836863 : List Nat := [1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 5]
def baseStart_6836863 : Nat := 118140960795 + 6836863 * 2 ^ 59
def prefixEnd_6836863 : Nat := 4983230072969 + 3 ^ 40 * 6836863 * 2
def baseEnd_6836863 : Nat := 3510596887940189475770345

theorem tailTrace_6836863 : CollatzResearch.WordTrace tailWord_6836863 prefixEnd_6836863 3510596887940189475770345 := by
  unfold tailWord_6836863
  simp only [CollatzResearch.WordTrace]
  refine ⟨249360879430220469084683243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166240586286813646056455495 249360879430220469084683243)
  ·
    refine ⟨374041319145330703627024865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249360879430220469084683243 374041319145330703627024865)
    ·
      refine ⟨280530989358998027720268649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 374041319145330703627024865 280530989358998027720268649)
      ·
        refine ⟨210398242019248520790201487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280530989358998027720268649 210398242019248520790201487)
        ·
          refine ⟨315597363028872781185302231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210398242019248520790201487 315597363028872781185302231)
          ·
            refine ⟨473396044543309171777953347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315597363028872781185302231 473396044543309171777953347)
            ·
              refine ⟨710094066814963757666930021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 473396044543309171777953347 710094066814963757666930021)
              ·
                refine ⟨133142637527805704562549379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 710094066814963757666930021 133142637527805704562549379)
                ·
                  refine ⟨199713956291708556843824069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133142637527805704562549379 199713956291708556843824069)
                  ·
                    refine ⟨37446366804695354408217013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 199713956291708556843824069 37446366804695354408217013)
                    ·
                      refine ⟨3510596887940189475770345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37446366804695354408217013 3510596887940189475770345)
                      ·
                        rfl

theorem cell23_6836863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 5].length) (baseStart_6836863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6836863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6836863 prefixEnd_6836863 := by exact prefixLift 6836863
  have htrace : WordTrace (prefixWord ++ tailWord_6836863) baseStart_6836863 baseEnd_6836863 := by
    simpa [prefixWord, tailWord_6836863, baseEnd_6836863] using wordTrace_append hprefix tailTrace_6836863
  have hstable : (prefixWord ++ tailWord_6836863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6836863).length < 2 ^ (prefixWord ++ tailWord_6836863).sum := by decide
  have hdescent : baseEnd_6836863 < baseStart_6836863 := by decide
  rcases family_descends (prefixWord ++ tailWord_6836863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6836873 : List Nat := [1, 2, 1, 1, 4, 1, 1, 1, 1, 2, 8]
def baseStart_6836873 : Nat := 118140960795 + 6836873 * 2 ^ 59
def prefixEnd_6836873 : Nat := 4983230072969 + 3 ^ 40 * 6836873 * 2
def baseEnd_6836873 : Nat := 3510602022746734436645299

theorem tailTrace_6836873 : CollatzResearch.WordTrace tailWord_6836873 prefixEnd_6836873 3510602022746734436645299 := by
  unfold tailWord_6836873
  simp only [CollatzResearch.WordTrace]
  refine ⟨249361244160184240792547273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166240829440122827195031515 249361244160184240792547273)
  ·
    refine ⟨187020933120138180594410455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249361244160184240792547273 187020933120138180594410455)
    ·
      refine ⟨280531399680207270891615683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187020933120138180594410455 280531399680207270891615683)
      ·
        refine ⟨420797099520310906337423525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280531399680207270891615683 420797099520310906337423525)
        ·
          refine ⟨78899456160058294938266911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 420797099520310906337423525 78899456160058294938266911)
          ·
            refine ⟨118349184240087442407400367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78899456160058294938266911 118349184240087442407400367)
            ·
              refine ⟨177523776360131163611100551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118349184240087442407400367 177523776360131163611100551)
              ·
                refine ⟨266285664540196745416650827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177523776360131163611100551 266285664540196745416650827)
                ·
                  refine ⟨399428496810295118124976241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 266285664540196745416650827 399428496810295118124976241)
                  ·
                    refine ⟨299571372607721338593732181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 399428496810295118124976241 299571372607721338593732181)
                    ·
                      refine ⟨3510602022746734436645299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 299571372607721338593732181 3510602022746734436645299)
                      ·
                        rfl

theorem cell23_6836873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 2, 8].length) (baseStart_6836873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6836873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6836873 prefixEnd_6836873 := by exact prefixLift 6836873
  have htrace : WordTrace (prefixWord ++ tailWord_6836873) baseStart_6836873 baseEnd_6836873 := by
    simpa [prefixWord, tailWord_6836873, baseEnd_6836873] using wordTrace_append hprefix tailTrace_6836873
  have hstable : (prefixWord ++ tailWord_6836873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6836873).length < 2 ^ (prefixWord ++ tailWord_6836873).sum := by decide
  have hdescent : baseEnd_6836873 < baseStart_6836873 := by decide
  rcases family_descends (prefixWord ++ tailWord_6836873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6836883 : List Nat := [1, 1, 1, 2, 1, 2, 2, 4, 1, 8]
def baseStart_6836883 : Nat := 118140960795 + 6836883 * 2 ^ 59
def prefixEnd_6836883 : Nat := 4983230072969 + 3 ^ 40 * 6836883 * 2
def baseEnd_6836883 : Nat := 1170202385851093132506751

theorem tailTrace_6836883 : CollatzResearch.WordTrace tailWord_6836883 prefixEnd_6836883 1170202385851093132506751 := by
  unfold tailWord_6836883
  simp only [CollatzResearch.WordTrace]
  refine ⟨249361608890148012500411303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166241072593432008333607535 249361608890148012500411303)
  ·
    refine ⟨374042413335222018750616955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249361608890148012500411303 374042413335222018750616955)
    ·
      refine ⟨561063620002833028125925433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374042413335222018750616955 561063620002833028125925433)
      ·
        refine ⟨420797715002124771094444075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 561063620002833028125925433 420797715002124771094444075)
        ·
          refine ⟨631196572503187156641666113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 420797715002124771094444075 631196572503187156641666113)
          ·
            refine ⟨473397429377390367481249585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 631196572503187156641666113 473397429377390367481249585)
            ·
              refine ⟨355048072033042775610937189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 473397429377390367481249585 355048072033042775610937189)
              ·
                refine ⟨66571513506195520427050723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 355048072033042775610937189 66571513506195520427050723)
                ·
                  refine ⟨99857270259293280640576085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66571513506195520427050723 99857270259293280640576085)
                  ·
                    refine ⟨1170202385851093132506751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 99857270259293280640576085 1170202385851093132506751)
                    ·
                      rfl

theorem cell23_6836883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 8].length) (baseStart_6836883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6836883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6836883 prefixEnd_6836883 := by exact prefixLift 6836883
  have htrace : WordTrace (prefixWord ++ tailWord_6836883) baseStart_6836883 baseEnd_6836883 := by
    simpa [prefixWord, tailWord_6836883, baseEnd_6836883] using wordTrace_append hprefix tailTrace_6836883
  have hstable : (prefixWord ++ tailWord_6836883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6836883).length < 2 ^ (prefixWord ++ tailWord_6836883).sum := by decide
  have hdescent : baseEnd_6836883 < baseStart_6836883 := by decide
  rcases family_descends (prefixWord ++ tailWord_6836883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6836884 : List Nat := [2, 4, 2, 2, 1, 2, 1, 2, 1, 3, 3]
def baseStart_6836884 : Nat := 118140960795 + 6836884 * 2 ^ 59
def prefixEnd_6836884 : Nat := 4983230072969 + 3 ^ 40 * 6836884 * 2
def baseEnd_6836884 : Nat := 3510607671033933893607749

theorem tailTrace_6836884 : CollatzResearch.WordTrace tailWord_6836884 prefixEnd_6836884 3510607671033933893607749 := by
  unfold tailWord_6836884
  simp only [CollatzResearch.WordTrace]
  refine ⟨124680822681572194835598853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166241096908762926447465137 124680822681572194835598853)
  ·
    refine ⟨23377654252794786531674785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124680822681572194835598853 23377654252794786531674785)
    ·
      refine ⟨17533240689596089898756089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23377654252794786531674785 17533240689596089898756089)
      ·
        refine ⟨13149930517197067424067067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17533240689596089898756089 13149930517197067424067067)
        ·
          refine ⟨19724895775795601136100601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13149930517197067424067067 19724895775795601136100601)
          ·
            refine ⟨14793671831846700852075451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19724895775795601136100601 14793671831846700852075451)
            ·
              refine ⟨22190507747770051278113177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14793671831846700852075451 22190507747770051278113177)
              ·
                refine ⟨16642880810827538458584883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22190507747770051278113177 16642880810827538458584883)
                ·
                  refine ⟨24964321216241307687877325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16642880810827538458584883 24964321216241307687877325)
                  ·
                    refine ⟨9361620456090490382953997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24964321216241307687877325 9361620456090490382953997)
                    ·
                      refine ⟨3510607671033933893607749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9361620456090490382953997 3510607671033933893607749)
                      ·
                        rfl

theorem cell23_6836884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_6836884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6836884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6836884 prefixEnd_6836884 := by exact prefixLift 6836884
  have htrace : WordTrace (prefixWord ++ tailWord_6836884) baseStart_6836884 baseEnd_6836884 := by
    simpa [prefixWord, tailWord_6836884, baseEnd_6836884] using wordTrace_append hprefix tailTrace_6836884
  have hstable : (prefixWord ++ tailWord_6836884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6836884).length < 2 ^ (prefixWord ++ tailWord_6836884).sum := by decide
  have hdescent : baseEnd_6836884 < baseStart_6836884 := by decide
  rcases family_descends (prefixWord ++ tailWord_6836884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6836900 : List Nat := [2, 3, 1, 2, 2, 1, 2, 2, 2, 6]
def baseStart_6836900 : Nat := 118140960795 + 6836900 * 2 ^ 59
def prefixEnd_6836900 : Nat := 4983230072969 + 3 ^ 40 * 6836900 * 2
def baseEnd_6836900 : Nat := 1170205295574801943669225

theorem tailTrace_6836900 : CollatzResearch.WordTrace tailWord_6836900 prefixEnd_6836900 1170205295574801943669225 := by
  unfold tailWord_6836900
  simp only [CollatzResearch.WordTrace]
  refine ⟨124681114465543212201890077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166241485954057616269186769 124681114465543212201890077)
  ·
    refine ⟨46755417924578704575708779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124681114465543212201890077 46755417924578704575708779)
    ·
      refine ⟨70133126886868056863563169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46755417924578704575708779 70133126886868056863563169)
      ·
        refine ⟨52599845165151042647672377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70133126886868056863563169 52599845165151042647672377)
        ·
          refine ⟨39449883873863281985754283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52599845165151042647672377 39449883873863281985754283)
          ·
            refine ⟨59174825810794922978631425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39449883873863281985754283 59174825810794922978631425)
            ·
              refine ⟨44381119358096192233973569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59174825810794922978631425 44381119358096192233973569)
              ·
                refine ⟨33285839518572144175480177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44381119358096192233973569 33285839518572144175480177)
                ·
                  refine ⟨24964379638929108131610133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33285839518572144175480177 24964379638929108131610133)
                  ·
                    refine ⟨1170205295574801943669225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24964379638929108131610133 1170205295574801943669225)
                    ·
                      rfl

theorem cell23_6836900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 2, 2, 6].length) (baseStart_6836900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6836900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6836900 prefixEnd_6836900 := by exact prefixLift 6836900
  have htrace : WordTrace (prefixWord ++ tailWord_6836900) baseStart_6836900 baseEnd_6836900 := by
    simpa [prefixWord, tailWord_6836900, baseEnd_6836900] using wordTrace_append hprefix tailTrace_6836900
  have hstable : (prefixWord ++ tailWord_6836900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6836900).length < 2 ^ (prefixWord ++ tailWord_6836900).sum := by decide
  have hdescent : baseEnd_6836900 < baseStart_6836900 := by decide
  rcases family_descends (prefixWord ++ tailWord_6836900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6836917 : List Nat := [1, 3, 3, 3, 1, 2, 1, 1, 2, 6]
def baseStart_6836917 : Nat := 118140960795 + 6836917 * 2 ^ 59
def prefixEnd_6836917 : Nat := 4983230072969 + 3 ^ 40 * 6836917 * 2
def baseEnd_6836917 : Nat := 1170208205298510754831699

theorem tailTrace_6836917 : CollatzResearch.WordTrace tailWord_6836917 prefixEnd_6836917 1170208205298510754831699 := by
  unfold tailWord_6836917
  simp only [CollatzResearch.WordTrace]
  refine ⟨249362848972024836307149005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166241899314683224204766003 249362848972024836307149005)
  ·
    refine ⟨93511068364509313615180877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249362848972024836307149005 93511068364509313615180877)
    ·
      refine ⟨35066650636690992605692829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93511068364509313615180877 35066650636690992605692829)
      ·
        refine ⟨13149993988759122227134811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35066650636690992605692829 13149993988759122227134811)
        ·
          refine ⟨19724990983138683340702217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13149993988759122227134811 19724990983138683340702217)
          ·
            refine ⟨14793743237354012505526663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19724990983138683340702217 14793743237354012505526663)
            ·
              refine ⟨22190614856031018758289995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14793743237354012505526663 22190614856031018758289995)
              ·
                refine ⟨33285922284046528137434993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22190614856031018758289995 33285922284046528137434993)
                ·
                  refine ⟨24964441713034896103076245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33285922284046528137434993 24964441713034896103076245)
                  ·
                    refine ⟨1170208205298510754831699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24964441713034896103076245 1170208205298510754831699)
                    ·
                      rfl

theorem cell23_6836917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 1, 2, 6].length) (baseStart_6836917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6836917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6836917 prefixEnd_6836917 := by exact prefixLift 6836917
  have htrace : WordTrace (prefixWord ++ tailWord_6836917) baseStart_6836917 baseEnd_6836917 := by
    simpa [prefixWord, tailWord_6836917, baseEnd_6836917] using wordTrace_append hprefix tailTrace_6836917
  have hstable : (prefixWord ++ tailWord_6836917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6836917).length < 2 ^ (prefixWord ++ tailWord_6836917).sum := by decide
  have hdescent : baseEnd_6836917 < baseStart_6836917 := by decide
  rcases family_descends (prefixWord ++ tailWord_6836917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6836924 : List Nat := [2, 2, 2, 3, 1, 1, 4, 1, 1, 4, 2]
def baseStart_6836924 : Nat := 118140960795 + 6836924 * 2 ^ 59
def prefixEnd_6836924 : Nat := 4983230072969 + 3 ^ 40 * 6836924 * 2
def baseEnd_6836924 : Nat := 3510628210260113737107565

theorem tailTrace_6836924 : CollatzResearch.WordTrace tailWord_6836924 prefixEnd_6836924 3510628210260113737107565 := by
  unfold tailWord_6836924
  simp only [CollatzResearch.WordTrace]
  refine ⟨124681552141499738251326913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166242069521999651001769217 124681552141499738251326913)
  ·
    refine ⟨93511164106124803688495185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124681552141499738251326913 93511164106124803688495185)
    ·
      refine ⟨70133373079593602766371389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93511164106124803688495185 70133373079593602766371389)
      ·
        refine ⟨26300014904847601037389271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70133373079593602766371389 26300014904847601037389271)
        ·
          refine ⟨39450022357271401556083907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26300014904847601037389271 39450022357271401556083907)
          ·
            refine ⟨59175033535907102334125861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39450022357271401556083907 59175033535907102334125861)
            ·
              refine ⟨11095318787982581687648599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59175033535907102334125861 11095318787982581687648599)
              ·
                refine ⟨16642978181973872531472899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11095318787982581687648599 16642978181973872531472899)
                ·
                  refine ⟨24964467272960808797209349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16642978181973872531472899 24964467272960808797209349)
                  ·
                    refine ⟨4680837613680151649476753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24964467272960808797209349 4680837613680151649476753)
                    ·
                      refine ⟨3510628210260113737107565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4680837613680151649476753 3510628210260113737107565)
                      ·
                        rfl

theorem cell23_6836924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 1, 1, 4, 2].length) (baseStart_6836924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6836924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6836924 prefixEnd_6836924 := by exact prefixLift 6836924
  have htrace : WordTrace (prefixWord ++ tailWord_6836924) baseStart_6836924 baseEnd_6836924 := by
    simpa [prefixWord, tailWord_6836924, baseEnd_6836924] using wordTrace_append hprefix tailTrace_6836924
  have hstable : (prefixWord ++ tailWord_6836924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6836924).length < 2 ^ (prefixWord ++ tailWord_6836924).sum := by decide
  have hdescent : baseEnd_6836924 < baseStart_6836924 := by decide
  rcases family_descends (prefixWord ++ tailWord_6836924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6836960 : List Nat := [2, 1, 1, 3, 1, 2, 1, 3, 4, 5]
def baseStart_6836960 : Nat := 118140960795 + 6836960 * 2 ^ 59
def prefixEnd_6836960 : Nat := 4983230072969 + 3 ^ 40 * 6836960 * 2
def baseEnd_6836960 : Nat := 1170215565187891865419133

theorem tailTrace_6836960 : CollatzResearch.WordTrace tailWord_6836960 prefixEnd_6836960 1170215565187891865419133 := by
  unfold tailWord_6836960
  simp only [CollatzResearch.WordTrace]
  refine ⟨124682208655434527325482167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166242944873912703100642889 124682208655434527325482167)
  ·
    refine ⟨187023312983151790988223251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124682208655434527325482167 187023312983151790988223251)
    ·
      refine ⟨280534969474727686482334877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187023312983151790988223251 280534969474727686482334877)
      ·
        refine ⟨105200613553022882430875579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 280534969474727686482334877 105200613553022882430875579)
        ·
          refine ⟨157800920329534323646313369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105200613553022882430875579 157800920329534323646313369)
          ·
            refine ⟨118350690247150742734735027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157800920329534323646313369 118350690247150742734735027)
            ·
              refine ⟨177526035370726114102102541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118350690247150742734735027 177526035370726114102102541)
              ·
                refine ⟨66572263264022292788288453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 177526035370726114102102541 66572263264022292788288453)
                ·
                  refine ⟨12482299362004179897804085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66572263264022292788288453 12482299362004179897804085)
                  ·
                    refine ⟨1170215565187891865419133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12482299362004179897804085 1170215565187891865419133)
                    ·
                      rfl

theorem cell23_6836960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 4, 5].length) (baseStart_6836960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6836960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6836960 prefixEnd_6836960 := by exact prefixLift 6836960
  have htrace : WordTrace (prefixWord ++ tailWord_6836960) baseStart_6836960 baseEnd_6836960 := by
    simpa [prefixWord, tailWord_6836960, baseEnd_6836960] using wordTrace_append hprefix tailTrace_6836960
  have hstable : (prefixWord ++ tailWord_6836960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6836960).length < 2 ^ (prefixWord ++ tailWord_6836960).sum := by decide
  have hdescent : baseEnd_6836960 < baseStart_6836960 := by decide
  rcases family_descends (prefixWord ++ tailWord_6836960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6836970 : List Nat := [3, 1, 3, 1, 1, 1, 1, 3, 1, 1, 7]
def baseStart_6836970 : Nat := 118140960795 + 6836970 * 2 ^ 59
def prefixEnd_6836970 : Nat := 4983230072969 + 3 ^ 40 * 6836970 * 2
def baseEnd_6836970 : Nat := 3510651830370220557132353

theorem tailTrace_6836970 : CollatzResearch.WordTrace tailWord_6836970 prefixEnd_6836970 3510651830370220557132353 := by
  unfold tailWord_6836970
  simp only [CollatzResearch.WordTrace]
  refine ⟨62341195510208206589707091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166243188027221884239218909 62341195510208206589707091)
  ·
    refine ⟨93511793265312309884560637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62341195510208206589707091 93511793265312309884560637)
    ·
      refine ⟨35066922474492116206710239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93511793265312309884560637 35066922474492116206710239)
      ·
        refine ⟨52600383711738174310065359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35066922474492116206710239 52600383711738174310065359)
        ·
          refine ⟨78900575567607261465098039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52600383711738174310065359 78900575567607261465098039)
          ·
            refine ⟨118350863351410892197647059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78900575567607261465098039 118350863351410892197647059)
            ·
              refine ⟨177526295027116338296470589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118350863351410892197647059 177526295027116338296470589)
              ·
                refine ⟨66572360635168626861176471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 177526295027116338296470589 66572360635168626861176471)
                ·
                  refine ⟨99858540952752940291764707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66572360635168626861176471 99858540952752940291764707)
                  ·
                    refine ⟨149787811429129410437647061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 99858540952752940291764707 149787811429129410437647061)
                    ·
                      refine ⟨3510651830370220557132353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 149787811429129410437647061 3510651830370220557132353)
                      ·
                        rfl

theorem cell23_6836970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_6836970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6836970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6836970 prefixEnd_6836970 := by exact prefixLift 6836970
  have htrace : WordTrace (prefixWord ++ tailWord_6836970) baseStart_6836970 baseEnd_6836970 := by
    simpa [prefixWord, tailWord_6836970, baseEnd_6836970] using wordTrace_append hprefix tailTrace_6836970
  have hstable : (prefixWord ++ tailWord_6836970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6836970).length < 2 ^ (prefixWord ++ tailWord_6836970).sum := by decide
  have hdescent : baseEnd_6836970 < baseStart_6836970 := by decide
  rcases family_descends (prefixWord ++ tailWord_6836970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6836997 : List Nat := [1, 3, 1, 1, 2, 1, 1, 4, 1, 6, 2]
def baseStart_6836997 : Nat := 118140960795 + 6836997 * 2 ^ 59
def prefixEnd_6836997 : Nat := 4983230072969 + 3 ^ 40 * 6836997 * 2
def baseEnd_6836997 : Nat := 3510665694347891951494729

theorem tailTrace_6836997 : CollatzResearch.WordTrace tailWord_6836997 prefixEnd_6836997 3510665694347891951494729 := by
  unfold tailWord_6836997
  simp only [CollatzResearch.WordTrace]
  refine ⟨249365766811735009970061245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166243844541156673313374163 249365766811735009970061245)
  ·
    refine ⟨93512162554400628738772967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249365766811735009970061245 93512162554400628738772967)
    ·
      refine ⟨140268243831600943108159451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93512162554400628738772967 140268243831600943108159451)
      ·
        refine ⟨210402365747401414662239177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140268243831600943108159451 210402365747401414662239177)
        ·
          refine ⟨157801774310551060996679383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210402365747401414662239177 157801774310551060996679383)
          ·
            refine ⟨236702661465826591495019075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157801774310551060996679383 236702661465826591495019075)
            ·
              refine ⟨355053992198739887242528613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 236702661465826591495019075 355053992198739887242528613)
              ·
                refine ⟨66572623537263728857974115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 355053992198739887242528613 66572623537263728857974115)
                ·
                  refine ⟨99858935305895593286961173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66572623537263728857974115 99858935305895593286961173)
                  ·
                    refine ⟨4680887592463855935326305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 99858935305895593286961173 4680887592463855935326305)
                    ·
                      refine ⟨3510665694347891951494729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4680887592463855935326305 3510665694347891951494729)
                      ·
                        rfl

theorem cell23_6836997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 6, 2].length) (baseStart_6836997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6836997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6836997 prefixEnd_6836997 := by exact prefixLift 6836997
  have htrace : WordTrace (prefixWord ++ tailWord_6836997) baseStart_6836997 baseEnd_6836997 := by
    simpa [prefixWord, tailWord_6836997, baseEnd_6836997] using wordTrace_append hprefix tailTrace_6836997
  have hstable : (prefixWord ++ tailWord_6836997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6836997).length < 2 ^ (prefixWord ++ tailWord_6836997).sum := by decide
  have hdescent : baseEnd_6836997 < baseStart_6836997 := by decide
  rcases family_descends (prefixWord ++ tailWord_6836997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6837024 : List Nat := [2, 1, 1, 5, 1, 2, 3, 1, 3, 4]
def baseStart_6837024 : Nat := 118140960795 + 6837024 * 2 ^ 59
def prefixEnd_6837024 : Nat := 4983230072969 + 3 ^ 40 * 6837024 * 2
def baseEnd_6837024 : Nat := 1170226519441854448619035

theorem tailTrace_6837024 : CollatzResearch.WordTrace tailWord_6837024 prefixEnd_6837024 1170226519441854448619035 := by
  unfold tailWord_6837024
  simp only [CollatzResearch.WordTrace]
  refine ⟨124683375791318596790647063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166244501055091462387529417 124683375791318596790647063)
  ·
    refine ⟨187025063686977895185970595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124683375791318596790647063 187025063686977895185970595)
    ·
      refine ⟨280537595530466842778955893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187025063686977895185970595 280537595530466842778955893)
      ·
        refine ⟨26300399580981266510527115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 280537595530466842778955893 26300399580981266510527115)
        ·
          refine ⟨39450599371471899765790673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26300399580981266510527115 39450599371471899765790673)
          ·
            refine ⟨29587949528603924824343005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39450599371471899765790673 29587949528603924824343005)
            ·
              refine ⟨11095481073226471809128627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29587949528603924824343005 11095481073226471809128627)
              ·
                refine ⟨16643221609839707713692941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11095481073226471809128627 16643221609839707713692941)
                ·
                  refine ⟨6241208103689890392634853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16643221609839707713692941 6241208103689890392634853)
                  ·
                    refine ⟨1170226519441854448619035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6241208103689890392634853 1170226519441854448619035)
                    ·
                      rfl

theorem cell23_6837024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 1, 3, 4].length) (baseStart_6837024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6837024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6837024 prefixEnd_6837024 := by exact prefixLift 6837024
  have htrace : WordTrace (prefixWord ++ tailWord_6837024) baseStart_6837024 baseEnd_6837024 := by
    simpa [prefixWord, tailWord_6837024, baseEnd_6837024] using wordTrace_append hprefix tailTrace_6837024
  have hstable : (prefixWord ++ tailWord_6837024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6837024).length < 2 ^ (prefixWord ++ tailWord_6837024).sum := by decide
  have hdescent : baseEnd_6837024 < baseStart_6837024 := by decide
  rcases family_descends (prefixWord ++ tailWord_6837024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6837040 : List Nat := [2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 6]
def baseStart_6837040 : Nat := 118140960795 + 6837040 * 2 ^ 59
def prefixEnd_6837040 : Nat := 4983230072969 + 3 ^ 40 * 6837040 * 2
def baseEnd_6837040 : Nat := 3510687774016035283257031

theorem tailTrace_6837040 : CollatzResearch.WordTrace tailWord_6837040 prefixEnd_6837040 3510687774016035283257031 := by
  unfold tailWord_6837040
  simp only [CollatzResearch.WordTrace]
  refine ⟨124683667575289614156938287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166244890100386152209251049 124683667575289614156938287)
  ·
    refine ⟨187025501362934421235407431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124683667575289614156938287 187025501362934421235407431)
    ·
      refine ⟨280538252044401631853111147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187025501362934421235407431 280538252044401631853111147)
      ·
        refine ⟨420807378066602447779666721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280538252044401631853111147 420807378066602447779666721)
        ·
          refine ⟨315605533549951835834750041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 420807378066602447779666721 315605533549951835834750041)
          ·
            refine ⟨236704150162463876876062531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 315605533549951835834750041 236704150162463876876062531)
            ·
              refine ⟨355056225243695815314093797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 236704150162463876876062531 355056225243695815314093797)
              ·
                refine ⟨66573042233192965371392587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 355056225243695815314093797 66573042233192965371392587)
                ·
                  refine ⟨99859563349789448057088881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66573042233192965371392587 99859563349789448057088881)
                  ·
                    refine ⟨74894672512342086042816661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 99859563349789448057088881 74894672512342086042816661)
                    ·
                      refine ⟨3510687774016035283257031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74894672512342086042816661 3510687774016035283257031)
                      ·
                        rfl

theorem cell23_6837040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 6].length) (baseStart_6837040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6837040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6837040 prefixEnd_6837040 := by exact prefixLift 6837040
  have htrace : WordTrace (prefixWord ++ tailWord_6837040) baseStart_6837040 baseEnd_6837040 := by
    simpa [prefixWord, tailWord_6837040, baseEnd_6837040] using wordTrace_append hprefix tailTrace_6837040
  have hstable : (prefixWord ++ tailWord_6837040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6837040).length < 2 ^ (prefixWord ++ tailWord_6837040).sum := by decide
  have hdescent : baseEnd_6837040 < baseStart_6837040 := by decide
  rcases family_descends (prefixWord ++ tailWord_6837040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6837084 : List Nat := [2, 2, 4, 2, 1, 1, 1, 2, 3, 5]
def baseStart_6837084 : Nat := 118140960795 + 6837084 * 2 ^ 59
def prefixEnd_6837084 : Nat := 4983230072969 + 3 ^ 40 * 6837084 * 2
def baseEnd_6837084 : Nat := 1170236789054944370368943

theorem tailTrace_6837084 : CollatzResearch.WordTrace tailWord_6837084 prefixEnd_6837084 1170236789054944370368943 := by
  unfold tailWord_6837084
  simp only [CollatzResearch.WordTrace]
  refine ⟨124684469981209911914239153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166245959974946549218985537 124684469981209911914239153)
  ·
    refine ⟨93513352485907433935679365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124684469981209911914239153 93513352485907433935679365)
    ·
      refine ⟨17533753591107643862939881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93513352485907433935679365 17533753591107643862939881)
      ·
        refine ⟨13150315193330732897204911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17533753591107643862939881 13150315193330732897204911)
        ·
          refine ⟨19725472789996099345807367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13150315193330732897204911 19725472789996099345807367)
          ·
            refine ⟨29588209184994149018711051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19725472789996099345807367 29588209184994149018711051)
            ·
              refine ⟨44382313777491223528066577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29588209184994149018711051 44382313777491223528066577)
              ·
                refine ⟨33286735333118417646049933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44382313777491223528066577 33286735333118417646049933)
                ·
                  refine ⟨12482525749919406617268725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33286735333118417646049933 12482525749919406617268725)
                  ·
                    refine ⟨1170236789054944370368943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12482525749919406617268725 1170236789054944370368943)
                    ·
                      rfl

theorem cell23_6837084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_6837084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6837084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6837084 prefixEnd_6837084 := by exact prefixLift 6837084
  have htrace : WordTrace (prefixWord ++ tailWord_6837084) baseStart_6837084 baseEnd_6837084 := by
    simpa [prefixWord, tailWord_6837084, baseEnd_6837084] using wordTrace_append hprefix tailTrace_6837084
  have hstable : (prefixWord ++ tailWord_6837084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6837084).length < 2 ^ (prefixWord ++ tailWord_6837084).sum := by decide
  have hdescent : baseEnd_6837084 < baseStart_6837084 := by decide
  rcases family_descends (prefixWord ++ tailWord_6837084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6837087 : List Nat := [1, 1, 2, 3, 1, 3, 1, 1, 5, 1, 4]
def baseStart_6837087 : Nat := 118140960795 + 6837087 * 2 ^ 59
def prefixEnd_6837087 : Nat := 4983230072969 + 3 ^ 40 * 6837087 * 2
def baseEnd_6837087 : Nat := 3510711907606796599369315

theorem tailTrace_6837087 : CollatzResearch.WordTrace tailWord_6837087 prefixEnd_6837087 3510711907606796599369315 := by
  unfold tailWord_6837087
  simp only [CollatzResearch.WordTrace]
  refine ⟨249369049381408955340837515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166246032920939303560558343 249369049381408955340837515)
  ·
    refine ⟨374053574072113433011256273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249369049381408955340837515 374053574072113433011256273)
    ·
      refine ⟨280540180554085074758442205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 374053574072113433011256273 280540180554085074758442205)
      ·
        refine ⟨105202567707781903034415827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 280540180554085074758442205 105202567707781903034415827)
        ·
          refine ⟨157803851561672854551623741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105202567707781903034415827 157803851561672854551623741)
          ·
            refine ⟨59176444335627320456858903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157803851561672854551623741 59176444335627320456858903)
            ·
              refine ⟨88764666503440980685288355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59176444335627320456858903 88764666503440980685288355)
              ·
                refine ⟨133146999755161471027932533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88764666503440980685288355 133146999755161471027932533)
                ·
                  refine ⟨12482531227046387908868675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 133146999755161471027932533 12482531227046387908868675)
                  ·
                    refine ⟨18723796840569581863303013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12482531227046387908868675 18723796840569581863303013)
                    ·
                      refine ⟨3510711907606796599369315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18723796840569581863303013 3510711907606796599369315)
                      ·
                        rfl

theorem cell23_6837087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 5, 1, 4].length) (baseStart_6837087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6837087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6837087 prefixEnd_6837087 := by exact prefixLift 6837087
  have htrace : WordTrace (prefixWord ++ tailWord_6837087) baseStart_6837087 baseEnd_6837087 := by
    simpa [prefixWord, tailWord_6837087, baseEnd_6837087] using wordTrace_append hprefix tailTrace_6837087
  have hstable : (prefixWord ++ tailWord_6837087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6837087).length < 2 ^ (prefixWord ++ tailWord_6837087).sum := by decide
  have hdescent : baseEnd_6837087 < baseStart_6837087 := by decide
  rcases family_descends (prefixWord ++ tailWord_6837087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6837097 : List Nat := [1, 2, 1, 1, 1, 3, 1, 1, 8, 4]
def baseStart_6837097 : Nat := 118140960795 + 6837097 * 2 ^ 59
def prefixEnd_6837097 : Nat := 4983230072969 + 3 ^ 40 * 6837097 * 2
def baseEnd_6837097 : Nat := 1170239014137780520081423

theorem tailTrace_6837097 : CollatzResearch.WordTrace tailWord_6837097 prefixEnd_6837097 1170239014137780520081423 := by
  unfold tailWord_6837097
  simp only [CollatzResearch.WordTrace]
  refine ⟨249369414111372727048701545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166246276074248484699134363 249369414111372727048701545)
  ·
    refine ⟨187027060583529545286526159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249369414111372727048701545 187027060583529545286526159)
    ·
      refine ⟨280540590875294317929789239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187027060583529545286526159 280540590875294317929789239)
      ·
        refine ⟨420810886312941476894683859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280540590875294317929789239 420810886312941476894683859)
        ·
          refine ⟨631216329469412215342025789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 420810886312941476894683859 631216329469412215342025789)
          ·
            refine ⟨236706123551029580753259671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 631216329469412215342025789 236706123551029580753259671)
            ·
              refine ⟨355059185326544371129889507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 236706123551029580753259671 355059185326544371129889507)
              ·
                refine ⟨532588777989816556694834261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 355059185326544371129889507 532588777989816556694834261)
                ·
                  refine ⟨6241274742068162773767589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 532588777989816556694834261 6241274742068162773767589)
                  ·
                    refine ⟨1170239014137780520081423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6241274742068162773767589 1170239014137780520081423)
                    ·
                      rfl

theorem cell23_6837097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 8, 4].length) (baseStart_6837097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6837097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6837097 prefixEnd_6837097 := by exact prefixLift 6837097
  have htrace : WordTrace (prefixWord ++ tailWord_6837097) baseStart_6837097 baseEnd_6837097 := by
    simpa [prefixWord, tailWord_6837097, baseEnd_6837097] using wordTrace_append hprefix tailTrace_6837097
  have hstable : (prefixWord ++ tailWord_6837097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6837097).length < 2 ^ (prefixWord ++ tailWord_6837097).sum := by decide
  have hdescent : baseEnd_6837097 < baseStart_6837097 := by decide
  rcases family_descends (prefixWord ++ tailWord_6837097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6837118 : List Nat := [4, 2, 3, 1, 2, 1, 1, 3, 1, 5]
def baseStart_6837118 : Nat := 118140960795 + 6837118 * 2 ^ 59
def prefixEnd_6837118 : Nat := 4983230072969 + 3 ^ 40 * 6837118 * 2
def baseEnd_6837118 : Nat := 1170242608502361992693891

theorem tailTrace_6837118 : CollatzResearch.WordTrace tailWord_6837118 prefixEnd_6837118 1170242608502361992693891 := by
  unfold tailWord_6837118
  simp only [CollatzResearch.WordTrace]
  refine ⟨31171272505537080954402001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166246786696197765090144005 31171272505537080954402001)
  ·
    refine ⟨23378454379152810715801501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31171272505537080954402001 23378454379152810715801501)
    ·
      refine ⟨8766920392182304018425563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23378454379152810715801501 8766920392182304018425563)
      ·
        refine ⟨13150380588273456027638345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8766920392182304018425563 13150380588273456027638345)
        ·
          refine ⟨9862785441205092020728759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13150380588273456027638345 9862785441205092020728759)
          ·
            refine ⟨14794178161807638031093139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9862785441205092020728759 14794178161807638031093139)
            ·
              refine ⟨22191267242711457046639709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14794178161807638031093139 22191267242711457046639709)
              ·
                refine ⟨8321725216016796392489891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22191267242711457046639709 8321725216016796392489891)
                ·
                  refine ⟨12482587824025194588734837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8321725216016796392489891 12482587824025194588734837)
                  ·
                    refine ⟨1170242608502361992693891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12482587824025194588734837 1170242608502361992693891)
                    ·
                      rfl

theorem cell23_6837118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_6837118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6837118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6837118 prefixEnd_6837118 := by exact prefixLift 6837118
  have htrace : WordTrace (prefixWord ++ tailWord_6837118) baseStart_6837118 baseEnd_6837118 := by
    simpa [prefixWord, tailWord_6837118, baseEnd_6837118] using wordTrace_append hprefix tailTrace_6837118
  have hstable : (prefixWord ++ tailWord_6837118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6837118).length < 2 ^ (prefixWord ++ tailWord_6837118).sum := by decide
  have hdescent : baseEnd_6837118 < baseStart_6837118 := by decide
  rcases family_descends (prefixWord ++ tailWord_6837118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6837127 : List Nat := [1, 1, 4, 2, 3, 2, 10]
def baseStart_6837127 : Nat := 118140960795 + 6837127 * 2 ^ 59
def prefixEnd_6837127 : Nat := 4983230072969 + 3 ^ 40 * 6837127 * 2
def baseEnd_6837127 : Nat := 43342375886826869665051

theorem tailTrace_6837127 : CollatzResearch.WordTrace tailWord_6837127 prefixEnd_6837127 43342375886826869665051 := by
  unfold tailWord_6837127
  simp only [CollatzResearch.WordTrace]
  refine ⟨249370508301264042172293635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166247005534176028114862423 249370508301264042172293635)
  ·
    refine ⟨374055762451896063258440453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249370508301264042172293635 374055762451896063258440453)
    ·
      refine ⟨70135455459730511860957585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 374055762451896063258440453 70135455459730511860957585)
      ·
        refine ⟨52601591594797883895718189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70135455459730511860957585 52601591594797883895718189)
        ·
          refine ⟨19725596848049206460894321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52601591594797883895718189 19725596848049206460894321)
          ·
            refine ⟨14794197636036904845670741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19725596848049206460894321 14794197636036904845670741)
            ·
              refine ⟨43342375886826869665051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14794197636036904845670741 43342375886826869665051)
              ·
                rfl

theorem cell23_6837127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 10].length) (baseStart_6837127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6837127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6837127 prefixEnd_6837127 := by exact prefixLift 6837127
  have htrace : WordTrace (prefixWord ++ tailWord_6837127) baseStart_6837127 baseEnd_6837127 := by
    simpa [prefixWord, tailWord_6837127, baseEnd_6837127] using wordTrace_append hprefix tailTrace_6837127
  have hstable : (prefixWord ++ tailWord_6837127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6837127).length < 2 ^ (prefixWord ++ tailWord_6837127).sum := by decide
  have hdescent : baseEnd_6837127 < baseStart_6837127 := by decide
  rcases family_descends (prefixWord ++ tailWord_6837127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6837148 : List Nat := [2, 2, 3, 3, 3, 1, 1, 1, 1, 6]
def baseStart_6837148 : Nat := 118140960795 + 6837148 * 2 ^ 59
def prefixEnd_6837148 : Nat := 4983230072969 + 3 ^ 40 * 6837148 * 2
def baseEnd_6837148 : Nat := 1170247743308906953568845

theorem tailTrace_6837148 : CollatzResearch.WordTrace tailWord_6837148 prefixEnd_6837148 1170247743308906953568845 := by
  unfold tailWord_6837148
  simp only [CollatzResearch.WordTrace]
  refine ⟨124685637117093981379404049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166247516156125308505872065 124685637117093981379404049)
  ·
    refine ⟨93514227837820486034553037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124685637117093981379404049 93514227837820486034553037)
    ·
      refine ⟨35067835439182682262957389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93514227837820486034553037 35067835439182682262957389)
      ·
        refine ⟨13150438289693505848609021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35067835439182682262957389 13150438289693505848609021)
        ·
          refine ⟨4931414358635064693228383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13150438289693505848609021 4931414358635064693228383)
          ·
            refine ⟨7397121537952597039842575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4931414358635064693228383 7397121537952597039842575)
            ·
              refine ⟨11095682306928895559763863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7397121537952597039842575 11095682306928895559763863)
              ·
                refine ⟨16643523460393343339645795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11095682306928895559763863 16643523460393343339645795)
                ·
                  refine ⟨24965285190590015009468693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16643523460393343339645795 24965285190590015009468693)
                  ·
                    refine ⟨1170247743308906953568845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24965285190590015009468693 1170247743308906953568845)
                    ·
                      rfl

theorem cell23_6837148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 1, 1, 6].length) (baseStart_6837148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6837148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6837148 prefixEnd_6837148 := by exact prefixLift 6837148
  have htrace : WordTrace (prefixWord ++ tailWord_6837148) baseStart_6837148 baseEnd_6837148 := by
    simpa [prefixWord, tailWord_6837148, baseEnd_6837148] using wordTrace_append hprefix tailTrace_6837148
  have hstable : (prefixWord ++ tailWord_6837148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6837148).length < 2 ^ (prefixWord ++ tailWord_6837148).sum := by decide
  have hdescent : baseEnd_6837148 < baseStart_6837148 := by decide
  rcases family_descends (prefixWord ++ tailWord_6837148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6837151 : List Nat := [1, 1, 2, 5, 2, 3, 1, 1, 1, 2, 4]
def baseStart_6837151 : Nat := 118140960795 + 6837151 * 2 ^ 59
def prefixEnd_6837151 : Nat := 4983230072969 + 3 ^ 40 * 6837151 * 2
def baseEnd_6837151 : Nat := 3510744770368684348969021

theorem tailTrace_6837151 : CollatzResearch.WordTrace tailWord_6837151 prefixEnd_6837151 3510744770368684348969021 := by
  unfold tailWord_6837151
  simp only [CollatzResearch.WordTrace]
  refine ⟨249371383653177094271167307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166247589102118062847444871 249371383653177094271167307)
  ·
    refine ⟨374057075479765641406750961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249371383653177094271167307 374057075479765641406750961)
    ·
      refine ⟨280542806609824231055063221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 374057075479765641406750961 280542806609824231055063221)
      ·
        refine ⟨26300888119671021661412177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 280542806609824231055063221 26300888119671021661412177)
        ·
          refine ⟨19725666089753266246059133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26300888119671021661412177 19725666089753266246059133)
          ·
            refine ⟨7397124783657474842272175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19725666089753266246059133 7397124783657474842272175)
            ·
              refine ⟨11095687175486212263408263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7397124783657474842272175 11095687175486212263408263)
              ·
                refine ⟨16643530763229318395112395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11095687175486212263408263 16643530763229318395112395)
                ·
                  refine ⟨24965296144843977592668593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16643530763229318395112395 24965296144843977592668593)
                  ·
                    refine ⟨18723972108632983194501445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24965296144843977592668593 18723972108632983194501445)
                    ·
                      refine ⟨3510744770368684348969021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18723972108632983194501445 3510744770368684348969021)
                      ·
                        rfl

theorem cell23_6837151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_6837151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6837151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6837151 prefixEnd_6837151 := by exact prefixLift 6837151
  have htrace : WordTrace (prefixWord ++ tailWord_6837151) baseStart_6837151 baseEnd_6837151 := by
    simpa [prefixWord, tailWord_6837151, baseEnd_6837151] using wordTrace_append hprefix tailTrace_6837151
  have hstable : (prefixWord ++ tailWord_6837151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6837151).length < 2 ^ (prefixWord ++ tailWord_6837151).sum := by decide
  have hdescent : baseEnd_6837151 < baseStart_6837151 := by decide
  rcases family_descends (prefixWord ++ tailWord_6837151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6837215 : List Nat := [1, 1, 2, 3, 5, 2, 1, 2, 1, 3, 2]
def baseStart_6837215 : Nat := 118140960795 + 6837215 * 2 ^ 59
def prefixEnd_6837215 : Nat := 4983230072969 + 3 ^ 40 * 6837215 * 2
def baseEnd_6837215 : Nat := 3510777633130572098568727

theorem tailTrace_6837215 : CollatzResearch.WordTrace tailWord_6837215 prefixEnd_6837215 3510777633130572098568727 := by
  unfold tailWord_6837215
  simp only [CollatzResearch.WordTrace]
  refine ⟨249373717924945233201497099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166249145283296822134331399 249373717924945233201497099)
  ·
    refine ⟨374060576887417849802245649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249373717924945233201497099 374060576887417849802245649)
    ·
      refine ⟨280545432665563387351684237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 374060576887417849802245649 280545432665563387351684237)
      ·
        refine ⟨105204537249586270256881589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 280545432665563387351684237 105204537249586270256881589)
        ·
          refine ⟨9862925367148712836582649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 105204537249586270256881589 9862925367148712836582649)
          ·
            refine ⟨7397194025361534627436987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9862925367148712836582649 7397194025361534627436987)
            ·
              refine ⟨11095791038042301941155481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7397194025361534627436987 11095791038042301941155481)
              ·
                refine ⟨8321843278531726455866611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11095791038042301941155481 8321843278531726455866611)
                ·
                  refine ⟨12482764917797589683799917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8321843278531726455866611 12482764917797589683799917)
                  ·
                    refine ⟨4681036844174096131424969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12482764917797589683799917 4681036844174096131424969)
                    ·
                      refine ⟨3510777633130572098568727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4681036844174096131424969 3510777633130572098568727)
                      ·
                        rfl

theorem cell23_6837215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 2, 1, 3, 2].length) (baseStart_6837215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6837215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6837215 prefixEnd_6837215 := by exact prefixLift 6837215
  have htrace : WordTrace (prefixWord ++ tailWord_6837215) baseStart_6837215 baseEnd_6837215 := by
    simpa [prefixWord, tailWord_6837215, baseEnd_6837215] using wordTrace_append hprefix tailTrace_6837215
  have hstable : (prefixWord ++ tailWord_6837215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6837215).length < 2 ^ (prefixWord ++ tailWord_6837215).sum := by decide
  have hdescent : baseEnd_6837215 < baseStart_6837215 := by decide
  rcases family_descends (prefixWord ++ tailWord_6837215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6837217 : List Nat := [1, 2, 3, 1, 2, 1, 1, 3, 9]
def baseStart_6837217 : Nat := 118140960795 + 6837217 * 2 ^ 59
def prefixEnd_6837217 : Nat := 4983230072969 + 3 ^ 40 * 6837217 * 2
def baseEnd_6837217 : Nat := 390086517787986787860413

theorem tailTrace_6837217 : CollatzResearch.WordTrace tailWord_6837217 prefixEnd_6837217 390086517787986787860413 := by
  unfold tailWord_6837217
  simp only [CollatzResearch.WordTrace]
  refine ⟨249373790870937987543069905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166249193913958658362046603 249373790870937987543069905)
  ·
    refine ⟨187030343153203490657302429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249373790870937987543069905 187030343153203490657302429)
    ·
      refine ⟨70136378682451308996488411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187030343153203490657302429 70136378682451308996488411)
      ·
        refine ⟨105204568023676963494732617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70136378682451308996488411 105204568023676963494732617)
        ·
          refine ⟨78903426017757722621049463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105204568023676963494732617 78903426017757722621049463)
          ·
            refine ⟨118355139026636583931574195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78903426017757722621049463 118355139026636583931574195)
            ·
              refine ⟨177532708539954875897361293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118355139026636583931574195 177532708539954875897361293)
              ·
                refine ⟨66574765702483078461510485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 177532708539954875897361293 66574765702483078461510485)
                ·
                  refine ⟨390086517787986787860413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 66574765702483078461510485 390086517787986787860413)
                  ·
                    rfl

theorem cell23_6837217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 9].length) (baseStart_6837217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6837217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6837217 prefixEnd_6837217 := by exact prefixLift 6837217
  have htrace : WordTrace (prefixWord ++ tailWord_6837217) baseStart_6837217 baseEnd_6837217 := by
    simpa [prefixWord, tailWord_6837217, baseEnd_6837217] using wordTrace_append hprefix tailTrace_6837217
  have hstable : (prefixWord ++ tailWord_6837217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6837217).length < 2 ^ (prefixWord ++ tailWord_6837217).sum := by decide
  have hdescent : baseEnd_6837217 < baseStart_6837217 := by decide
  rcases family_descends (prefixWord ++ tailWord_6837217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6837247 : List Nat := [1, 1, 2, 2, 1, 2, 1, 1, 5, 7]
def baseStart_6837247 : Nat := 118140960795 + 6837247 * 2 ^ 59
def prefixEnd_6837247 : Nat := 4983230072969 + 3 ^ 40 * 6837247 * 2
def baseEnd_6837247 : Nat := 1170264688170505324456193

theorem tailTrace_6837247 : CollatzResearch.WordTrace tailWord_6837247 prefixEnd_6837247 1170264688170505324456193 := by
  unfold tailWord_6837247
  simp only [CollatzResearch.WordTrace]
  refine ⟨249374885060829302666661995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166249923373886201777774663 249374885060829302666661995)
  ·
    refine ⟨374062327591243953999992993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249374885060829302666661995 374062327591243953999992993)
    ·
      refine ⟨280546745693432965499994745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 374062327591243953999992993 280546745693432965499994745)
      ·
        refine ⟨210410059270074724124996059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280546745693432965499994745 210410059270074724124996059)
        ·
          refine ⟨315615088905112086187494089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210410059270074724124996059 315615088905112086187494089)
          ·
            refine ⟨236711316678834064640620567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 315615088905112086187494089 236711316678834064640620567)
            ·
              refine ⟨355066975018251096960930851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 236711316678834064640620567 355066975018251096960930851)
              ·
                refine ⟨532600462527376645441396277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 355066975018251096960930851 532600462527376645441396277)
                ·
                  refine ⟨49931293361941560510130901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 532600462527376645441396277 49931293361941560510130901)
                  ·
                    refine ⟨1170264688170505324456193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49931293361941560510130901 1170264688170505324456193)
                    ·
                      rfl

theorem cell23_6837247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 5, 7].length) (baseStart_6837247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6837247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6837247 prefixEnd_6837247 := by exact prefixLift 6837247
  have htrace : WordTrace (prefixWord ++ tailWord_6837247) baseStart_6837247 baseEnd_6837247 := by
    simpa [prefixWord, tailWord_6837247, baseEnd_6837247] using wordTrace_append hprefix tailTrace_6837247
  have hstable : (prefixWord ++ tailWord_6837247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6837247).length < 2 ^ (prefixWord ++ tailWord_6837247).sum := by decide
  have hdescent : baseEnd_6837247 < baseStart_6837247 := by decide
  rcases family_descends (prefixWord ++ tailWord_6837247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6837281 : List Nat := [1, 2, 3, 2, 3, 1, 3, 1, 2, 5]
def baseStart_6837281 : Nat := 118140960795 + 6837281 * 2 ^ 59
def prefixEnd_6837281 : Nat := 4983230072969 + 3 ^ 40 * 6837281 * 2
def baseEnd_6837281 : Nat := 1170270507617922946781141

theorem tailTrace_6837281 : CollatzResearch.WordTrace tailWord_6837281 prefixEnd_6837281 1170270507617922946781141 := by
  unfold tailWord_6837281
  simp only [CollatzResearch.WordTrace]
  refine ⟨249376125142706126473399697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166250750095137417648933131 249376125142706126473399697)
  ·
    refine ⟨187032093857029594855049773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249376125142706126473399697 187032093857029594855049773)
    ·
      refine ⟨70137035196386098070643665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187032093857029594855049773 70137035196386098070643665)
      ·
        refine ⟨52602776397289573552982749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70137035196386098070643665 52602776397289573552982749)
        ·
          refine ⟨19726041148983590082368531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52602776397289573552982749 19726041148983590082368531)
          ·
            refine ⟨29589061723475385123552797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19726041148983590082368531 29589061723475385123552797)
            ·
              refine ⟨11095898146303269421332299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29589061723475385123552797 11095898146303269421332299)
              ·
                refine ⟨16643847219454904131998449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11095898146303269421332299 16643847219454904131998449)
                ·
                  refine ⟨12482885414591178098998837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16643847219454904131998449 12482885414591178098998837)
                  ·
                    refine ⟨1170270507617922946781141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12482885414591178098998837 1170270507617922946781141)
                    ·
                      rfl

theorem cell23_6837281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 1, 2, 5].length) (baseStart_6837281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6837281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6837281 prefixEnd_6837281 := by exact prefixLift 6837281
  have htrace : WordTrace (prefixWord ++ tailWord_6837281) baseStart_6837281 baseEnd_6837281 := by
    simpa [prefixWord, tailWord_6837281, baseEnd_6837281] using wordTrace_append hprefix tailTrace_6837281
  have hstable : (prefixWord ++ tailWord_6837281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6837281).length < 2 ^ (prefixWord ++ tailWord_6837281).sum := by decide
  have hdescent : baseEnd_6837281 < baseStart_6837281 := by decide
  rcases family_descends (prefixWord ++ tailWord_6837281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6837318 : List Nat := [6, 1, 1, 1, 1, 2, 1, 2, 1, 3, 4]
def baseStart_6837318 : Nat := 118140960795 + 6837318 * 2 ^ 59
def prefixEnd_6837318 : Nat := 4983230072969 + 3 ^ 40 * 6837318 * 2
def baseEnd_6837318 : Nat := 3510830521637985195580753

theorem tailTrace_6837318 : CollatzResearch.WordTrace tailWord_6837318 prefixEnd_6837318 3510830521637985195580753 := by
  unfold tailWord_6837318
  simp only [CollatzResearch.WordTrace]
  refine ⟨7793046082611627556015519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 166251649762381387861664405 7793046082611627556015519)
  ·
    refine ⟨11689569123917441334023279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7793046082611627556015519 11689569123917441334023279)
    ·
      refine ⟨17534353685876162001034919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11689569123917441334023279 17534353685876162001034919)
      ·
        refine ⟨26301530528814243001552379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17534353685876162001034919 26301530528814243001552379)
        ·
          refine ⟨39452295793221364502328569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26301530528814243001552379 39452295793221364502328569)
          ·
            refine ⟨29589221844916023376746427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39452295793221364502328569 29589221844916023376746427)
            ·
              refine ⟨44383832767374035065119641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29589221844916023376746427 44383832767374035065119641)
              ·
                refine ⟨33287874575530526298839731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44383832767374035065119641 33287874575530526298839731)
                ·
                  refine ⟨49931811863295789448259597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33287874575530526298839731 49931811863295789448259597)
                  ·
                    refine ⟨18724429448735921043097349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49931811863295789448259597 18724429448735921043097349)
                    ·
                      refine ⟨3510830521637985195580753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18724429448735921043097349 3510830521637985195580753)
                      ·
                        rfl

theorem cell23_6837318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_6837318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6837318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6837318 prefixEnd_6837318 := by exact prefixLift 6837318
  have htrace : WordTrace (prefixWord ++ tailWord_6837318) baseStart_6837318 baseEnd_6837318 := by
    simpa [prefixWord, tailWord_6837318, baseEnd_6837318] using wordTrace_append hprefix tailTrace_6837318
  have hstable : (prefixWord ++ tailWord_6837318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6837318).length < 2 ^ (prefixWord ++ tailWord_6837318).sum := by decide
  have hdescent : baseEnd_6837318 < baseStart_6837318 := by decide
  rcases family_descends (prefixWord ++ tailWord_6837318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6837361 : List Nat := [1, 2, 2, 2, 1, 1, 2, 2, 3, 5, 2]
def baseStart_6837361 : Nat := 118140960795 + 6837361 * 2 ^ 59
def prefixEnd_6837361 : Nat := 4983230072969 + 3 ^ 40 * 6837361 * 2
def baseEnd_6837361 : Nat := 3510852601306128527343055

theorem tailTrace_6837361 : CollatzResearch.WordTrace tailWord_6837361 prefixEnd_6837361 3510852601306128527343055 := by
  unfold tailWord_6837361
  simp only [CollatzResearch.WordTrace]
  refine ⟨249379042982416300136311937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166252695321610866757541291 249379042982416300136311937)
  ·
    refine ⟨187034282236812225102233953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249379042982416300136311937 187034282236812225102233953)
    ·
      refine ⟨140275711677609168826675465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187034282236812225102233953 140275711677609168826675465)
      ·
        refine ⟨105206783758206876620006599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140275711677609168826675465 105206783758206876620006599)
        ·
          refine ⟨157810175637310314930009899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105206783758206876620006599 157810175637310314930009899)
          ·
            refine ⟨236715263455965472395014849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157810175637310314930009899 236715263455965472395014849)
            ·
              refine ⟨177536447591974104296261137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 236715263455965472395014849 177536447591974104296261137)
              ·
                refine ⟨133152335693980578222195853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 177536447591974104296261137 133152335693980578222195853)
                ·
                  refine ⟨49932125885242716833323445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 133152335693980578222195853 49932125885242716833323445)
                  ·
                    refine ⟨4681136801741504703124073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49932125885242716833323445 4681136801741504703124073)
                    ·
                      refine ⟨3510852601306128527343055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4681136801741504703124073 3510852601306128527343055)
                      ·
                        rfl

theorem cell23_6837361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 3, 5, 2].length) (baseStart_6837361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6837361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6837361 prefixEnd_6837361 := by exact prefixLift 6837361
  have htrace : WordTrace (prefixWord ++ tailWord_6837361) baseStart_6837361 baseEnd_6837361 := by
    simpa [prefixWord, tailWord_6837361, baseEnd_6837361] using wordTrace_append hprefix tailTrace_6837361
  have hstable : (prefixWord ++ tailWord_6837361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6837361).length < 2 ^ (prefixWord ++ tailWord_6837361).sum := by decide
  have hdescent : baseEnd_6837361 < baseStart_6837361 := by decide
  rcases family_descends (prefixWord ++ tailWord_6837361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6837368 : List Nat := [2, 1, 2, 1, 1, 1, 7, 1, 3, 1, 3]
def baseStart_6837368 : Nat := 118140960795 + 6837368 * 2 ^ 59
def prefixEnd_6837368 : Nat := 4983230072969 + 3 ^ 40 * 6837368 * 2
def baseEnd_6837368 : Nat := 3510856195670709999955523

theorem tailTrace_6837368 : CollatzResearch.WordTrace tailWord_6837368 prefixEnd_6837368 3510856195670709999955523 := by
  unfold tailWord_6837368
  simp only [CollatzResearch.WordTrace]
  refine ⟨124689649146695470165908379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166252865528927293554544505 124689649146695470165908379)
  ·
    refine ⟨187034473720043205248862569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124689649146695470165908379 187034473720043205248862569)
    ·
      refine ⟨140275855290032403936646927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187034473720043205248862569 140275855290032403936646927)
      ·
        refine ⟨210413782935048605904970391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140275855290032403936646927 210413782935048605904970391)
        ·
          refine ⟨315620674402572908857455587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210413782935048605904970391 315620674402572908857455587)
          ·
            refine ⟨473431011603859363286183381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315620674402572908857455587 473431011603859363286183381)
            ·
              refine ⟨11096039334465453827019923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 473431011603859363286183381 11096039334465453827019923)
              ·
                refine ⟨16644059001698180740529885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11096039334465453827019923 16644059001698180740529885)
                ·
                  refine ⟨6241522125636817777698707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16644059001698180740529885 6241522125636817777698707)
                  ·
                    refine ⟨9362283188455226666548061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6241522125636817777698707 9362283188455226666548061)
                    ·
                      refine ⟨3510856195670709999955523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9362283188455226666548061 3510856195670709999955523)
                      ·
                        rfl

theorem cell23_6837368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 1, 3, 1, 3].length) (baseStart_6837368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6837368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6837368 prefixEnd_6837368 := by exact prefixLift 6837368
  have htrace : WordTrace (prefixWord ++ tailWord_6837368) baseStart_6837368 baseEnd_6837368 := by
    simpa [prefixWord, tailWord_6837368, baseEnd_6837368] using wordTrace_append hprefix tailTrace_6837368
  have hstable : (prefixWord ++ tailWord_6837368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6837368).length < 2 ^ (prefixWord ++ tailWord_6837368).sum := by decide
  have hdescent : baseEnd_6837368 < baseStart_6837368 := by decide
  rcases family_descends (prefixWord ++ tailWord_6837368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6837438 : List Nat := [4, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4]
def baseStart_6837438 : Nat := 118140960795 + 6837438 * 2 ^ 59
def prefixEnd_6837438 : Nat := 4983230072969 + 3 ^ 40 * 6837438 * 2
def baseEnd_6837438 : Nat := 3510892139316524726080201

theorem tailTrace_6837438 : CollatzResearch.WordTrace tailWord_6837438 prefixEnd_6837438 3510892139316524726080201 := by
  unfold tailWord_6837438
  simp only [CollatzResearch.WordTrace]
  refine ⟨31172731425392167785858121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166254567602091561524576645 31172731425392167785858121)
  ·
    refine ⟨23379548569044125839393591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31172731425392167785858121 23379548569044125839393591)
    ·
      refine ⟨35069322853566188759090387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23379548569044125839393591 35069322853566188759090387)
      ·
        refine ⟨52603984280349283138635581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35069322853566188759090387 52603984280349283138635581)
        ·
          refine ⟨19726494105130981176988343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52603984280349283138635581 19726494105130981176988343)
          ·
            refine ⟨29589741157696471765482515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19726494105130981176988343 29589741157696471765482515)
            ·
              refine ⟨44384611736544707648223773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29589741157696471765482515 44384611736544707648223773)
              ·
                refine ⟨16644229401204265368083915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44384611736544707648223773 16644229401204265368083915)
                ·
                  refine ⟨24966344101806398052125873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16644229401204265368083915 24966344101806398052125873)
                  ·
                    refine ⟨18724758076354798539094405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24966344101806398052125873 18724758076354798539094405)
                    ·
                      refine ⟨3510892139316524726080201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18724758076354798539094405 3510892139316524726080201)
                      ·
                        rfl

theorem cell23_6837438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_6837438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6837438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6837438 prefixEnd_6837438 := by exact prefixLift 6837438
  have htrace : WordTrace (prefixWord ++ tailWord_6837438) baseStart_6837438 baseEnd_6837438 := by
    simpa [prefixWord, tailWord_6837438, baseEnd_6837438] using wordTrace_append hprefix tailTrace_6837438
  have hstable : (prefixWord ++ tailWord_6837438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6837438).length < 2 ^ (prefixWord ++ tailWord_6837438).sum := by decide
  have hdescent : baseEnd_6837438 < baseStart_6837438 := by decide
  rcases family_descends (prefixWord ++ tailWord_6837438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6837458 : List Nat := [3, 2, 2, 2, 1, 1, 1, 4, 1, 3, 3]
def baseStart_6837458 : Nat := 118140960795 + 6837458 * 2 ^ 59
def prefixEnd_6837458 : Nat := 4983230072969 + 3 ^ 40 * 6837458 * 2
def baseEnd_6837458 : Nat := 3510902408929614647830109

theorem tailTrace_6837458 : CollatzResearch.WordTrace tailWord_6837458 prefixEnd_6837458 3510902408929614647830109 := by
  unfold tailWord_6837458
  simp only [CollatzResearch.WordTrace]
  refine ⟨62345645215766221425648257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166255053908709923801728685 62345645215766221425648257)
  ·
    refine ⟨46759233911824666069236193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62345645215766221425648257 46759233911824666069236193)
    ·
      refine ⟨35069425433868499551927145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46759233911824666069236193 35069425433868499551927145)
      ·
        refine ⟨26302069075401374663945359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35069425433868499551927145 26302069075401374663945359)
        ·
          refine ⟨39453103613102061995918039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26302069075401374663945359 39453103613102061995918039)
          ·
            refine ⟨59179655419653092993877059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39453103613102061995918039 59179655419653092993877059)
            ·
              refine ⟨88769483129479639490815589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59179655419653092993877059 88769483129479639490815589)
              ·
                refine ⟨16644278086777432404527923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88769483129479639490815589 16644278086777432404527923)
                ·
                  refine ⟨24966417130166148606791885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16644278086777432404527923 24966417130166148606791885)
                  ·
                    refine ⟨9362406423812305727546957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24966417130166148606791885 9362406423812305727546957)
                    ·
                      refine ⟨3510902408929614647830109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9362406423812305727546957 3510902408929614647830109)
                      ·
                        rfl

theorem cell23_6837458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_6837458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6837458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6837458 prefixEnd_6837458 := by exact prefixLift 6837458
  have htrace : WordTrace (prefixWord ++ tailWord_6837458) baseStart_6837458 baseEnd_6837458 := by
    simpa [prefixWord, tailWord_6837458, baseEnd_6837458] using wordTrace_append hprefix tailTrace_6837458
  have hstable : (prefixWord ++ tailWord_6837458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6837458).length < 2 ^ (prefixWord ++ tailWord_6837458).sum := by decide
  have hdescent : baseEnd_6837458 < baseStart_6837458 := by decide
  rcases family_descends (prefixWord ++ tailWord_6837458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6837469 : List Nat := [1, 4, 3, 2, 3, 1, 1, 2, 2, 4]
def baseStart_6837469 : Nat := 118140960795 + 6837469 * 2 ^ 59
def prefixEnd_6837469 : Nat := 4983230072969 + 3 ^ 40 * 6837469 * 2
def baseEnd_6837469 : Nat := 1170302685738938034930853

theorem tailTrace_6837469 : CollatzResearch.WordTrace tailWord_6837469 prefixEnd_6837469 1170302685738938034930853 := by
  unfold tailWord_6837469
  simp only [CollatzResearch.WordTrace]
  refine ⟨249382982066025034581243461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166255321377350023054162307 249382982066025034581243461)
  ·
    refine ⟨46759309137379693983983149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 249382982066025034581243461 46759309137379693983983149)
    ·
      refine ⟨17534740926517385243993681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46759309137379693983983149 17534740926517385243993681)
      ·
        refine ⟨13151055694888038932995261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17534740926517385243993681 13151055694888038932995261)
        ·
          refine ⟨4931645885583014599873223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13151055694888038932995261 4931645885583014599873223)
          ·
            refine ⟨7397468828374521899809835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4931645885583014599873223 7397468828374521899809835)
            ·
              refine ⟨11096203242561782849714753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7397468828374521899809835 11096203242561782849714753)
              ·
                refine ⟨8322152431921337137286065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11096203242561782849714753 8322152431921337137286065)
                ·
                  refine ⟨6241614323941002852964549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8322152431921337137286065 6241614323941002852964549)
                  ·
                    refine ⟨1170302685738938034930853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6241614323941002852964549 1170302685738938034930853)
                    ·
                      rfl

theorem cell23_6837469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_6837469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6837469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6837469 prefixEnd_6837469 := by exact prefixLift 6837469
  have htrace : WordTrace (prefixWord ++ tailWord_6837469) baseStart_6837469 baseEnd_6837469 := by
    simpa [prefixWord, tailWord_6837469, baseEnd_6837469] using wordTrace_append hprefix tailTrace_6837469
  have hstable : (prefixWord ++ tailWord_6837469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6837469).length < 2 ^ (prefixWord ++ tailWord_6837469).sum := by decide
  have hdescent : baseEnd_6837469 < baseStart_6837469 := by decide
  rcases family_descends (prefixWord ++ tailWord_6837469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6837491 : List Nat := [1, 1, 1, 2, 2, 5, 2, 1, 2, 6]
def baseStart_6837491 : Nat := 118140960795 + 6837491 * 2 ^ 59
def prefixEnd_6837491 : Nat := 4983230072969 + 3 ^ 40 * 6837491 * 2
def baseEnd_6837491 : Nat := 1170306451263737672905819

theorem tailTrace_6837491 : CollatzResearch.WordTrace tailWord_6837491 prefixEnd_6837491 1170306451263737672905819 := by
  unfold tailWord_6837491
  simp only [CollatzResearch.WordTrace]
  refine ⟨249383784471945332338544327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166255856314630221559029551 249383784471945332338544327)
  ·
    refine ⟨374075676707917998507816491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249383784471945332338544327 374075676707917998507816491)
    ·
      refine ⟨561113515061876997761724737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374075676707917998507816491 561113515061876997761724737)
      ·
        refine ⟨420835136296407748321293553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 561113515061876997761724737 420835136296407748321293553)
        ·
          refine ⟨315626352222305811240970165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 420835136296407748321293553 315626352222305811240970165)
          ·
            refine ⟨29589970520841169803840953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 315626352222305811240970165 29589970520841169803840953)
            ·
              refine ⟨22192477890630877352880715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29589970520841169803840953 22192477890630877352880715)
              ·
                refine ⟨33288716835946316029321073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22192477890630877352880715 33288716835946316029321073)
                ·
                  refine ⟨24966537626959737021990805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33288716835946316029321073 24966537626959737021990805)
                  ·
                    refine ⟨1170306451263737672905819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24966537626959737021990805 1170306451263737672905819)
                    ·
                      rfl

theorem cell23_6837491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 1, 2, 6].length) (baseStart_6837491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6837491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6837491 prefixEnd_6837491 := by exact prefixLift 6837491
  have htrace : WordTrace (prefixWord ++ tailWord_6837491) baseStart_6837491 baseEnd_6837491 := by
    simpa [prefixWord, tailWord_6837491, baseEnd_6837491] using wordTrace_append hprefix tailTrace_6837491
  have hstable : (prefixWord ++ tailWord_6837491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6837491).length < 2 ^ (prefixWord ++ tailWord_6837491).sum := by decide
  have hdescent : baseEnd_6837491 < baseStart_6837491 := by decide
  rcases family_descends (prefixWord ++ tailWord_6837491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6837502 : List Nat := [4, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2]
def baseStart_6837502 : Nat := 118140960795 + 6837502 * 2 ^ 59
def prefixEnd_6837502 : Nat := 4983230072969 + 3 ^ 40 * 6837502 * 2
def baseEnd_6837502 : Nat := 3510925002078412475679907

theorem tailTrace_6837502 : CollatzResearch.WordTrace tailWord_6837502 prefixEnd_6837502 3510925002078412475679907 := by
  unfold tailWord_6837502
  simp only [CollatzResearch.WordTrace]
  refine ⟨31173023209363185152149345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166256123783270320811463173 31173023209363185152149345)
  ·
    refine ⟨23379767407022388864112009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31173023209363185152149345 23379767407022388864112009)
    ·
      refine ⟨17534825555266791648084007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23379767407022388864112009 17534825555266791648084007)
      ·
        refine ⟨26302238332900187472126011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17534825555266791648084007 26302238332900187472126011)
        ·
          refine ⟨39453357499350281208189017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26302238332900187472126011 39453357499350281208189017)
          ·
            refine ⟨29590018124512710906141763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39453357499350281208189017 29590018124512710906141763)
            ·
              refine ⟨44385027186769066359212645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29590018124512710906141763 44385027186769066359212645)
              ·
                refine ⟨8322192597519199942352371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44385027186769066359212645 8322192597519199942352371)
                ·
                  refine ⟨12483288896278799913528557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8322192597519199942352371 12483288896278799913528557)
                  ·
                    refine ⟨4681233336104549967573209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12483288896278799913528557 4681233336104549967573209)
                    ·
                      refine ⟨3510925002078412475679907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4681233336104549967573209 3510925002078412475679907)
                      ·
                        rfl

theorem cell23_6837502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2].length) (baseStart_6837502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6837502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6837502 prefixEnd_6837502 := by exact prefixLift 6837502
  have htrace : WordTrace (prefixWord ++ tailWord_6837502) baseStart_6837502 baseEnd_6837502 := by
    simpa [prefixWord, tailWord_6837502, baseEnd_6837502] using wordTrace_append hprefix tailTrace_6837502
  have hstable : (prefixWord ++ tailWord_6837502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6837502).length < 2 ^ (prefixWord ++ tailWord_6837502).sum := by decide
  have hdescent : baseEnd_6837502 < baseStart_6837502 := by decide
  rcases family_descends (prefixWord ++ tailWord_6837502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6837515 : List Nat := [1, 1, 1, 1, 5, 3, 1, 2, 4, 2, 2]
def baseStart_6837515 : Nat := 118140960795 + 6837515 * 2 ^ 59
def prefixEnd_6837515 : Nat := 4983230072969 + 3 ^ 40 * 6837515 * 2
def baseEnd_6837515 : Nat := 3510931677326920924817347

theorem tailTrace_6837515 : CollatzResearch.WordTrace tailWord_6837515 prefixEnd_6837515 3510931677326920924817347 := by
  unfold tailWord_6837515
  simp only [CollatzResearch.WordTrace]
  refine ⟨249384659823858384437417999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166256439882572256291611999 249384659823858384437417999)
  ·
    refine ⟨374076989735787576656126999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249384659823858384437417999 374076989735787576656126999)
    ·
      refine ⟨561115484603681364984190499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374076989735787576656126999 561115484603681364984190499)
      ·
        refine ⟨841673226905522047476285749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 561115484603681364984190499 841673226905522047476285749)
        ·
          refine ⟨78906865022392691950901789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 841673226905522047476285749 78906865022392691950901789)
          ·
            refine ⟨29590074383397259481588171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78906865022392691950901789 29590074383397259481588171)
            ·
              refine ⟨44385111575095889222382257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29590074383397259481588171 44385111575095889222382257)
              ·
                refine ⟨33288833681321916916786693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44385111575095889222382257 33288833681321916916786693)
                ·
                  refine ⟨6241656315247859421897505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33288833681321916916786693 6241656315247859421897505)
                  ·
                    refine ⟨4681242236435894566423129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6241656315247859421897505 4681242236435894566423129)
                    ·
                      refine ⟨3510931677326920924817347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4681242236435894566423129 3510931677326920924817347)
                      ·
                        rfl

theorem cell23_6837515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 2, 4, 2, 2].length) (baseStart_6837515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6837515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6837515 prefixEnd_6837515 := by exact prefixLift 6837515
  have htrace : WordTrace (prefixWord ++ tailWord_6837515) baseStart_6837515 baseEnd_6837515 := by
    simpa [prefixWord, tailWord_6837515, baseEnd_6837515] using wordTrace_append hprefix tailTrace_6837515
  have hstable : (prefixWord ++ tailWord_6837515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6837515).length < 2 ^ (prefixWord ++ tailWord_6837515).sum := by decide
  have hdescent : baseEnd_6837515 < baseStart_6837515 := by decide
  rcases family_descends (prefixWord ++ tailWord_6837515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6837518 : List Nat := [4, 1, 1, 2, 1, 4, 1, 1, 2, 1, 5]
def baseStart_6837518 : Nat := 118140960795 + 6837518 * 2 ^ 59
def prefixEnd_6837518 : Nat := 4983230072969 + 3 ^ 40 * 6837518 * 2
def baseEnd_6837518 : Nat := 3510933217768884413079833

theorem tailTrace_6837518 : CollatzResearch.WordTrace tailWord_6837518 prefixEnd_6837518 3510933217768884413079833 := by
  unfold tailWord_6837518
  simp only [CollatzResearch.WordTrace]
  refine ⟨31173096155355939493722151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166256512828565010633184805 31173096155355939493722151)
  ·
    refine ⟨46759644233033909240583227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31173096155355939493722151 46759644233033909240583227)
    ·
      refine ⟨70139466349550863860874841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46759644233033909240583227 70139466349550863860874841)
      ·
        refine ⟨52604599762163147895656131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70139466349550863860874841 52604599762163147895656131)
        ·
          refine ⟨78906899643244721843484197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52604599762163147895656131 78906899643244721843484197)
          ·
            refine ⟨14795043683108385345653287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78906899643244721843484197 14795043683108385345653287)
            ·
              refine ⟨22192565524662578018479931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14795043683108385345653287 22192565524662578018479931)
              ·
                refine ⟨33288848286993867027719897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22192565524662578018479931 33288848286993867027719897)
                ·
                  refine ⟨24966636215245400270789923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33288848286993867027719897 24966636215245400270789923)
                  ·
                    refine ⟨37449954322868100406184885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24966636215245400270789923 37449954322868100406184885)
                    ·
                      refine ⟨3510933217768884413079833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37449954322868100406184885 3510933217768884413079833)
                      ·
                        rfl

theorem cell23_6837518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_6837518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6837518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6837518 prefixEnd_6837518 := by exact prefixLift 6837518
  have htrace : WordTrace (prefixWord ++ tailWord_6837518) baseStart_6837518 baseEnd_6837518 := by
    simpa [prefixWord, tailWord_6837518, baseEnd_6837518] using wordTrace_append hprefix tailTrace_6837518
  have hstable : (prefixWord ++ tailWord_6837518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6837518).length < 2 ^ (prefixWord ++ tailWord_6837518).sum := by decide
  have hdescent : baseEnd_6837518 < baseStart_6837518 := by decide
  rcases family_descends (prefixWord ++ tailWord_6837518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6837551 : List Nat := [1, 1, 2, 1, 2, 1, 3, 1, 6, 5]
def baseStart_6837551 : Nat := 118140960795 + 6837551 * 2 ^ 59
def prefixEnd_6837551 : Nat := 4983230072969 + 3 ^ 40 * 6837551 * 2
def baseEnd_6837551 : Nat := 1170316720876827594655727

theorem tailTrace_6837551 : CollatzResearch.WordTrace tailWord_6837551 prefixEnd_6837551 1170316720876827594655727 := by
  unfold tailWord_6837551
  simp only [CollatzResearch.WordTrace]
  refine ⟨249385972851727962585728507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166257315234485308390485671 249385972851727962585728507)
  ·
    refine ⟨374078959277591943878592761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249385972851727962585728507 374078959277591943878592761)
    ·
      refine ⟨280559219458193957908944571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 374078959277591943878592761 280559219458193957908944571)
      ·
        refine ⟨420838829187290936863416857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280559219458193957908944571 420838829187290936863416857)
        ·
          refine ⟨315629121890468202647562643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 420838829187290936863416857 315629121890468202647562643)
          ·
            refine ⟨473443682835702303971343965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315629121890468202647562643 473443682835702303971343965)
            ·
              refine ⟨177541381063388363989253987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 473443682835702303971343965 177541381063388363989253987)
              ·
                refine ⟨266312071595082545983880981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177541381063388363989253987 266312071595082545983880981)
                ·
                  refine ⟨12483378356019494342994421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 266312071595082545983880981 12483378356019494342994421)
                  ·
                    refine ⟨1170316720876827594655727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12483378356019494342994421 1170316720876827594655727)
                    ·
                      rfl

theorem cell23_6837551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 6, 5].length) (baseStart_6837551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6837551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6837551 prefixEnd_6837551 := by exact prefixLift 6837551
  have htrace : WordTrace (prefixWord ++ tailWord_6837551) baseStart_6837551 baseEnd_6837551 := by
    simpa [prefixWord, tailWord_6837551, baseEnd_6837551] using wordTrace_append hprefix tailTrace_6837551
  have hstable : (prefixWord ++ tailWord_6837551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6837551).length < 2 ^ (prefixWord ++ tailWord_6837551).sum := by decide
  have hdescent : baseEnd_6837551 < baseStart_6837551 := by decide
  rcases family_descends (prefixWord ++ tailWord_6837551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6837568 : List Nat := [2, 1, 1, 2, 2, 1, 6, 1, 2, 5]
def baseStart_6837568 : Nat := 118140960795 + 6837568 * 2 ^ 59
def prefixEnd_6837568 : Nat := 4983230072969 + 3 ^ 40 * 6837568 * 2
def baseEnd_6837568 : Nat := 1170319630600536405818201

theorem tailTrace_6837568 : CollatzResearch.WordTrace tailWord_6837568 prefixEnd_6837568 1170319630600536405818201 := by
  unfold tailWord_6837568
  simp only [CollatzResearch.WordTrace]
  refine ⟨124693296446333187244548679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166257728595110916326064905 124693296446333187244548679)
  ·
    refine ⟨187039944669499780866823019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124693296446333187244548679 187039944669499780866823019)
    ·
      refine ⟨280559917004249671300234529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187039944669499780866823019 280559917004249671300234529)
      ·
        refine ⟨210419937753187253475175897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280559917004249671300234529 210419937753187253475175897)
        ·
          refine ⟨157814953314890440106381923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210419937753187253475175897 157814953314890440106381923)
          ·
            refine ⟨236722429972335660159572885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157814953314890440106381923 236722429972335660159572885)
            ·
              refine ⟨11096363904953234069979979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 236722429972335660159572885 11096363904953234069979979)
              ·
                refine ⟨16644545857429851104969969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11096363904953234069979979 16644545857429851104969969)
                ·
                  refine ⟨12483409393072388328727477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16644545857429851104969969 12483409393072388328727477)
                  ·
                    refine ⟨1170319630600536405818201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12483409393072388328727477 1170319630600536405818201)
                    ·
                      rfl

theorem cell23_6837568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 1, 2, 5].length) (baseStart_6837568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6837568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6837568 prefixEnd_6837568 := by exact prefixLift 6837568
  have htrace : WordTrace (prefixWord ++ tailWord_6837568) baseStart_6837568 baseEnd_6837568 := by
    simpa [prefixWord, tailWord_6837568, baseEnd_6837568] using wordTrace_append hprefix tailTrace_6837568
  have hstable : (prefixWord ++ tailWord_6837568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6837568).length < 2 ^ (prefixWord ++ tailWord_6837568).sum := by decide
  have hdescent : baseEnd_6837568 < baseStart_6837568 := by decide
  rcases family_descends (prefixWord ++ tailWord_6837568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6837605 : List Nat := [1, 3, 1, 3, 1, 2, 3, 1, 2, 4, 2]
def baseStart_6837605 : Nat := 118140960795 + 6837605 * 2 ^ 59
def prefixEnd_6837605 : Nat := 4983230072969 + 3 ^ 40 * 6837605 * 2
def baseEnd_6837605 : Nat := 3510977890585825572691933

theorem tailTrace_6837605 : CollatzResearch.WordTrace tailWord_6837605 prefixEnd_6837605 3510977890585825572691933 := by
  unfold tailWord_6837605
  simp only [CollatzResearch.WordTrace]
  refine ⟨249387942393532329808194269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166258628262354886538796179 249387942393532329808194269)
  ·
    refine ⟨93520478397574623678072851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249387942393532329808194269 93520478397574623678072851)
    ·
      refine ⟨140280717596361935517109277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93520478397574623678072851 140280717596361935517109277)
      ·
        refine ⟨52605269098635725818915979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140280717596361935517109277 52605269098635725818915979)
        ·
          refine ⟨78907903647953588728373969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52605269098635725818915979 78907903647953588728373969)
          ·
            refine ⟨59180927735965191546280477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78907903647953588728373969 59180927735965191546280477)
            ·
              refine ⟨22192847900986946829855179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59180927735965191546280477 22192847900986946829855179)
              ·
                refine ⟨33289271851480420244782769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22192847900986946829855179 33289271851480420244782769)
                ·
                  refine ⟨24966953888610315183587077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33289271851480420244782769 24966953888610315183587077)
                  ·
                    refine ⟨4681303854114434096922577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24966953888610315183587077 4681303854114434096922577)
                    ·
                      refine ⟨3510977890585825572691933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4681303854114434096922577 3510977890585825572691933)
                      ·
                        rfl

theorem cell23_6837605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 1, 2, 4, 2].length) (baseStart_6837605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6837605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6837605 prefixEnd_6837605 := by exact prefixLift 6837605
  have htrace : WordTrace (prefixWord ++ tailWord_6837605) baseStart_6837605 baseEnd_6837605 := by
    simpa [prefixWord, tailWord_6837605, baseEnd_6837605] using wordTrace_append hprefix tailTrace_6837605
  have hstable : (prefixWord ++ tailWord_6837605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6837605).length < 2 ^ (prefixWord ++ tailWord_6837605).sum := by decide
  have hdescent : baseEnd_6837605 < baseStart_6837605 := by decide
  rcases family_descends (prefixWord ++ tailWord_6837605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6837625 : List Nat := [1, 2, 1, 3, 2, 1, 5, 1, 2, 2, 3]
def baseStart_6837625 : Nat := 118140960795 + 6837625 * 2 ^ 59
def prefixEnd_6837625 : Nat := 4983230072969 + 3 ^ 40 * 6837625 * 2
def baseEnd_6837625 : Nat := 3510988160198915494441841

theorem tailTrace_6837625 : CollatzResearch.WordTrace tailWord_6837625 prefixEnd_6837625 3510988160198915494441841 := by
  unfold tailWord_6837625
  simp only [CollatzResearch.WordTrace]
  refine ⟨249388671853459873223922329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166259114568973248815948219 249388671853459873223922329)
  ·
    refine ⟨187041503890094904917941747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249388671853459873223922329 187041503890094904917941747)
    ·
      refine ⟨280562255835142357376912621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187041503890094904917941747 280562255835142357376912621)
      ·
        refine ⟨105210845938178384016342233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 280562255835142357376912621 105210845938178384016342233)
        ·
          refine ⟨78908134453633788012256675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105210845938178384016342233 78908134453633788012256675)
          ·
            refine ⟨118362201680450682018385013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78908134453633788012256675 118362201680450682018385013)
            ·
              refine ⟨11096456407542251439223595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 118362201680450682018385013 11096456407542251439223595)
              ·
                refine ⟨16644684611313377158835393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11096456407542251439223595 16644684611313377158835393)
                ·
                  refine ⟨12483513458485032869126545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16644684611313377158835393 12483513458485032869126545)
                  ·
                    refine ⟨9362635093863774651844909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12483513458485032869126545 9362635093863774651844909)
                    ·
                      refine ⟨3510988160198915494441841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9362635093863774651844909 3510988160198915494441841)
                      ·
                        rfl

theorem cell23_6837625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 1, 2, 2, 3].length) (baseStart_6837625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6837625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6837625 prefixEnd_6837625 := by exact prefixLift 6837625
  have htrace : WordTrace (prefixWord ++ tailWord_6837625) baseStart_6837625 baseEnd_6837625 := by
    simpa [prefixWord, tailWord_6837625, baseEnd_6837625] using wordTrace_append hprefix tailTrace_6837625
  have hstable : (prefixWord ++ tailWord_6837625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6837625).length < 2 ^ (prefixWord ++ tailWord_6837625).sum := by decide
  have hdescent : baseEnd_6837625 < baseStart_6837625 := by decide
  rcases family_descends (prefixWord ++ tailWord_6837625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6837631 : List Nat := [1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 8]
def baseStart_6837631 : Nat := 118140960795 + 6837631 * 2 ^ 59
def prefixEnd_6837631 : Nat := 4983230072969 + 3 ^ 40 * 6837631 * 2
def baseEnd_6837631 : Nat := 3510991241082842470966813

theorem tailTrace_6837631 : CollatzResearch.WordTrace tailWord_6837631 prefixEnd_6837631 3510991241082842470966813 := by
  unfold tailWord_6837631
  simp only [CollatzResearch.WordTrace]
  refine ⟨249388890691438136248640747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166259260460958757499093831 249388890691438136248640747)
  ·
    refine ⟨374083336037157204372961121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249388890691438136248640747 374083336037157204372961121)
    ·
      refine ⟨280562502027867903279720841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 374083336037157204372961121 280562502027867903279720841)
      ·
        refine ⟨210421876520900927459790631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280562502027867903279720841 210421876520900927459790631)
        ·
          refine ⟨315632814781351391189685947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210421876520900927459790631 315632814781351391189685947)
          ·
            refine ⟨473449222172027086784528921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315632814781351391189685947 473449222172027086784528921)
            ·
              refine ⟨355086916629020315088396691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 473449222172027086784528921 355086916629020315088396691)
              ·
                refine ⟨532630374943530472632595037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 355086916629020315088396691 532630374943530472632595037)
                ·
                  refine ⟨199736390603823927237223139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 532630374943530472632595037 199736390603823927237223139)
                  ·
                    refine ⟨299604585905735890855834709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 199736390603823927237223139 299604585905735890855834709)
                    ·
                      refine ⟨3510991241082842470966813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 299604585905735890855834709 3510991241082842470966813)
                      ·
                        rfl

theorem cell23_6837631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 8].length) (baseStart_6837631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6837631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6837631 prefixEnd_6837631 := by exact prefixLift 6837631
  have htrace : WordTrace (prefixWord ++ tailWord_6837631) baseStart_6837631 baseEnd_6837631 := by
    simpa [prefixWord, tailWord_6837631, baseEnd_6837631] using wordTrace_append hprefix tailTrace_6837631
  have hstable : (prefixWord ++ tailWord_6837631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6837631).length < 2 ^ (prefixWord ++ tailWord_6837631).sum := by decide
  have hdescent : baseEnd_6837631 < baseStart_6837631 := by decide
  rcases family_descends (prefixWord ++ tailWord_6837631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6837688 : List Nat := [2, 1, 2, 1, 2, 2, 2, 4, 1, 6]
def baseStart_6837688 : Nat := 118140960795 + 6837688 * 2 ^ 59
def prefixEnd_6837688 : Nat := 4983230072969 + 3 ^ 40 * 6837688 * 2
def baseEnd_6837688 : Nat := 1170340169826716249318017

theorem tailTrace_6837688 : CollatzResearch.WordTrace tailWord_6837688 prefixEnd_6837688 1170340169826716249318017 := by
  unfold tailWord_6837688
  simp only [CollatzResearch.WordTrace]
  refine ⟨124695484826115817491732859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166260646434821089988977145 124695484826115817491732859)
  ·
    refine ⟨187043227239173726237599289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124695484826115817491732859 187043227239173726237599289)
    ·
      refine ⟨140282420429380294678199467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187043227239173726237599289 140282420429380294678199467)
      ·
        refine ⟨210423630644070442017299201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140282420429380294678199467 210423630644070442017299201)
        ·
          refine ⟨157817722983052831512974401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210423630644070442017299201 157817722983052831512974401)
          ·
            refine ⟨118363292237289623634730801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157817722983052831512974401 118363292237289623634730801)
            ·
              refine ⟨88772469177967217726048101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118363292237289623634730801 88772469177967217726048101)
              ·
                refine ⟨16644837970868853323634019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88772469177967217726048101 16644837970868853323634019)
                ·
                  refine ⟨24967256956303279985451029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16644837970868853323634019 24967256956303279985451029)
                  ·
                    refine ⟨1170340169826716249318017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24967256956303279985451029 1170340169826716249318017)
                    ·
                      rfl

theorem cell23_6837688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 4, 1, 6].length) (baseStart_6837688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6837688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6837688 prefixEnd_6837688 := by exact prefixLift 6837688
  have htrace : WordTrace (prefixWord ++ tailWord_6837688) baseStart_6837688 baseEnd_6837688 := by
    simpa [prefixWord, tailWord_6837688, baseEnd_6837688] using wordTrace_append hprefix tailTrace_6837688
  have hstable : (prefixWord ++ tailWord_6837688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6837688).length < 2 ^ (prefixWord ++ tailWord_6837688).sum := by decide
  have hdescent : baseEnd_6837688 < baseStart_6837688 := by decide
  rcases family_descends (prefixWord ++ tailWord_6837688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6837705 : List Nat := [1, 2, 1, 1, 2, 1, 3, 6, 2, 4]
def baseStart_6837705 : Nat := 118140960795 + 6837705 * 2 ^ 59
def prefixEnd_6837705 : Nat := 4983230072969 + 3 ^ 40 * 6837705 * 2
def baseEnd_6837705 : Nat := 1170343079550425060480491

theorem tailTrace_6837705 : CollatzResearch.WordTrace tailWord_6837705 prefixEnd_6837705 1170343079550425060480491 := by
  unfold tailWord_6837705
  simp only [CollatzResearch.WordTrace]
  refine ⟨249391589693170046886834569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166261059795446697924556379 249391589693170046886834569)
  ·
    refine ⟨187043692269877535165125927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249391589693170046886834569 187043692269877535165125927)
    ·
      refine ⟨280565538404816302747688891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187043692269877535165125927 280565538404816302747688891)
      ·
        refine ⟨420848307607224454121533337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280565538404816302747688891 420848307607224454121533337)
        ·
          refine ⟨315636230705418340591150003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 420848307607224454121533337 315636230705418340591150003)
          ·
            refine ⟨473454346058127510886725005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315636230705418340591150003 473454346058127510886725005)
            ·
              refine ⟨177545379771797816582521877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 473454346058127510886725005 177545379771797816582521877)
              ·
                refine ⟨8322439676803022652305713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 177545379771797816582521877 8322439676803022652305713)
                ·
                  refine ⟨6241829757602266989229285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8322439676803022652305713 6241829757602266989229285)
                  ·
                    refine ⟨1170343079550425060480491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6241829757602266989229285 1170343079550425060480491)
                    ·
                      rfl

theorem cell23_6837705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 6, 2, 4].length) (baseStart_6837705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6837705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6837705 prefixEnd_6837705 := by exact prefixLift 6837705
  have htrace : WordTrace (prefixWord ++ tailWord_6837705) baseStart_6837705 baseEnd_6837705 := by
    simpa [prefixWord, tailWord_6837705, baseEnd_6837705] using wordTrace_append hprefix tailTrace_6837705
  have hstable : (prefixWord ++ tailWord_6837705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6837705).length < 2 ^ (prefixWord ++ tailWord_6837705).sum := by decide
  have hdescent : baseEnd_6837705 < baseStart_6837705 := by decide
  rcases family_descends (prefixWord ++ tailWord_6837705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6837706 : List Nat := [3, 1, 2, 1, 2, 4, 3, 2, 1, 1, 3]
def baseStart_6837706 : Nat := 118140960795 + 6837706 * 2 ^ 59
def prefixEnd_6837706 : Nat := 4983230072969 + 3 ^ 40 * 6837706 * 2
def baseEnd_6837706 : Nat := 3511029752131929677528969

theorem tailTrace_6837706 : CollatzResearch.WordTrace tailWord_6837706 prefixEnd_6837706 3511029752131929677528969 := by
  unfold tailWord_6837706
  simp only [CollatzResearch.WordTrace]
  refine ⟨62347906541541606014405243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166261084110777616038413981 62347906541541606014405243)
  ·
    refine ⟨93521859812312409021607865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62347906541541606014405243 93521859812312409021607865)
    ·
      refine ⟨70141394859234306766205899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93521859812312409021607865 70141394859234306766205899)
      ·
        refine ⟨105212092288851460149308849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70141394859234306766205899 105212092288851460149308849)
        ·
          refine ⟨78909069216638595111981637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105212092288851460149308849 78909069216638595111981637)
          ·
            refine ⟨14795450478119736583496557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78909069216638595111981637 14795450478119736583496557)
            ·
              refine ⟨5548293929294901218811209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14795450478119736583496557 5548293929294901218811209)
              ·
                refine ⟨4161220446971175914108407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5548293929294901218811209 4161220446971175914108407)
                ·
                  refine ⟨6241830670456763871162611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4161220446971175914108407 6241830670456763871162611)
                  ·
                    refine ⟨9362746005685145806743917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6241830670456763871162611 9362746005685145806743917)
                    ·
                      refine ⟨3511029752131929677528969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9362746005685145806743917 3511029752131929677528969)
                      ·
                        rfl

theorem cell23_6837706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 3, 2, 1, 1, 3].length) (baseStart_6837706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6837706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6837706 prefixEnd_6837706 := by exact prefixLift 6837706
  have htrace : WordTrace (prefixWord ++ tailWord_6837706) baseStart_6837706 baseEnd_6837706 := by
    simpa [prefixWord, tailWord_6837706, baseEnd_6837706] using wordTrace_append hprefix tailTrace_6837706
  have hstable : (prefixWord ++ tailWord_6837706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6837706).length < 2 ^ (prefixWord ++ tailWord_6837706).sum := by decide
  have hdescent : baseEnd_6837706 < baseStart_6837706 := by decide
  rcases family_descends (prefixWord ++ tailWord_6837706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6837722 : List Nat := [3, 1, 1, 2, 3, 3, 1, 3, 2, 4]
def baseStart_6837722 : Nat := 118140960795 + 6837722 * 2 ^ 59
def prefixEnd_6837722 : Nat := 4983230072969 + 3 ^ 40 * 6837722 * 2
def baseEnd_6837722 : Nat := 1170345989274133871642965

theorem tailTrace_6837722 : CollatzResearch.WordTrace tailWord_6837722 prefixEnd_6837722 1170345989274133871642965 := by
  unfold tailWord_6837722
  simp only [CollatzResearch.WordTrace]
  refine ⟨62348052433527114697550855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166261473156072305860135613 62348052433527114697550855)
  ·
    refine ⟨93522078650290672046326283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62348052433527114697550855 93522078650290672046326283)
    ·
      refine ⟨140283117975436008069489425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93522078650290672046326283 140283117975436008069489425)
      ·
        refine ⟨105212338481577006052117069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140283117975436008069489425 105212338481577006052117069)
        ·
          refine ⟨39454626930591377269543901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105212338481577006052117069 39454626930591377269543901)
          ·
            refine ⟨14795485098971766476078963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39454626930591377269543901 14795485098971766476078963)
            ·
              refine ⟨22193227648457649714118445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14795485098971766476078963 22193227648457649714118445)
              ·
                refine ⟨8322460368171618642794417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22193227648457649714118445 8322460368171618642794417)
                ·
                  refine ⟨6241845276128713982095813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8322460368171618642794417 6241845276128713982095813)
                  ·
                    refine ⟨1170345989274133871642965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6241845276128713982095813 1170345989274133871642965)
                    ·
                      rfl

theorem cell23_6837722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 3, 2, 4].length) (baseStart_6837722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6837722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6837722 prefixEnd_6837722 := by exact prefixLift 6837722
  have htrace : WordTrace (prefixWord ++ tailWord_6837722) baseStart_6837722 baseEnd_6837722 := by
    simpa [prefixWord, tailWord_6837722, baseEnd_6837722] using wordTrace_append hprefix tailTrace_6837722
  have hstable : (prefixWord ++ tailWord_6837722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6837722).length < 2 ^ (prefixWord ++ tailWord_6837722).sum := by decide
  have hdescent : baseEnd_6837722 < baseStart_6837722 := by decide
  rcases family_descends (prefixWord ++ tailWord_6837722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6837725 : List Nat := [1, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6]
def baseStart_6837725 : Nat := 118140960795 + 6837725 * 2 ^ 59
def prefixEnd_6837725 : Nat := 4983230072969 + 3 ^ 40 * 6837725 * 2
def baseEnd_6837725 : Nat := 3511039508264365103191381

theorem tailTrace_6837725 : CollatzResearch.WordTrace tailWord_6837725 prefixEnd_6837725 3511039508264365103191381 := by
  unfold tailWord_6837725
  simp only [CollatzResearch.WordTrace]
  refine ⟨249392319153097590302562629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166261546102065060201708419 249392319153097590302562629)
  ·
    refine ⟨46761059841205798181730493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 249392319153097590302562629 46761059841205798181730493)
    ·
      refine ⟨17535397440452174318148935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46761059841205798181730493 17535397440452174318148935)
      ·
        refine ⟨26303096160678261477223403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17535397440452174318148935 26303096160678261477223403)
        ·
          refine ⟨39454644241017392215835105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26303096160678261477223403 39454644241017392215835105)
          ·
            refine ⟨29590983180763044161876329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39454644241017392215835105 29590983180763044161876329)
            ·
              refine ⟨22193237385572283121407247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29590983180763044161876329 22193237385572283121407247)
              ·
                refine ⟨33289856078358424682110871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22193237385572283121407247 33289856078358424682110871)
                ·
                  refine ⟨49934784117537637023166307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33289856078358424682110871 49934784117537637023166307)
                  ·
                    refine ⟨74902176176306455534749461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49934784117537637023166307 74902176176306455534749461)
                    ·
                      refine ⟨3511039508264365103191381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74902176176306455534749461 3511039508264365103191381)
                      ·
                        rfl

theorem cell23_6837725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_6837725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6837725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6837725 prefixEnd_6837725 := by exact prefixLift 6837725
  have htrace : WordTrace (prefixWord ++ tailWord_6837725) baseStart_6837725 baseEnd_6837725 := by
    simpa [prefixWord, tailWord_6837725, baseEnd_6837725] using wordTrace_append hprefix tailTrace_6837725
  have hstable : (prefixWord ++ tailWord_6837725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6837725).length < 2 ^ (prefixWord ++ tailWord_6837725).sum := by decide
  have hdescent : baseEnd_6837725 < baseStart_6837725 := by decide
  rcases family_descends (prefixWord ++ tailWord_6837725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6837745 : List Nat := [1, 2, 2, 2, 3, 2, 1, 1, 3, 3, 3]
def baseStart_6837745 : Nat := 118140960795 + 6837745 * 2 ^ 59
def prefixEnd_6837745 : Nat := 4983230072969 + 3 ^ 40 * 6837745 * 2
def baseEnd_6837745 : Nat := 3511049777877455024941289

theorem tailTrace_6837745 : CollatzResearch.WordTrace tailWord_6837745 prefixEnd_6837745 3511049777877455024941289 := by
  unfold tailWord_6837745
  simp only [CollatzResearch.WordTrace]
  refine ⟨249393048613025133718290689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166262032408683422478860459 249393048613025133718290689)
  ·
    refine ⟨187044786459768850288718017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249393048613025133718290689 187044786459768850288718017)
    ·
      refine ⟨140283589844826637716538513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187044786459768850288718017 140283589844826637716538513)
      ·
        refine ⟨105212692383619978287403885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140283589844826637716538513 105212692383619978287403885)
        ·
          refine ⟨39454759643857491857776457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105212692383619978287403885 39454759643857491857776457)
          ·
            refine ⟨29591069732893118893332343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39454759643857491857776457 29591069732893118893332343)
            ·
              refine ⟨44386604599339678339998515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29591069732893118893332343 44386604599339678339998515)
              ·
                refine ⟨66579906899009517509997773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44386604599339678339998515 66579906899009517509997773)
                ·
                  refine ⟨24967465087128569066249165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66579906899009517509997773 24967465087128569066249165)
                  ·
                    refine ⟨9362799407673213399843437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24967465087128569066249165 9362799407673213399843437)
                    ·
                      refine ⟨3511049777877455024941289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9362799407673213399843437 3511049777877455024941289)
                      ·
                        rfl

theorem cell23_6837745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 3, 3, 3].length) (baseStart_6837745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6837745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6837745 prefixEnd_6837745 := by exact prefixLift 6837745
  have htrace : WordTrace (prefixWord ++ tailWord_6837745) baseStart_6837745 baseEnd_6837745 := by
    simpa [prefixWord, tailWord_6837745, baseEnd_6837745] using wordTrace_append hprefix tailTrace_6837745
  have hstable : (prefixWord ++ tailWord_6837745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6837745).length < 2 ^ (prefixWord ++ tailWord_6837745).sum := by decide
  have hdescent : baseEnd_6837745 < baseStart_6837745 := by decide
  rcases family_descends (prefixWord ++ tailWord_6837745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6837749 : List Nat := [1, 3, 5, 1, 1, 3, 1, 1, 1, 1, 5]
def baseStart_6837749 : Nat := 118140960795 + 6837749 * 2 ^ 59
def prefixEnd_6837749 : Nat := 4983230072969 + 3 ^ 40 * 6837749 * 2
def baseEnd_6837749 : Nat := 3511051831800073009291271

theorem tailTrace_6837749 : CollatzResearch.WordTrace tailWord_6837749 prefixEnd_6837749 3511051831800073009291271 := by
  unfold tailWord_6837749
  simp only [CollatzResearch.WordTrace]
  refine ⟨249393194505010642401436301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166262129670007094934290867 249393194505010642401436301)
  ·
    refine ⟨93522447939378990900538613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249393194505010642401436301 93522447939378990900538613)
    ·
      refine ⟨8767729494316780396925495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 93522447939378990900538613 8767729494316780396925495)
      ·
        refine ⟨13151594241475170595388243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8767729494316780396925495 13151594241475170595388243)
        ·
          refine ⟨19727391362212755893082365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13151594241475170595388243 19727391362212755893082365)
          ·
            refine ⟨7397771760829783459905887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19727391362212755893082365 7397771760829783459905887)
            ·
              refine ⟨11096657641244675189858831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7397771760829783459905887 11096657641244675189858831)
              ·
                refine ⟨16644986461867012784788247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11096657641244675189858831 16644986461867012784788247)
                ·
                  refine ⟨24967479692800519177182371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16644986461867012784788247 24967479692800519177182371)
                  ·
                    refine ⟨37451219539200778765773557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24967479692800519177182371 37451219539200778765773557)
                    ·
                      refine ⟨3511051831800073009291271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37451219539200778765773557 3511051831800073009291271)
                      ·
                        rfl

theorem cell23_6837749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_6837749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6837749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6837749 prefixEnd_6837749 := by exact prefixLift 6837749
  have htrace : WordTrace (prefixWord ++ tailWord_6837749) baseStart_6837749 baseEnd_6837749 := by
    simpa [prefixWord, tailWord_6837749, baseEnd_6837749] using wordTrace_append hprefix tailTrace_6837749
  have hstable : (prefixWord ++ tailWord_6837749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6837749).length < 2 ^ (prefixWord ++ tailWord_6837749).sum := by decide
  have hdescent : baseEnd_6837749 < baseStart_6837749 := by decide
  rcases family_descends (prefixWord ++ tailWord_6837749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6837789 : List Nat := [1, 4, 2, 2, 1, 1, 2, 4, 1, 3, 2]
def baseStart_6837789 : Nat := 118140960795 + 6837789 * 2 ^ 59
def prefixEnd_6837789 : Nat := 4983230072969 + 3 ^ 40 * 6837789 * 2
def baseEnd_6837789 : Nat := 3511072371026252852791087

theorem tailTrace_6837789 : CollatzResearch.WordTrace tailWord_6837789 prefixEnd_6837789 3511072371026252852791087 := by
  unfold tailWord_6837789
  simp only [CollatzResearch.WordTrace]
  refine ⟨249394653424865729232892421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166263102283243819488594947 249394653424865729232892421)
  ·
    refine ⟨46761497517162324231167329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 249394653424865729232892421 46761497517162324231167329)
    ·
      refine ⟨35071123137871743173375497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46761497517162324231167329 35071123137871743173375497)
      ·
        refine ⟨26303342353403807380031623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35071123137871743173375497 26303342353403807380031623)
        ·
          refine ⟨39455013530105711070047435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26303342353403807380031623 39455013530105711070047435)
          ·
            refine ⟨59182520295158566605071153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39455013530105711070047435 59182520295158566605071153)
            ·
              refine ⟨44386890221368924953803365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59182520295158566605071153 44386890221368924953803365)
              ·
                refine ⟨8322541916506673428838131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44386890221368924953803365 8322541916506673428838131)
                ·
                  refine ⟨12483812874760010143257197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8322541916506673428838131 12483812874760010143257197)
                  ·
                    refine ⟨4681429828035003803721449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12483812874760010143257197 4681429828035003803721449)
                    ·
                      refine ⟨3511072371026252852791087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4681429828035003803721449 3511072371026252852791087)
                      ·
                        rfl

theorem cell23_6837789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 4, 1, 3, 2].length) (baseStart_6837789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6837789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6837789 prefixEnd_6837789 := by exact prefixLift 6837789
  have htrace : WordTrace (prefixWord ++ tailWord_6837789) baseStart_6837789 baseEnd_6837789 := by
    simpa [prefixWord, tailWord_6837789, baseEnd_6837789] using wordTrace_append hprefix tailTrace_6837789
  have hstable : (prefixWord ++ tailWord_6837789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6837789).length < 2 ^ (prefixWord ++ tailWord_6837789).sum := by decide
  have hdescent : baseEnd_6837789 < baseStart_6837789 := by decide
  rcases family_descends (prefixWord ++ tailWord_6837789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6837806 : List Nat := [4, 1, 3, 1, 2, 2, 1, 3, 1, 3, 2]
def baseStart_6837806 : Nat := 118140960795 + 6837806 * 2 ^ 59
def prefixEnd_6837806 : Nat := 4983230072969 + 3 ^ 40 * 6837806 * 2
def baseEnd_6837806 : Nat := 3511081100197379286278509

theorem tailTrace_6837806 : CollatzResearch.WordTrace tailWord_6837806 prefixEnd_6837806 3511081100197379286278509 := by
  unfold tailWord_6837806
  simp only [CollatzResearch.WordTrace]
  refine ⟨31174409183225517642032659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166263515643869427424174181 31174409183225517642032659)
  ·
    refine ⟨46761613774838276463048989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31174409183225517642032659 46761613774838276463048989)
    ·
      refine ⟨17535605165564353673643371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46761613774838276463048989 17535605165564353673643371)
      ·
        refine ⟨26303407748346530510465057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17535605165564353673643371 26303407748346530510465057)
        ·
          refine ⟨19727555811259897882848793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26303407748346530510465057 19727555811259897882848793)
          ·
            refine ⟨14795666858444923412136595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19727555811259897882848793 14795666858444923412136595)
            ·
              refine ⟨22193500287667385118204893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14795666858444923412136595 22193500287667385118204893)
              ·
                refine ⟨8322562607875269419326835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22193500287667385118204893 8322562607875269419326835)
                ·
                  refine ⟨12483843911812904128990253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8322562607875269419326835 12483843911812904128990253)
                  ·
                    refine ⟨4681441466929839048371345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12483843911812904128990253 4681441466929839048371345)
                    ·
                      refine ⟨3511081100197379286278509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4681441466929839048371345 3511081100197379286278509)
                      ·
                        rfl

theorem cell23_6837806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 3, 1, 3, 2].length) (baseStart_6837806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6837806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6837806 prefixEnd_6837806 := by exact prefixLift 6837806
  have htrace : WordTrace (prefixWord ++ tailWord_6837806) baseStart_6837806 baseEnd_6837806 := by
    simpa [prefixWord, tailWord_6837806, baseEnd_6837806] using wordTrace_append hprefix tailTrace_6837806
  have hstable : (prefixWord ++ tailWord_6837806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6837806).length < 2 ^ (prefixWord ++ tailWord_6837806).sum := by decide
  have hdescent : baseEnd_6837806 < baseStart_6837806 := by decide
  rcases family_descends (prefixWord ++ tailWord_6837806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6837808 : List Nat := [2, 1, 1, 1, 2, 3, 1, 1, 11]
def baseStart_6837808 : Nat := 118140960795 + 6837808 * 2 ^ 59
def prefixEnd_6837808 : Nat := 4983230072969 + 3 ^ 40 * 6837808 * 2
def baseEnd_6837808 : Nat := 390120236350965364272611

theorem tailTrace_6837808 : CollatzResearch.WordTrace tailWord_6837808 prefixEnd_6837808 390120236350965364272611 := by
  unfold tailWord_6837808
  simp only [CollatzResearch.WordTrace]
  refine ⟨124697673205898447738917039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166263564274531263651889385 124697673205898447738917039)
  ·
    refine ⟨187046509808847671608375559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124697673205898447738917039 187046509808847671608375559)
    ·
      refine ⟨280569764713271507412563339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187046509808847671608375559 280569764713271507412563339)
      ·
        refine ⟨420854647069907261118845009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280569764713271507412563339 420854647069907261118845009)
        ·
          refine ⟨315640985302430445839133757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 420854647069907261118845009 315640985302430445839133757)
          ·
            refine ⟨118365369488411417189675159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 315640985302430445839133757 118365369488411417189675159)
            ·
              refine ⟨177548054232617125784512739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118365369488411417189675159 177548054232617125784512739)
              ·
                refine ⟨266322081348925688676769109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177548054232617125784512739 266322081348925688676769109)
                ·
                  refine ⟨390120236350965364272611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 266322081348925688676769109 390120236350965364272611)
                  ·
                    rfl

theorem cell23_6837808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 11].length) (baseStart_6837808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6837808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6837808 prefixEnd_6837808 := by exact prefixLift 6837808
  have htrace : WordTrace (prefixWord ++ tailWord_6837808) baseStart_6837808 baseEnd_6837808 := by
    simpa [prefixWord, tailWord_6837808, baseEnd_6837808] using wordTrace_append hprefix tailTrace_6837808
  have hstable : (prefixWord ++ tailWord_6837808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6837808).length < 2 ^ (prefixWord ++ tailWord_6837808).sum := by decide
  have hdescent : baseEnd_6837808 < baseStart_6837808 := by decide
  rcases family_descends (prefixWord ++ tailWord_6837808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6837815 : List Nat := [1, 1, 3, 1, 2, 4, 1, 2, 2, 2, 4]
def baseStart_6837815 : Nat := 118140960795 + 6837815 * 2 ^ 59
def prefixEnd_6837815 : Nat := 4983230072969 + 3 ^ 40 * 6837815 * 2
def baseEnd_6837815 : Nat := 3511085721523269751065967

theorem tailTrace_6837815 : CollatzResearch.WordTrace tailWord_6837815 prefixEnd_6837815 3511085721523269751065967 := by
  unfold tailWord_6837815
  simp only [CollatzResearch.WordTrace]
  refine ⟨249395601722771535673338899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166263734481847690448892599 249395601722771535673338899)
  ·
    refine ⟨374093402584157303510008349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249395601722771535673338899 374093402584157303510008349)
    ·
      refine ⟨140285025969058988816253131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 374093402584157303510008349 140285025969058988816253131)
      ·
        refine ⟨210427538953588483224379697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140285025969058988816253131 210427538953588483224379697)
        ·
          refine ⟨157820654215191362418284773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210427538953588483224379697 157820654215191362418284773)
          ·
            refine ⟨29591372665348380453428395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 157820654215191362418284773 29591372665348380453428395)
            ·
              refine ⟨44387058998022570680142593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29591372665348380453428395 44387058998022570680142593)
              ·
                refine ⟨33290294248516928010106945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44387058998022570680142593 33290294248516928010106945)
                ·
                  refine ⟨24967720686387696007580209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33290294248516928010106945 24967720686387696007580209)
                  ·
                    refine ⟨18725790514790772005685157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24967720686387696007580209 18725790514790772005685157)
                    ·
                      refine ⟨3511085721523269751065967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18725790514790772005685157 3511085721523269751065967)
                      ·
                        rfl

theorem cell23_6837815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 2, 2, 2, 4].length) (baseStart_6837815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6837815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6837815 prefixEnd_6837815 := by exact prefixLift 6837815
  have htrace : WordTrace (prefixWord ++ tailWord_6837815) baseStart_6837815 baseEnd_6837815 := by
    simpa [prefixWord, tailWord_6837815, baseEnd_6837815] using wordTrace_append hprefix tailTrace_6837815
  have hstable : (prefixWord ++ tailWord_6837815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6837815).length < 2 ^ (prefixWord ++ tailWord_6837815).sum := by decide
  have hdescent : baseEnd_6837815 < baseStart_6837815 := by decide
  rcases family_descends (prefixWord ++ tailWord_6837815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6837830 : List Nat := [6, 1, 1, 1, 3, 1, 3, 1, 2, 1, 3]
def baseStart_6837830 : Nat := 118140960795 + 6837830 * 2 ^ 59
def prefixEnd_6837830 : Nat := 4983230072969 + 3 ^ 40 * 6837830 * 2
def baseEnd_6837830 : Nat := 3511093423733087192378399

theorem tailTrace_6837830 : CollatzResearch.WordTrace tailWord_6837830 prefixEnd_6837830 3511093423733087192378399 := by
  unfold tailWord_6837830
  simp only [CollatzResearch.WordTrace]
  refine ⟨7793629650553662288597967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 166264099211811462156756629 7793629650553662288597967)
  ·
    refine ⟨11690444475830493432896951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7793629650553662288597967 11690444475830493432896951)
    ·
      refine ⟨17535666713745740149345427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11690444475830493432896951 17535666713745740149345427)
      ·
        refine ⟨26303500070618610224018141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17535666713745740149345427 26303500070618610224018141)
        ·
          refine ⟨9863812526481978834006803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26303500070618610224018141 9863812526481978834006803)
          ·
            refine ⟨14795718789722968251010205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9863812526481978834006803 14795718789722968251010205)
            ·
              refine ⟨5548394546146113094128827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14795718789722968251010205 5548394546146113094128827)
              ·
                refine ⟨8322591819219169641193241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5548394546146113094128827 8322591819219169641193241)
                ·
                  refine ⟨6241943864414377230894931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8322591819219169641193241 6241943864414377230894931)
                  ·
                    refine ⟨9362915796621565846342397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6241943864414377230894931 9362915796621565846342397)
                    ·
                      refine ⟨3511093423733087192378399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9362915796621565846342397 3511093423733087192378399)
                      ·
                        rfl

theorem cell23_6837830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 3, 1, 2, 1, 3].length) (baseStart_6837830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6837830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6837830 prefixEnd_6837830 := by exact prefixLift 6837830
  have htrace : WordTrace (prefixWord ++ tailWord_6837830) baseStart_6837830 baseEnd_6837830 := by
    simpa [prefixWord, tailWord_6837830, baseEnd_6837830] using wordTrace_append hprefix tailTrace_6837830
  have hstable : (prefixWord ++ tailWord_6837830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6837830).length < 2 ^ (prefixWord ++ tailWord_6837830).sum := by decide
  have hdescent : baseEnd_6837830 < baseStart_6837830 := by decide
  rcases family_descends (prefixWord ++ tailWord_6837830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6837859 : List Nat := [1, 1, 1, 5, 1, 5, 1, 3, 5]
def baseStart_6837859 : Nat := 118140960795 + 6837859 * 2 ^ 59
def prefixEnd_6837859 : Nat := 4983230072969 + 3 ^ 40 * 6837859 * 2
def baseEnd_6837859 : Nat := 390123146074674175435085

theorem tailTrace_6837859 : CollatzResearch.WordTrace tailWord_6837859 prefixEnd_6837859 390123146074674175435085 := by
  unfold tailWord_6837859
  simp only [CollatzResearch.WordTrace]
  refine ⟨249397206534612131187940631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166264804356408087458627087 249397206534612131187940631)
  ·
    refine ⟨374095809801918196781910947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249397206534612131187940631 374095809801918196781910947)
    ·
      refine ⟨561143714702877295172866421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374095809801918196781910947 561143714702877295172866421)
      ·
        refine ⟨52607223253394746422456227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 561143714702877295172866421 52607223253394746422456227)
        ·
          refine ⟨78910834880092119633684341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52607223253394746422456227 78910834880092119633684341)
          ·
            refine ⟨7397890770008636215657907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 78910834880092119633684341 7397890770008636215657907)
            ·
              refine ⟨11096836155012954323486861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7397890770008636215657907 11096836155012954323486861)
              ·
                refine ⟨4161313558129857871307573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11096836155012954323486861 4161313558129857871307573)
                ·
                  refine ⟨390123146074674175435085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4161313558129857871307573 390123146074674175435085)
                  ·
                    rfl

theorem cell23_6837859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 3, 5].length) (baseStart_6837859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6837859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6837859 prefixEnd_6837859 := by exact prefixLift 6837859
  have htrace : WordTrace (prefixWord ++ tailWord_6837859) baseStart_6837859 baseEnd_6837859 := by
    simpa [prefixWord, tailWord_6837859, baseEnd_6837859] using wordTrace_append hprefix tailTrace_6837859
  have hstable : (prefixWord ++ tailWord_6837859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6837859).length < 2 ^ (prefixWord ++ tailWord_6837859).sum := by decide
  have hdescent : baseEnd_6837859 < baseStart_6837859 := by decide
  rcases family_descends (prefixWord ++ tailWord_6837859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6837872 : List Nat := [2, 1, 1, 1, 6, 2, 1, 2, 2, 5]
def baseStart_6837872 : Nat := 118140960795 + 6837872 * 2 ^ 59
def prefixEnd_6837872 : Nat := 4983230072969 + 3 ^ 40 * 6837872 * 2
def baseEnd_6837872 : Nat := 1170371663306858676017735

theorem tailTrace_6837872 : CollatzResearch.WordTrace tailWord_6837872 prefixEnd_6837872 1170371663306858676017735 := by
  unfold tailWord_6837872
  simp only [CollatzResearch.WordTrace]
  refine ⟨124698840341782517204081935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166265120455710022938775913 124698840341782517204081935)
  ·
    refine ⟨187048260512673775806122903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124698840341782517204081935 187048260512673775806122903)
    ·
      refine ⟨280572390769010663709184355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187048260512673775806122903 280572390769010663709184355)
      ·
        refine ⟨420858586153515995563776533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280572390769010663709184355 420858586153515995563776533)
        ·
          refine ⟨19727746225946062292052025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 420858586153515995563776533 19727746225946062292052025)
          ·
            refine ⟨14795809669459546719039019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19727746225946062292052025 14795809669459546719039019)
            ·
              refine ⟨22193714504189320078558529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14795809669459546719039019 22193714504189320078558529)
              ·
                refine ⟨16645285878141990058918897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22193714504189320078558529 16645285878141990058918897)
                ·
                  refine ⟨12483964408606492544189173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16645285878141990058918897 12483964408606492544189173)
                  ·
                    refine ⟨1170371663306858676017735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12483964408606492544189173 1170371663306858676017735)
                    ·
                      rfl

theorem cell23_6837872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 2, 2, 5].length) (baseStart_6837872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6837872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6837872 prefixEnd_6837872 := by exact prefixLift 6837872
  have htrace : WordTrace (prefixWord ++ tailWord_6837872) baseStart_6837872 baseEnd_6837872 := by
    simpa [prefixWord, tailWord_6837872, baseEnd_6837872] using wordTrace_append hprefix tailTrace_6837872
  have hstable : (prefixWord ++ tailWord_6837872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6837872).length < 2 ^ (prefixWord ++ tailWord_6837872).sum := by decide
  have hdescent : baseEnd_6837872 < baseStart_6837872 := by decide
  rcases family_descends (prefixWord ++ tailWord_6837872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6837935 : List Nat := [1, 1, 2, 1, 2, 4, 2, 1, 1, 2, 6]
def baseStart_6837935 : Nat := 118140960795 + 6837935 * 2 ^ 59
def prefixEnd_6837935 : Nat := 4983230072969 + 3 ^ 40 * 6837935 * 2
def baseEnd_6837935 : Nat := 3511147339201809281565415

theorem tailTrace_6837935 : CollatzResearch.WordTrace tailWord_6837935 prefixEnd_6837935 3511147339201809281565415 := by
  unfold tailWord_6837935
  simp only [CollatzResearch.WordTrace]
  refine ⟨249399978482336796167707259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166266652321557864111804839 249399978482336796167707259)
  ·
    refine ⟨374099967723505194251560889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249399978482336796167707259 374099967723505194251560889)
    ·
      refine ⟨280574975792628895688670667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 374099967723505194251560889 280574975792628895688670667)
      ·
        refine ⟨420862463688943343533006001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280574975792628895688670667 420862463688943343533006001)
        ·
          refine ⟨315646847766707507649754501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 420862463688943343533006001 315646847766707507649754501)
          ·
            refine ⟨59183783956257657684328969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 315646847766707507649754501 59183783956257657684328969)
            ·
              refine ⟨44387837967193243263246727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59183783956257657684328969 44387837967193243263246727)
              ·
                refine ⟨66581756950789864894870091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44387837967193243263246727 66581756950789864894870091)
                ·
                  refine ⟨99872635426184797342305137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66581756950789864894870091 99872635426184797342305137)
                  ·
                    refine ⟨74904476569638598006728853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 99872635426184797342305137 74904476569638598006728853)
                    ·
                      refine ⟨3511147339201809281565415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74904476569638598006728853 3511147339201809281565415)
                      ·
                        rfl

theorem cell23_6837935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 2, 6].length) (baseStart_6837935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6837935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6837935 prefixEnd_6837935 := by exact prefixLift 6837935
  have htrace : WordTrace (prefixWord ++ tailWord_6837935) baseStart_6837935 baseEnd_6837935 := by
    simpa [prefixWord, tailWord_6837935, baseEnd_6837935] using wordTrace_append hprefix tailTrace_6837935
  have hstable : (prefixWord ++ tailWord_6837935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6837935).length < 2 ^ (prefixWord ++ tailWord_6837935).sum := by decide
  have hdescent : baseEnd_6837935 < baseStart_6837935 := by decide
  rcases family_descends (prefixWord ++ tailWord_6837935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6837936 : List Nat := [2, 1, 1, 1, 2, 1, 8, 2, 1, 4]
def baseStart_6837936 : Nat := 118140960795 + 6837936 * 2 ^ 59
def prefixEnd_6837936 : Nat := 4983230072969 + 3 ^ 40 * 6837936 * 2
def baseEnd_6837936 : Nat := 1170382617560821259217637

theorem tailTrace_6837936 : CollatzResearch.WordTrace tailWord_6837936 prefixEnd_6837936 1170382617560821259217637 := by
  unfold tailWord_6837936
  simp only [CollatzResearch.WordTrace]
  refine ⟨124700007477666586669246831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166266676636888782225662441 124700007477666586669246831)
  ·
    refine ⟨187050011216499880003870247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124700007477666586669246831 187050011216499880003870247)
    ·
      refine ⟨280575016824749820005805371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187050011216499880003870247 280575016824749820005805371)
      ·
        refine ⟨420862525237124730008708057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280575016824749820005805371 420862525237124730008708057)
        ·
          refine ⟨315646893927843547506531043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 420862525237124730008708057 315646893927843547506531043)
          ·
            refine ⟨473470340891765321259796565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315646893927843547506531043 473470340891765321259796565)
            ·
              refine ⟨5548480557325374858513241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 473470340891765321259796565 5548480557325374858513241)
              ·
                refine ⟨4161360417994031143884931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5548480557325374858513241 4161360417994031143884931)
                ·
                  refine ⟨6242040626991046715827397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4161360417994031143884931 6242040626991046715827397)
                  ·
                    refine ⟨1170382617560821259217637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6242040626991046715827397 1170382617560821259217637)
                    ·
                      rfl

theorem cell23_6837936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 8, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 8, 2, 1, 4].length) (baseStart_6837936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6837936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6837936 prefixEnd_6837936 := by exact prefixLift 6837936
  have htrace : WordTrace (prefixWord ++ tailWord_6837936) baseStart_6837936 baseEnd_6837936 := by
    simpa [prefixWord, tailWord_6837936, baseEnd_6837936] using wordTrace_append hprefix tailTrace_6837936
  have hstable : (prefixWord ++ tailWord_6837936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6837936).length < 2 ^ (prefixWord ++ tailWord_6837936).sum := by decide
  have hdescent : baseEnd_6837936 < baseStart_6837936 := by decide
  rcases family_descends (prefixWord ++ tailWord_6837936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6837959 : List Nat := [1, 1, 4, 1, 1, 1, 5, 2, 3, 1, 3]
def baseStart_6837959 : Nat := 118140960795 + 6837959 * 2 ^ 59
def prefixEnd_6837959 : Nat := 4983230072969 + 3 ^ 40 * 6837959 * 2
def baseEnd_6837959 : Nat := 3511159662737517187665305

theorem tailTrace_6837959 : CollatzResearch.WordTrace tailWord_6837959 prefixEnd_6837959 3511159662737517187665305 := by
  unfold tailWord_6837959
  simp only [CollatzResearch.WordTrace]
  refine ⟨249400853834249848266580931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166267235889499898844387287 249400853834249848266580931)
  ·
    refine ⟨374101280751374772399871397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249400853834249848266580931 374101280751374772399871397)
    ·
      refine ⟨70143990140882769824975887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 374101280751374772399871397 70143990140882769824975887)
      ·
        refine ⟨105215985211324154737463831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70143990140882769824975887 105215985211324154737463831)
        ·
          refine ⟨157823977816986232106195747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105215985211324154737463831 157823977816986232106195747)
          ·
            refine ⟨236735966725479348159293621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157823977816986232106195747 236735966725479348159293621)
            ·
              refine ⟨22193996880513688889933777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 236735966725479348159293621 22193996880513688889933777)
              ·
                refine ⟨16645497660385266667450333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22193996880513688889933777 16645497660385266667450333)
                ·
                  refine ⟨6242061622644475000293875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16645497660385266667450333 6242061622644475000293875)
                  ·
                    refine ⟨9363092433966712500440813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6242061622644475000293875 9363092433966712500440813)
                    ·
                      refine ⟨3511159662737517187665305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9363092433966712500440813 3511159662737517187665305)
                      ·
                        rfl

theorem cell23_6837959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 2, 3, 1, 3].length) (baseStart_6837959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6837959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6837959 prefixEnd_6837959 := by exact prefixLift 6837959
  have htrace : WordTrace (prefixWord ++ tailWord_6837959) baseStart_6837959 baseEnd_6837959 := by
    simpa [prefixWord, tailWord_6837959, baseEnd_6837959] using wordTrace_append hprefix tailTrace_6837959
  have hstable : (prefixWord ++ tailWord_6837959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6837959).length < 2 ^ (prefixWord ++ tailWord_6837959).sum := by decide
  have hdescent : baseEnd_6837959 < baseStart_6837959 := by decide
  rcases family_descends (prefixWord ++ tailWord_6837959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6837969 : List Nat := [1, 2, 2, 1, 2, 5, 1, 1, 1, 5, 2]
def baseStart_6837969 : Nat := 118140960795 + 6837969 * 2 ^ 59
def prefixEnd_6837969 : Nat := 4983230072969 + 3 ^ 40 * 6837969 * 2
def baseEnd_6837969 : Nat := 3511164797544062148540259

theorem tailTrace_6837969 : CollatzResearch.WordTrace tailWord_6837969 prefixEnd_6837969 3511164797544062148540259 := by
  unfold tailWord_6837969
  simp only [CollatzResearch.WordTrace]
  refine ⟨249401218564213619974444961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166267479042809079982963307 249401218564213619974444961)
  ·
    refine ⟨187050913923160214980833721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249401218564213619974444961 187050913923160214980833721)
    ·
      refine ⟨140288185442370161235625291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187050913923160214980833721 140288185442370161235625291)
      ·
        refine ⟨210432278163555241853437937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140288185442370161235625291 210432278163555241853437937)
        ·
          refine ⟨157824208622666431390078453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210432278163555241853437937 157824208622666431390078453)
          ·
            refine ⟨14796019558374977942819855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 157824208622666431390078453 14796019558374977942819855)
            ·
              refine ⟨22194029337562466914229783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14796019558374977942819855 22194029337562466914229783)
              ·
                refine ⟨33291044006343700371344675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22194029337562466914229783 33291044006343700371344675)
                ·
                  refine ⟨49936566009515550557017013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33291044006343700371344675 49936566009515550557017013)
                  ·
                    refine ⟨4681553063392082864720345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49936566009515550557017013 4681553063392082864720345)
                    ·
                      refine ⟨3511164797544062148540259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4681553063392082864720345 3511164797544062148540259)
                      ·
                        rfl

theorem cell23_6837969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 1, 1, 5, 2].length) (baseStart_6837969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6837969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6837969 prefixEnd_6837969 := by exact prefixLift 6837969
  have htrace : WordTrace (prefixWord ++ tailWord_6837969) baseStart_6837969 baseEnd_6837969 := by
    simpa [prefixWord, tailWord_6837969, baseEnd_6837969] using wordTrace_append hprefix tailTrace_6837969
  have hstable : (prefixWord ++ tailWord_6837969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6837969).length < 2 ^ (prefixWord ++ tailWord_6837969).sum := by decide
  have hdescent : baseEnd_6837969 < baseStart_6837969 := by decide
  rcases family_descends (prefixWord ++ tailWord_6837969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6838012 : List Nat := [2, 2, 2, 1, 3, 1, 3, 1, 1, 1, 6]
def baseStart_6838012 : Nat := 118140960795 + 6838012 * 2 ^ 59
def prefixEnd_6838012 : Nat := 4983230072969 + 3 ^ 40 * 6838012 * 2
def baseEnd_6838012 : Nat := 3511186877212205480302561

theorem tailTrace_6838012 : CollatzResearch.WordTrace tailWord_6838012 prefixEnd_6838012 3511186877212205480302561 := by
  unfold tailWord_6838012
  simp only [CollatzResearch.WordTrace]
  refine ⟨124701393451528919159130145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166268524602038558878840193 124701393451528919159130145)
  ·
    refine ⟨93526045088646689369347609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124701393451528919159130145 93526045088646689369347609)
    ·
      refine ⟨70144533816485017027010707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93526045088646689369347609 70144533816485017027010707)
      ·
        refine ⟨105216800724727525540516061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70144533816485017027010707 105216800724727525540516061)
        ·
          refine ⟨39456300271772822077693523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105216800724727525540516061 39456300271772822077693523)
          ·
            refine ⟨59184450407659233116540285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39456300271772822077693523 59184450407659233116540285)
            ·
              refine ⟨22194168902872212418702607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59184450407659233116540285 22194168902872212418702607)
              ·
                refine ⟨33291253354308318628053911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22194168902872212418702607 33291253354308318628053911)
                ·
                  refine ⟨49936880031462477942080867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33291253354308318628053911 49936880031462477942080867)
                  ·
                    refine ⟨74905320047193716913121301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49936880031462477942080867 74905320047193716913121301)
                    ·
                      refine ⟨3511186877212205480302561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74905320047193716913121301 3511186877212205480302561)
                      ·
                        rfl

theorem cell23_6838012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 1, 1, 1, 6].length) (baseStart_6838012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6838012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6838012 prefixEnd_6838012 := by exact prefixLift 6838012
  have htrace : WordTrace (prefixWord ++ tailWord_6838012) baseStart_6838012 baseEnd_6838012 := by
    simpa [prefixWord, tailWord_6838012, baseEnd_6838012] using wordTrace_append hprefix tailTrace_6838012
  have hstable : (prefixWord ++ tailWord_6838012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6838012).length < 2 ^ (prefixWord ++ tailWord_6838012).sum := by decide
  have hdescent : baseEnd_6838012 < baseStart_6838012 := by decide
  rcases family_descends (prefixWord ++ tailWord_6838012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6838019 : List Nat := [1, 1, 1, 3, 2, 2, 3, 4, 1, 2, 3]
def baseStart_6838019 : Nat := 118140960795 + 6838019 * 2 ^ 59
def prefixEnd_6838019 : Nat := 4983230072969 + 3 ^ 40 * 6838019 * 2
def baseEnd_6838019 : Nat := 3511190471576786952915029

theorem tailTrace_6838019 : CollatzResearch.WordTrace tailWord_6838019 prefixEnd_6838019 3511190471576786952915029 := by
  unfold tailWord_6838019
  simp only [CollatzResearch.WordTrace]
  refine ⟨249403042214032478513765111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166268694809354985675843407 249403042214032478513765111)
  ·
    refine ⟨374104563321048717770647667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249403042214032478513765111 374104563321048717770647667)
    ·
      refine ⟨561156844981573076655971501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374104563321048717770647667 561156844981573076655971501)
      ·
        refine ⟨210433816868089903745989313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 561156844981573076655971501 210433816868089903745989313)
        ·
          refine ⟨157825362651067427809491985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210433816868089903745989313 157825362651067427809491985)
          ·
            refine ⟨118369021988300570857118989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157825362651067427809491985 118369021988300570857118989)
            ·
              refine ⟨44388383245612714071419621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118369021988300570857118989 44388383245612714071419621)
              ·
                refine ⟨8322821858552383888391179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44388383245612714071419621 8322821858552383888391179)
                ·
                  refine ⟨12484232787828575832586769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8322821858552383888391179 12484232787828575832586769)
                  ·
                    refine ⟨9363174590871431874440077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12484232787828575832586769 9363174590871431874440077)
                    ·
                      refine ⟨3511190471576786952915029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9363174590871431874440077 3511190471576786952915029)
                      ·
                        rfl

theorem cell23_6838019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 4, 1, 2, 3].length) (baseStart_6838019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6838019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6838019 prefixEnd_6838019 := by exact prefixLift 6838019
  have htrace : WordTrace (prefixWord ++ tailWord_6838019) baseStart_6838019 baseEnd_6838019 := by
    simpa [prefixWord, tailWord_6838019, baseEnd_6838019] using wordTrace_append hprefix tailTrace_6838019
  have hstable : (prefixWord ++ tailWord_6838019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6838019).length < 2 ^ (prefixWord ++ tailWord_6838019).sum := by decide
  have hdescent : baseEnd_6838019 < baseStart_6838019 := by decide
  rcases family_descends (prefixWord ++ tailWord_6838019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6838070 : List Nat := [5, 1, 2, 2, 1, 3, 1, 2, 1, 2, 3]
def baseStart_6838070 : Nat := 118140960795 + 6838070 * 2 ^ 59
def prefixEnd_6838070 : Nat := 4983230072969 + 3 ^ 40 * 6838070 * 2
def baseEnd_6838070 : Nat := 3511216659090166253377295

theorem tailTrace_6838070 : CollatzResearch.WordTrace tailWord_6838070 prefixEnd_6838070 3511216659090166253377295 := by
  unfold tailWord_6838070
  simp only [CollatzResearch.WordTrace]
  refine ⟨15587806396052982138991979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 166269934891231809482581109 15587806396052982138991979)
  ·
    refine ⟨23381709594079473208487969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15587806396052982138991979 23381709594079473208487969)
    ·
      refine ⟨17536282195559604906365977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23381709594079473208487969 17536282195559604906365977)
      ·
        refine ⟨13152211646669703679774483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17536282195559604906365977 13152211646669703679774483)
        ·
          refine ⟨19728317470004555519661725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13152211646669703679774483 19728317470004555519661725)
          ·
            refine ⟨7398119051251708319873147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19728317470004555519661725 7398119051251708319873147)
            ·
              refine ⟨11097178576877562479809721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7398119051251708319873147 11097178576877562479809721)
              ·
                refine ⟨8322883932658171859857291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11097178576877562479809721 8322883932658171859857291)
                ·
                  refine ⟨12484325898987257789785937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8322883932658171859857291 12484325898987257789785937)
                  ·
                    refine ⟨9363244424240443342339453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12484325898987257789785937 9363244424240443342339453)
                    ·
                      refine ⟨3511216659090166253377295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9363244424240443342339453 3511216659090166253377295)
                      ·
                        rfl

theorem cell23_6838070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_6838070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6838070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6838070 prefixEnd_6838070 := by exact prefixLift 6838070
  have htrace : WordTrace (prefixWord ++ tailWord_6838070) baseStart_6838070 baseEnd_6838070 := by
    simpa [prefixWord, tailWord_6838070, baseEnd_6838070] using wordTrace_append hprefix tailTrace_6838070
  have hstable : (prefixWord ++ tailWord_6838070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6838070).length < 2 ^ (prefixWord ++ tailWord_6838070).sum := by decide
  have hdescent : baseEnd_6838070 < baseStart_6838070 := by decide
  rcases family_descends (prefixWord ++ tailWord_6838070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6838119 : List Nat := [1, 1, 5, 1, 2, 1, 3, 1, 2, 2, 4]
def baseStart_6838119 : Nat := 118140960795 + 6838119 * 2 ^ 59
def prefixEnd_6838119 : Nat := 4983230072969 + 3 ^ 40 * 6838119 * 2
def baseEnd_6838119 : Nat := 3511241819642236561664569

theorem tailTrace_6838119 : CollatzResearch.WordTrace tailWord_6838119 prefixEnd_6838119 3511241819642236561664569 := by
  unfold tailWord_6838119
  simp only [CollatzResearch.WordTrace]
  refine ⟨249406689513670195592405411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166271126342446797061603607 249406689513670195592405411)
  ·
    refine ⟨374110034270505293388608117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249406689513670195592405411 374110034270505293388608117)
    ·
      refine ⟨35072815712859871255182011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 374110034270505293388608117 35072815712859871255182011)
      ·
        refine ⟨52609223569289806882773017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35072815712859871255182011 52609223569289806882773017)
        ·
          refine ⟨39456917676967355162079763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52609223569289806882773017 39456917676967355162079763)
          ·
            refine ⟨59185376515451032743119645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39456917676967355162079763 59185376515451032743119645)
            ·
              refine ⟨22194516193294137278669867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59185376515451032743119645 22194516193294137278669867)
              ·
                refine ⟨33291774289941205918004801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22194516193294137278669867 33291774289941205918004801)
                ·
                  refine ⟨24968830717455904438503601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33291774289941205918004801 24968830717455904438503601)
                  ·
                    refine ⟨18726623038091928328877701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24968830717455904438503601 18726623038091928328877701)
                    ·
                      refine ⟨3511241819642236561664569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18726623038091928328877701 3511241819642236561664569)
                      ·
                        rfl

theorem cell23_6838119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_6838119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6838119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6838119 prefixEnd_6838119 := by exact prefixLift 6838119
  have htrace : WordTrace (prefixWord ++ tailWord_6838119) baseStart_6838119 baseEnd_6838119 := by
    simpa [prefixWord, tailWord_6838119, baseEnd_6838119] using wordTrace_append hprefix tailTrace_6838119
  have hstable : (prefixWord ++ tailWord_6838119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6838119).length < 2 ^ (prefixWord ++ tailWord_6838119).sum := by decide
  have hdescent : baseEnd_6838119 < baseStart_6838119 := by decide
  rcases family_descends (prefixWord ++ tailWord_6838119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6838174 : List Nat := [4, 3, 1, 3, 2, 1, 1, 1, 1, 4, 2]
def baseStart_6838174 : Nat := 118140960795 + 6838174 * 2 ^ 59
def prefixEnd_6838174 : Nat := 4983230072969 + 3 ^ 40 * 6838174 * 2
def baseEnd_6838174 : Nat := 3511270061078233846476817

theorem tailTrace_6838174 : CollatzResearch.WordTrace tailWord_6838174 prefixEnd_6838174 3511270061078233846476817 := by
  unfold tailWord_6838174
  simp only [CollatzResearch.WordTrace]
  refine ⟨31176086941058867498207197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166272463685647293323771717 31176086941058867498207197)
  ·
    refine ⟨11691032602897075311827699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31176086941058867498207197 11691032602897075311827699)
    ·
      refine ⟨17536548904345612967741549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11691032602897075311827699 17536548904345612967741549)
      ·
        refine ⟨6576205839129604862903081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17536548904345612967741549 6576205839129604862903081)
        ·
          refine ⟨4932154379347203647177311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6576205839129604862903081 4932154379347203647177311)
          ·
            refine ⟨7398231569020805470765967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4932154379347203647177311 7398231569020805470765967)
            ·
              refine ⟨11097347353531208206148951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7398231569020805470765967 11097347353531208206148951)
              ·
                refine ⟨16646021030296812309223427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11097347353531208206148951 16646021030296812309223427)
                ·
                  refine ⟨24969031545445218463835141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16646021030296812309223427 24969031545445218463835141)
                  ·
                    refine ⟨4681693414770978461969089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24969031545445218463835141 4681693414770978461969089)
                    ·
                      refine ⟨3511270061078233846476817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4681693414770978461969089 3511270061078233846476817)
                      ·
                        rfl

theorem cell23_6838174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_6838174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6838174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6838174 prefixEnd_6838174 := by exact prefixLift 6838174
  have htrace : WordTrace (prefixWord ++ tailWord_6838174) baseStart_6838174 baseEnd_6838174 := by
    simpa [prefixWord, tailWord_6838174, baseEnd_6838174] using wordTrace_append hprefix tailTrace_6838174
  have hstable : (prefixWord ++ tailWord_6838174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6838174).length < 2 ^ (prefixWord ++ tailWord_6838174).sum := by decide
  have hdescent : baseEnd_6838174 < baseStart_6838174 := by decide
  rcases family_descends (prefixWord ++ tailWord_6838174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6838216 : List Nat := [2, 1, 3, 1, 4, 1, 1, 1, 4, 2, 3]
def baseStart_6838216 : Nat := 118140960795 + 6838216 * 2 ^ 59
def prefixEnd_6838216 : Nat := 4983230072969 + 3 ^ 40 * 6838216 * 2
def baseEnd_6838216 : Nat := 3511291627265722682151623

theorem tailTrace_6838216 : CollatzResearch.WordTrace tailWord_6838216 prefixEnd_6838216 3511291627265722682151623 := by
  unfold tailWord_6838216
  simp only [CollatzResearch.WordTrace]
  refine ⟨124705113697159390579343251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166273484929545854105791001 124705113697159390579343251)
  ·
    refine ⟨187057670545739085869014877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124705113697159390579343251 187057670545739085869014877)
    ·
      refine ⟨70146626454652157200880579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187057670545739085869014877 70146626454652157200880579)
      ·
        refine ⟨105219939681978235801320869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70146626454652157200880579 105219939681978235801320869)
        ·
          refine ⟨19728738690370919212747663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105219939681978235801320869 19728738690370919212747663)
          ·
            refine ⟨29593108035556378819121495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19728738690370919212747663 29593108035556378819121495)
            ·
              refine ⟨44389662053334568228682243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29593108035556378819121495 44389662053334568228682243)
              ·
                refine ⟨66584493080001852343023365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44389662053334568228682243 66584493080001852343023365)
                ·
                  refine ⟨12484592452500347314316881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66584493080001852343023365 12484592452500347314316881)
                  ·
                    refine ⟨9363444339375260485737661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12484592452500347314316881 9363444339375260485737661)
                    ·
                      refine ⟨3511291627265722682151623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9363444339375260485737661 3511291627265722682151623)
                      ·
                        rfl

theorem cell23_6838216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 4, 2, 3].length) (baseStart_6838216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6838216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6838216 prefixEnd_6838216 := by exact prefixLift 6838216
  have htrace : WordTrace (prefixWord ++ tailWord_6838216) baseStart_6838216 baseEnd_6838216 := by
    simpa [prefixWord, tailWord_6838216, baseEnd_6838216] using wordTrace_append hprefix tailTrace_6838216
  have hstable : (prefixWord ++ tailWord_6838216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6838216).length < 2 ^ (prefixWord ++ tailWord_6838216).sum := by decide
  have hdescent : baseEnd_6838216 < baseStart_6838216 := by decide
  rcases family_descends (prefixWord ++ tailWord_6838216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6838219 : List Nat := [1, 1, 1, 1, 3, 4, 2, 4, 6]
def baseStart_6838219 : Nat := 118140960795 + 6838219 * 2 ^ 59
def prefixEnd_6838219 : Nat := 4983230072969 + 3 ^ 40 * 6838219 * 2
def baseEnd_6838219 : Nat := 390143685300854018934901

theorem tailTrace_6838219 : CollatzResearch.WordTrace tailWord_6838219 prefixEnd_6838219 390143685300854018934901 := by
  unfold tailWord_6838219
  simp only [CollatzResearch.WordTrace]
  refine ⟨249410336813307912671045711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166273557875538608447363807 249410336813307912671045711)
  ·
    refine ⟨374115505219961869006568567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249410336813307912671045711 374115505219961869006568567)
    ·
      refine ⟨561173257829942803509852851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374115505219961869006568567 561173257829942803509852851)
      ·
        refine ⟨841759886744914205264779277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 561173257829942803509852851 841759886744914205264779277)
        ·
          refine ⟨315659957529342826974292229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 841759886744914205264779277 315659957529342826974292229)
          ·
            refine ⟨59186242036751780057679793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 315659957529342826974292229 59186242036751780057679793)
            ·
              refine ⟨44389681527563835043259845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59186242036751780057679793 44389681527563835043259845)
              ·
                refine ⟨8323065286418219070611221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44389681527563835043259845 8323065286418219070611221)
                ·
                  refine ⟨390143685300854018934901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8323065286418219070611221 390143685300854018934901)
                  ·
                    rfl

theorem cell23_6838219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 4, 6].length) (baseStart_6838219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6838219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6838219 prefixEnd_6838219 := by exact prefixLift 6838219
  have htrace : WordTrace (prefixWord ++ tailWord_6838219) baseStart_6838219 baseEnd_6838219 := by
    simpa [prefixWord, tailWord_6838219, baseEnd_6838219] using wordTrace_append hprefix tailTrace_6838219
  have hstable : (prefixWord ++ tailWord_6838219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6838219).length < 2 ^ (prefixWord ++ tailWord_6838219).sum := by decide
  have hdescent : baseEnd_6838219 < baseStart_6838219 := by decide
  rcases family_descends (prefixWord ++ tailWord_6838219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6838256 : List Nat := [2, 1, 1, 1, 3, 2, 2, 3, 1, 5, 2]
def baseStart_6838256 : Nat := 118140960795 + 6838256 * 2 ^ 59
def prefixEnd_6838256 : Nat := 4983230072969 + 3 ^ 40 * 6838256 * 2
def baseEnd_6838256 : Nat := 3511312166491902525651439

theorem tailTrace_6838256 : CollatzResearch.WordTrace tailWord_6838256 prefixEnd_6838256 3511312166491902525651439 := by
  unfold tailWord_6838256
  simp only [CollatzResearch.WordTrace]
  refine ⟨124705843157086933995071311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166274457542782578660095081 124705843157086933995071311)
  ·
    refine ⟨187058764735630400992606967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124705843157086933995071311 187058764735630400992606967)
    ·
      refine ⟨280588147103445601488910451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187058764735630400992606967 280588147103445601488910451)
      ·
        refine ⟨420882220655168402233365677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280588147103445601488910451 420882220655168402233365677)
        ·
          refine ⟨157830832745688150837512129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 420882220655168402233365677 157830832745688150837512129)
          ·
            refine ⟨118373124559266113128134097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157830832745688150837512129 118373124559266113128134097)
            ·
              refine ⟨88779843419449584846100573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118373124559266113128134097 88779843419449584846100573)
              ·
                refine ⟨33292441282293594317287715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88779843419449584846100573 33292441282293594317287715)
                ·
                  refine ⟨49938661923440391475931573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33292441282293594317287715 49938661923440391475931573)
                  ·
                    refine ⟨4681749555322536700868585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49938661923440391475931573 4681749555322536700868585)
                    ·
                      refine ⟨3511312166491902525651439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4681749555322536700868585 3511312166491902525651439)
                      ·
                        rfl

theorem cell23_6838256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 3, 1, 5, 2].length) (baseStart_6838256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6838256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6838256 prefixEnd_6838256 := by exact prefixLift 6838256
  have htrace : WordTrace (prefixWord ++ tailWord_6838256) baseStart_6838256 baseEnd_6838256 := by
    simpa [prefixWord, tailWord_6838256, baseEnd_6838256] using wordTrace_append hprefix tailTrace_6838256
  have hstable : (prefixWord ++ tailWord_6838256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6838256).length < 2 ^ (prefixWord ++ tailWord_6838256).sum := by decide
  have hdescent : baseEnd_6838256 < baseStart_6838256 := by decide
  rcases family_descends (prefixWord ++ tailWord_6838256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6838273 : List Nat := [1, 2, 4, 1, 2, 1, 1, 4, 2, 3, 2]
def baseStart_6838273 : Nat := 118140960795 + 6838273 * 2 ^ 59
def prefixEnd_6838273 : Nat := 4983230072969 + 3 ^ 40 * 6838273 * 2
def baseEnd_6838273 : Nat := 3511320895663028959138861

theorem tailTrace_6838273 : CollatzResearch.WordTrace tailWord_6838273 prefixEnd_6838273 3511320895663028959138861 := by
  unfold tailWord_6838273
  simp only [CollatzResearch.WordTrace]
  refine ⟨249412306355112279893511473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166274870903408186595674315 249412306355112279893511473)
  ·
    refine ⟨187059229766334209920133605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249412306355112279893511473 187059229766334209920133605)
    ·
      refine ⟨35073605581187664360025051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 187059229766334209920133605 35073605581187664360025051)
      ·
        refine ⟨52610408371781496540037577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35073605581187664360025051 52610408371781496540037577)
        ·
          refine ⟨39457806278836122405028183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52610408371781496540037577 39457806278836122405028183)
          ·
            refine ⟨59186709418254183607542275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39457806278836122405028183 59186709418254183607542275)
            ·
              refine ⟨88780064127381275411313413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59186709418254183607542275 88780064127381275411313413)
              ·
                refine ⟨16646262023883989139621265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88780064127381275411313413 16646262023883989139621265)
                ·
                  refine ⟨12484696517912991854715949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16646262023883989139621265 12484696517912991854715949)
                  ·
                    refine ⟨4681761194217371945518481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12484696517912991854715949 4681761194217371945518481)
                    ·
                      refine ⟨3511320895663028959138861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4681761194217371945518481 3511320895663028959138861)
                      ·
                        rfl

theorem cell23_6838273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 4, 2, 3, 2].length) (baseStart_6838273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6838273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6838273 prefixEnd_6838273 := by exact prefixLift 6838273
  have htrace : WordTrace (prefixWord ++ tailWord_6838273) baseStart_6838273 baseEnd_6838273 := by
    simpa [prefixWord, tailWord_6838273, baseEnd_6838273] using wordTrace_append hprefix tailTrace_6838273
  have hstable : (prefixWord ++ tailWord_6838273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6838273).length < 2 ^ (prefixWord ++ tailWord_6838273).sum := by decide
  have hdescent : baseEnd_6838273 < baseStart_6838273 := by decide
  rcases family_descends (prefixWord ++ tailWord_6838273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6838280 : List Nat := [2, 1, 3, 2, 1, 2, 3, 4, 1, 1, 3]
def baseStart_6838280 : Nat := 118140960795 + 6838280 * 2 ^ 59
def prefixEnd_6838280 : Nat := 4983230072969 + 3 ^ 40 * 6838280 * 2
def baseEnd_6838280 : Nat := 3511324490027610431751329

theorem tailTrace_6838280 : CollatzResearch.WordTrace tailWord_6838280 prefixEnd_6838280 3511324490027610431751329 := by
  unfold tailWord_6838280
  simp only [CollatzResearch.WordTrace]
  refine ⟨124706280833043460044508147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166275041110724613392677529 124706280833043460044508147)
  ·
    refine ⟨187059421249565190066762221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124706280833043460044508147 187059421249565190066762221)
    ·
      refine ⟨70147282968586946275035833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187059421249565190066762221 70147282968586946275035833)
      ·
        refine ⟨52610462226440209706276875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70147282968586946275035833 52610462226440209706276875)
        ·
          refine ⟨78915693339660314559415313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52610462226440209706276875 78915693339660314559415313)
          ·
            refine ⟨59186770004745235919561485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78915693339660314559415313 59186770004745235919561485)
            ·
              refine ⟨22195038751779463469835557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59186770004745235919561485 22195038751779463469835557)
              ·
                refine ⟨4161569765958649400594167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22195038751779463469835557 4161569765958649400594167)
                ·
                  refine ⟨6242354648937974100891251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4161569765958649400594167 6242354648937974100891251)
                  ·
                    refine ⟨9363531973406961151336877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6242354648937974100891251 9363531973406961151336877)
                    ·
                      refine ⟨3511324490027610431751329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9363531973406961151336877 3511324490027610431751329)
                      ·
                        rfl

theorem cell23_6838280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 4, 1, 1, 3].length) (baseStart_6838280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6838280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6838280 prefixEnd_6838280 := by exact prefixLift 6838280
  have htrace : WordTrace (prefixWord ++ tailWord_6838280) baseStart_6838280 baseEnd_6838280 := by
    simpa [prefixWord, tailWord_6838280, baseEnd_6838280] using wordTrace_append hprefix tailTrace_6838280
  have hstable : (prefixWord ++ tailWord_6838280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6838280).length < 2 ^ (prefixWord ++ tailWord_6838280).sum := by decide
  have hdescent : baseEnd_6838280 < baseStart_6838280 := by decide
  rcases family_descends (prefixWord ++ tailWord_6838280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6838286 : List Nat := [4, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4]
def baseStart_6838286 : Nat := 118140960795 + 6838286 * 2 ^ 59
def prefixEnd_6838286 : Nat := 4983230072969 + 3 ^ 40 * 6838286 * 2
def baseEnd_6838286 : Nat := 3511327570911537408276301

theorem tailTrace_6838286 : CollatzResearch.WordTrace tailWord_6838286 prefixEnd_6838286 3511327570911537408276301 := by
  unfold tailWord_6838286
  simp only [CollatzResearch.WordTrace]
  refine ⟨31176597563008147889216839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166275187002710122075823141 31176597563008147889216839)
  ·
    refine ⟨46764896344512221833825259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31176597563008147889216839 46764896344512221833825259)
    ·
      refine ⟨70147344516768332750737889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46764896344512221833825259 70147344516768332750737889)
      ·
        refine ⟨52610508387576249563053417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70147344516768332750737889 52610508387576249563053417)
        ·
          refine ⟨39457881290682187172290063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52610508387576249563053417 39457881290682187172290063)
          ·
            refine ⟨59186821936023280758435095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39457881290682187172290063 59186821936023280758435095)
            ·
              refine ⟨88780232904034921137652643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59186821936023280758435095 88780232904034921137652643)
              ·
                refine ⟨133170349356052381706478965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88780232904034921137652643 133170349356052381706478965)
                ·
                  refine ⟨12484720252129910784982403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 133170349356052381706478965 12484720252129910784982403)
                  ·
                    refine ⟨18727080378194866177473605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12484720252129910784982403 18727080378194866177473605)
                    ·
                      refine ⟨3511327570911537408276301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18727080378194866177473605 3511327570911537408276301)
                      ·
                        rfl

theorem cell23_6838286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_6838286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6838286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6838286 prefixEnd_6838286 := by exact prefixLift 6838286
  have htrace : WordTrace (prefixWord ++ tailWord_6838286) baseStart_6838286 baseEnd_6838286 := by
    simpa [prefixWord, tailWord_6838286, baseEnd_6838286] using wordTrace_append hprefix tailTrace_6838286
  have hstable : (prefixWord ++ tailWord_6838286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6838286).length < 2 ^ (prefixWord ++ tailWord_6838286).sum := by decide
  have hdescent : baseEnd_6838286 < baseStart_6838286 := by decide
  rcases family_descends (prefixWord ++ tailWord_6838286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6838296 : List Nat := [2, 1, 2, 3, 2, 1, 4, 1, 1, 6]
def baseStart_6838296 : Nat := 118140960795 + 6838296 * 2 ^ 59
def prefixEnd_6838296 : Nat := 4983230072969 + 3 ^ 40 * 6838296 * 2
def baseEnd_6838296 : Nat := 1170444235239360789717085

theorem tailTrace_6838296 : CollatzResearch.WordTrace tailWord_6838296 prefixEnd_6838296 1170444235239360789717085 := by
  unfold tailWord_6838296
  simp only [CollatzResearch.WordTrace]
  refine ⟨124706572617014477410799371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166275430156019303214399161 124706572617014477410799371)
  ·
    refine ⟨187059858925521716116199057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124706572617014477410799371 187059858925521716116199057)
    ·
      refine ⟨140294894194141287087149293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187059858925521716116199057 140294894194141287087149293)
      ·
        refine ⟨52610585322802982657680985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140294894194141287087149293 52610585322802982657680985)
        ·
          refine ⟨39457938992102236993260739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52610585322802982657680985 39457938992102236993260739)
          ·
            refine ⟨59186908488153355489891109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39457938992102236993260739 59186908488153355489891109)
            ·
              refine ⟨11097545341528754154354583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59186908488153355489891109 11097545341528754154354583)
              ·
                refine ⟨16646318012293131231531875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11097545341528754154354583 16646318012293131231531875)
                ·
                  refine ⟨24969477018439696847297813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16646318012293131231531875 24969477018439696847297813)
                  ·
                    refine ⟨1170444235239360789717085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24969477018439696847297813 1170444235239360789717085)
                    ·
                      rfl

theorem cell23_6838296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 1, 1, 6].length) (baseStart_6838296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6838296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6838296 prefixEnd_6838296 := by exact prefixLift 6838296
  have htrace : WordTrace (prefixWord ++ tailWord_6838296) baseStart_6838296 baseEnd_6838296 := by
    simpa [prefixWord, tailWord_6838296, baseEnd_6838296] using wordTrace_append hprefix tailTrace_6838296
  have hstable : (prefixWord ++ tailWord_6838296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6838296).length < 2 ^ (prefixWord ++ tailWord_6838296).sum := by decide
  have hdescent : baseEnd_6838296 < baseStart_6838296 := by decide
  rcases family_descends (prefixWord ++ tailWord_6838296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6838320 : List Nat := [2, 1, 1, 1, 2, 7, 2, 1, 1, 1, 4]
def baseStart_6838320 : Nat := 118140960795 + 6838320 * 2 ^ 59
def prefixEnd_6838320 : Nat := 4983230072969 + 3 ^ 40 * 6838320 * 2
def baseEnd_6838320 : Nat := 3511345029253790275251145

theorem tailTrace_6838320 : CollatzResearch.WordTrace tailWord_6838320 prefixEnd_6838320 3511345029253790275251145 := by
  unfold tailWord_6838320
  simp only [CollatzResearch.WordTrace]
  refine ⟨124707010292971003460236207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166276013723961337946981609 124707010292971003460236207)
  ·
    refine ⟨187060515439456505190354311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124707010292971003460236207 187060515439456505190354311)
    ·
      refine ⟨280590773159184757785531467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187060515439456505190354311 280590773159184757785531467)
      ·
        refine ⟨420886159738777136678297201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280590773159184757785531467 420886159738777136678297201)
        ·
          refine ⟨315664619804082852508722901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 420886159738777136678297201 315664619804082852508722901)
          ·
            refine ⟨7398389526658191855673193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 315664619804082852508722901 7398389526658191855673193)
            ·
              refine ⟨5548792144993643891754895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7398389526658191855673193 5548792144993643891754895)
              ·
                refine ⟨8323188217490465837632343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5548792144993643891754895 8323188217490465837632343)
                ·
                  refine ⟨12484782326235698756448515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8323188217490465837632343 12484782326235698756448515)
                  ·
                    refine ⟨18727173489353548134672773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12484782326235698756448515 18727173489353548134672773)
                    ·
                      refine ⟨3511345029253790275251145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18727173489353548134672773 3511345029253790275251145)
                      ·
                        rfl

theorem cell23_6838320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 2, 1, 1, 1, 4].length) (baseStart_6838320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6838320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6838320 prefixEnd_6838320 := by exact prefixLift 6838320
  have htrace : WordTrace (prefixWord ++ tailWord_6838320) baseStart_6838320 baseEnd_6838320 := by
    simpa [prefixWord, tailWord_6838320, baseEnd_6838320] using wordTrace_append hprefix tailTrace_6838320
  have hstable : (prefixWord ++ tailWord_6838320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6838320).length < 2 ^ (prefixWord ++ tailWord_6838320).sum := by decide
  have hdescent : baseEnd_6838320 < baseStart_6838320 := by decide
  rcases family_descends (prefixWord ++ tailWord_6838320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6838326 : List Nat := [5, 1, 2, 1, 1, 1, 12]
def baseStart_6838326 : Nat := 118140960795 + 6838326 * 2 ^ 59
def prefixEnd_6838326 : Nat := 4983230072969 + 3 ^ 40 * 6838326 * 2
def baseEnd_6838326 : Nat := 43349976668366879651557

theorem tailTrace_6838326 : CollatzResearch.WordTrace tailWord_6838326 prefixEnd_6838326 43349976668366879651557 := by
  unfold tailWord_6838326
  simp only [CollatzResearch.WordTrace]
  refine ⟨15588389963995016871574427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 166276159615946846630127221 15588389963995016871574427)
  ·
    refine ⟨23382584945992525307361641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15588389963995016871574427 23382584945992525307361641)
    ·
      refine ⟨17536938709494393980521231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23382584945992525307361641 17536938709494393980521231)
      ·
        refine ⟨26305408064241590970781847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17536938709494393980521231 26305408064241590970781847)
        ·
          refine ⟨39458112096362386456172771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26305408064241590970781847 39458112096362386456172771)
          ·
            refine ⟨59187168144543579684259157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39458112096362386456172771 59187168144543579684259157)
            ·
              refine ⟨43349976668366879651557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 59187168144543579684259157 43349976668366879651557)
              ·
                rfl

theorem cell23_6838326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 12].length) (baseStart_6838326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6838326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6838326 prefixEnd_6838326 := by exact prefixLift 6838326
  have htrace : WordTrace (prefixWord ++ tailWord_6838326) baseStart_6838326 baseEnd_6838326 := by
    simpa [prefixWord, tailWord_6838326, baseEnd_6838326] using wordTrace_append hprefix tailTrace_6838326
  have hstable : (prefixWord ++ tailWord_6838326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6838326).length < 2 ^ (prefixWord ++ tailWord_6838326).sum := by decide
  have hdescent : baseEnd_6838326 < baseStart_6838326 := by decide
  rcases family_descends (prefixWord ++ tailWord_6838326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6838337 : List Nat := [1, 2, 5, 1, 2, 2, 2, 1, 3, 2, 2]
def baseStart_6838337 : Nat := 118140960795 + 6838337 * 2 ^ 59
def prefixEnd_6838337 : Nat := 4983230072969 + 3 ^ 40 * 6838337 * 2
def baseEnd_6838337 : Nat := 3511353758424916708738567

theorem tailTrace_6838337 : CollatzResearch.WordTrace tailWord_6838337 prefixEnd_6838337 3511353758424916708738567 := by
  unfold tailWord_6838337
  simp only [CollatzResearch.WordTrace]
  refine ⟨249414640626880418823841265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166276427084586945882560843 249414640626880418823841265)
  ·
    refine ⟨187060980470160314117880949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249414640626880418823841265 187060980470160314117880949)
    ·
      refine ⟨17536966919077529448551339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 187060980470160314117880949 17536966919077529448551339)
      ·
        refine ⟨26305450378616294172827009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17536966919077529448551339 26305450378616294172827009)
        ·
          refine ⟨19729087783962220629620257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26305450378616294172827009 19729087783962220629620257)
          ·
            refine ⟨14796815837971665472215193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19729087783962220629620257 14796815837971665472215193)
            ·
              refine ⟨11097611878478749104161395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14796815837971665472215193 11097611878478749104161395)
              ·
                refine ⟨16646417817718123656242093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11097611878478749104161395 16646417817718123656242093)
                ·
                  refine ⟨6242406681644296371090785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16646417817718123656242093 6242406681644296371090785)
                  ·
                    refine ⟨4681805011233222278318089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6242406681644296371090785 4681805011233222278318089)
                    ·
                      refine ⟨3511353758424916708738567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4681805011233222278318089 3511353758424916708738567)
                      ·
                        rfl

theorem cell23_6838337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 1, 3, 2, 2].length) (baseStart_6838337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6838337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6838337 prefixEnd_6838337 := by exact prefixLift 6838337
  have htrace : WordTrace (prefixWord ++ tailWord_6838337) baseStart_6838337 baseEnd_6838337 := by
    simpa [prefixWord, tailWord_6838337, baseEnd_6838337] using wordTrace_append hprefix tailTrace_6838337
  have hstable : (prefixWord ++ tailWord_6838337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6838337).length < 2 ^ (prefixWord ++ tailWord_6838337).sum := by decide
  have hdescent : baseEnd_6838337 < baseStart_6838337 := by decide
  rcases family_descends (prefixWord ++ tailWord_6838337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6838339 : List Nat := [1, 1, 1, 3, 1, 2, 2, 3, 2, 7]
def baseStart_6838339 : Nat := 118140960795 + 6838339 * 2 ^ 59
def prefixEnd_6838339 : Nat := 4983230072969 + 3 ^ 40 * 6838339 * 2
def baseEnd_6838339 : Nat := 1170451595128741900304519

theorem tailTrace_6838339 : CollatzResearch.WordTrace tailWord_6838339 prefixEnd_6838339 1170451595128741900304519 := by
  unfold tailWord_6838339
  simp only [CollatzResearch.WordTrace]
  refine ⟨249414713572873173165414071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166276475715248782110276047 249414713572873173165414071)
  ·
    refine ⟨374122070359309759748121107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249414713572873173165414071 374122070359309759748121107)
    ·
      refine ⟨561183105538964639622181661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374122070359309759748121107 561183105538964639622181661)
      ·
        refine ⟨210443664577111739858318123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 561183105538964639622181661 210443664577111739858318123)
        ·
          refine ⟨315665496865667609787477185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210443664577111739858318123 315665496865667609787477185)
          ·
            refine ⟨236749122649250707340607889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 315665496865667609787477185 236749122649250707340607889)
            ·
              refine ⟨177561841986938030505455917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 236749122649250707340607889 177561841986938030505455917)
              ·
                refine ⟨66585690745101761439545969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 177561841986938030505455917 66585690745101761439545969)
                ·
                  refine ⟨49939268058826321079659477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66585690745101761439545969 49939268058826321079659477)
                  ·
                    refine ⟨1170451595128741900304519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49939268058826321079659477 1170451595128741900304519)
                    ·
                      rfl

theorem cell23_6838339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 2, 7].length) (baseStart_6838339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6838339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6838339 prefixEnd_6838339 := by exact prefixLift 6838339
  have htrace : WordTrace (prefixWord ++ tailWord_6838339) baseStart_6838339 baseEnd_6838339 := by
    simpa [prefixWord, tailWord_6838339, baseEnd_6838339] using wordTrace_append hprefix tailTrace_6838339
  have hstable : (prefixWord ++ tailWord_6838339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6838339).length < 2 ^ (prefixWord ++ tailWord_6838339).sum := by decide
  have hdescent : baseEnd_6838339 < baseStart_6838339 := by decide
  rcases family_descends (prefixWord ++ tailWord_6838339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6838380 : List Nat := [2, 2, 1, 1, 3, 3, 2, 3, 1, 3, 2]
def baseStart_6838380 : Nat := 118140960795 + 6838380 * 2 ^ 59
def prefixEnd_6838380 : Nat := 4983230072969 + 3 ^ 40 * 6838380 * 2
def baseEnd_6838380 : Nat := 3511375838093060040500869

theorem tailTrace_6838380 : CollatzResearch.WordTrace tailWord_6838380 prefixEnd_6838380 3511375838093060040500869 := by
  unfold tailWord_6838380
  simp only [CollatzResearch.WordTrace]
  refine ⟨124708104482862318583828297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166277472643816424778437729 124708104482862318583828297)
  ·
    refine ⟨93531078362146738937871223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124708104482862318583828297 93531078362146738937871223)
    ·
      refine ⟨140296617543220108406806835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93531078362146738937871223 140296617543220108406806835)
      ·
        refine ⟨210444926314830162610210253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140296617543220108406806835 210444926314830162610210253)
        ·
          refine ⟨78916847368061310978828845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 210444926314830162610210253 78916847368061310978828845)
          ·
            refine ⟨29593817763022991617060817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78916847368061310978828845 29593817763022991617060817)
            ·
              refine ⟨22195363322267243712795613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29593817763022991617060817 22195363322267243712795613)
              ·
                refine ⟨8323261245850216392298355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22195363322267243712795613 8323261245850216392298355)
                ·
                  refine ⟨12484891868775324588447533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8323261245850216392298355 12484891868775324588447533)
                  ·
                    refine ⟨4681834450790746720667825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12484891868775324588447533 4681834450790746720667825)
                    ·
                      refine ⟨3511375838093060040500869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4681834450790746720667825 3511375838093060040500869)
                      ·
                        rfl

theorem cell23_6838380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 3, 2].length) (baseStart_6838380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6838380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6838380 prefixEnd_6838380 := by exact prefixLift 6838380
  have htrace : WordTrace (prefixWord ++ tailWord_6838380) baseStart_6838380 baseEnd_6838380 := by
    simpa [prefixWord, tailWord_6838380, baseEnd_6838380] using wordTrace_append hprefix tailTrace_6838380
  have hstable : (prefixWord ++ tailWord_6838380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6838380).length < 2 ^ (prefixWord ++ tailWord_6838380).sum := by decide
  have hdescent : baseEnd_6838380 < baseStart_6838380 := by decide
  rcases family_descends (prefixWord ++ tailWord_6838380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6838414 : List Nat := [4, 1, 1, 3, 3, 2, 1, 2, 1, 3, 2]
def baseStart_6838414 : Nat := 118140960795 + 6838414 * 2 ^ 59
def prefixEnd_6838414 : Nat := 4983230072969 + 3 ^ 40 * 6838414 * 2
def baseEnd_6838414 : Nat := 3511393296435312907475713

theorem tailTrace_6838414 : CollatzResearch.WordTrace tailWord_6838414 prefixEnd_6838414 3511393296435312907475713 := by
  unfold tailWord_6838414
  simp only [CollatzResearch.WordTrace]
  refine ⟨31177181130950182621799287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166278299365067640649596197 31177181130950182621799287)
  ·
    refine ⟨46765771696425273932698931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31177181130950182621799287 46765771696425273932698931)
    ·
      refine ⟨70148657544637910899048397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46765771696425273932698931 70148657544637910899048397)
      ·
        refine ⟨26305746579239216587143149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70148657544637910899048397 26305746579239216587143149)
        ·
          refine ⟨9864654967214706220178681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26305746579239216587143149 9864654967214706220178681)
          ·
            refine ⟨7398491225411029665134011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9864654967214706220178681 7398491225411029665134011)
            ·
              refine ⟨11097736838116544497701017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7398491225411029665134011 11097736838116544497701017)
              ·
                refine ⟨8323302628587408373275763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11097736838116544497701017 8323302628587408373275763)
                ·
                  refine ⟨12484953942881112559913645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8323302628587408373275763 12484953942881112559913645)
                  ·
                    refine ⟨4681857728580417209967617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12484953942881112559913645 4681857728580417209967617)
                    ·
                      refine ⟨3511393296435312907475713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4681857728580417209967617 3511393296435312907475713)
                      ·
                        rfl

theorem cell23_6838414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 2, 1, 3, 2].length) (baseStart_6838414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6838414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6838414 prefixEnd_6838414 := by exact prefixLift 6838414
  have htrace : WordTrace (prefixWord ++ tailWord_6838414) baseStart_6838414 baseEnd_6838414 := by
    simpa [prefixWord, tailWord_6838414, baseEnd_6838414] using wordTrace_append hprefix tailTrace_6838414
  have hstable : (prefixWord ++ tailWord_6838414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6838414).length < 2 ^ (prefixWord ++ tailWord_6838414).sum := by decide
  have hdescent : baseEnd_6838414 < baseStart_6838414 := by decide
  rcases family_descends (prefixWord ++ tailWord_6838414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6838456 : List Nat := [2, 1, 2, 1, 2, 1, 3, 3, 1, 2, 5]
def baseStart_6838456 : Nat := 118140960795 + 6838456 * 2 ^ 59
def prefixEnd_6838456 : Nat := 4983230072969 + 3 ^ 40 * 6838456 * 2
def baseEnd_6838456 : Nat := 3511414862622801743150519

theorem tailTrace_6838456 : CollatzResearch.WordTrace tailWord_6838456 prefixEnd_6838456 3511414862622801743150519 := by
  unfold tailWord_6838456
  simp only [CollatzResearch.WordTrace]
  refine ⟨124709490456724651073711611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166279320608966201431615481 124709490456724651073711611)
  ·
    refine ⟨187064235685086976610567417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124709490456724651073711611 187064235685086976610567417)
    ·
      refine ⟨140298176763815232457925563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187064235685086976610567417 140298176763815232457925563)
      ·
        refine ⟨210447265145722848686888345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140298176763815232457925563 210447265145722848686888345)
        ·
          refine ⟨157835448859292136515166259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210447265145722848686888345 157835448859292136515166259)
          ·
            refine ⟨236753173288938204772749389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157835448859292136515166259 236753173288938204772749389)
            ·
              refine ⟨88782439983351826789781021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 236753173288938204772749389 88782439983351826789781021)
              ·
                refine ⟨33293414993756935046167883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88782439983351826789781021 33293414993756935046167883)
                ·
                  refine ⟨49940122490635402569251825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33293414993756935046167883 49940122490635402569251825)
                  ·
                    refine ⟨37455091867976551926938869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49940122490635402569251825 37455091867976551926938869)
                    ·
                      refine ⟨3511414862622801743150519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37455091867976551926938869 3511414862622801743150519)
                      ·
                        rfl

theorem cell23_6838456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 3, 1, 2, 5].length) (baseStart_6838456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6838456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6838456 prefixEnd_6838456 := by exact prefixLift 6838456
  have htrace : WordTrace (prefixWord ++ tailWord_6838456) baseStart_6838456 baseEnd_6838456 := by
    simpa [prefixWord, tailWord_6838456, baseEnd_6838456] using wordTrace_append hprefix tailTrace_6838456
  have hstable : (prefixWord ++ tailWord_6838456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6838456).length < 2 ^ (prefixWord ++ tailWord_6838456).sum := by decide
  have hdescent : baseEnd_6838456 < baseStart_6838456 := by decide
  rcases family_descends (prefixWord ++ tailWord_6838456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6838460 : List Nat := [2, 2, 2, 3, 3, 1, 1, 1, 2, 3, 3]
def baseStart_6838460 : Nat := 118140960795 + 6838460 * 2 ^ 59
def prefixEnd_6838460 : Nat := 4983230072969 + 3 ^ 40 * 6838460 * 2
def baseEnd_6838460 : Nat := 3511416916545419727500501

theorem tailTrace_6838460 : CollatzResearch.WordTrace tailWord_6838460 prefixEnd_6838460 3511416916545419727500501 := by
  unfold tailWord_6838460
  simp only [CollatzResearch.WordTrace]
  refine ⟨124709563402717405415284417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166279417870289873887045889 124709563402717405415284417)
  ·
    refine ⟨93532172552038054061463313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124709563402717405415284417 93532172552038054061463313)
    ·
      refine ⟨70149129414028540546097485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93532172552038054061463313 70149129414028540546097485)
      ·
        refine ⟨26305923530260702704786557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70149129414028540546097485 26305923530260702704786557)
        ·
          refine ⟨9864721323847763514294959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26305923530260702704786557 9864721323847763514294959)
          ·
            refine ⟨14797081985771645271442439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9864721323847763514294959 14797081985771645271442439)
            ·
              refine ⟨22195622978657467907163659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14797081985771645271442439 22195622978657467907163659)
              ·
                refine ⟨33293434467986201860745489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22195622978657467907163659 33293434467986201860745489)
                ·
                  refine ⟨24970075850989651395559117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33293434467986201860745489 24970075850989651395559117)
                  ·
                    refine ⟨9363778444121119273334669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24970075850989651395559117 9363778444121119273334669)
                    ·
                      refine ⟨3511416916545419727500501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9363778444121119273334669 3511416916545419727500501)
                      ·
                        rfl

theorem cell23_6838460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_6838460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6838460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6838460 prefixEnd_6838460 := by exact prefixLift 6838460
  have htrace : WordTrace (prefixWord ++ tailWord_6838460) baseStart_6838460 baseEnd_6838460 := by
    simpa [prefixWord, tailWord_6838460, baseEnd_6838460] using wordTrace_append hprefix tailTrace_6838460
  have hstable : (prefixWord ++ tailWord_6838460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6838460).length < 2 ^ (prefixWord ++ tailWord_6838460).sum := by decide
  have hdescent : baseEnd_6838460 < baseStart_6838460 := by decide
  rcases family_descends (prefixWord ++ tailWord_6838460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6838483 : List Nat := [1, 1, 1, 2, 1, 1, 1, 3, 6, 4, 2]
def baseStart_6838483 : Nat := 118140960795 + 6838483 * 2 ^ 59
def prefixEnd_6838483 : Nat := 4983230072969 + 3 ^ 40 * 6838483 * 2
def baseEnd_6838483 : Nat := 3511428726600473137512895

theorem tailTrace_6838483 : CollatzResearch.WordTrace tailWord_6838483 prefixEnd_6838483 3511428726600473137512895 := by
  unfold tailWord_6838483
  simp only [CollatzResearch.WordTrace]
  refine ⟨249419965684351485758656103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166279977122900990505770735 249419965684351485758656103)
  ·
    refine ⟨374129948526527228637984155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249419965684351485758656103 374129948526527228637984155)
    ·
      refine ⟨561194922789790842956976233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374129948526527228637984155 561194922789790842956976233)
      ·
        refine ⟨420896192092343132217732175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 561194922789790842956976233 420896192092343132217732175)
        ·
          refine ⟨631344288138514698326598263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 420896192092343132217732175 631344288138514698326598263)
          ·
            refine ⟨947016432207772047489897395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 631344288138514698326598263 947016432207772047489897395)
            ·
              refine ⟨1420524648311658071234846093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 947016432207772047489897395 1420524648311658071234846093)
              ·
                refine ⟨532696743116871776713067285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1420524648311658071234846093 532696743116871776713067285)
                ·
                  refine ⟨24970159833603364533425029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 532696743116871776713067285 24970159833603364533425029)
                  ·
                    refine ⟨4681904968800630850017193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24970159833603364533425029 4681904968800630850017193)
                    ·
                      refine ⟨3511428726600473137512895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4681904968800630850017193 3511428726600473137512895)
                      ·
                        rfl

theorem cell23_6838483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 6, 4, 2].length) (baseStart_6838483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6838483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6838483 prefixEnd_6838483 := by exact prefixLift 6838483
  have htrace : WordTrace (prefixWord ++ tailWord_6838483) baseStart_6838483 baseEnd_6838483 := by
    simpa [prefixWord, tailWord_6838483, baseEnd_6838483] using wordTrace_append hprefix tailTrace_6838483
  have hstable : (prefixWord ++ tailWord_6838483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6838483).length < 2 ^ (prefixWord ++ tailWord_6838483).sum := by decide
  have hdescent : baseEnd_6838483 < baseStart_6838483 := by decide
  rcases family_descends (prefixWord ++ tailWord_6838483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6838496 : List Nat := [2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 6]
def baseStart_6838496 : Nat := 118140960795 + 6838496 * 2 ^ 59
def prefixEnd_6838496 : Nat := 4983230072969 + 3 ^ 40 * 6838496 * 2
def baseEnd_6838496 : Nat := 3511435401848981586650335

theorem tailTrace_6838496 : CollatzResearch.WordTrace tailWord_6838496 prefixEnd_6838496 3511435401848981586650335 := by
  unfold tailWord_6838496
  simp only [CollatzResearch.WordTrace]
  refine ⟨124710219916652194489439671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166280293222202925985919561 124710219916652194489439671)
  ·
    refine ⟨187065329874978291734159507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124710219916652194489439671 187065329874978291734159507)
    ·
      refine ⟨280597994812467437601239261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187065329874978291734159507 280597994812467437601239261)
      ·
        refine ⟨105224248054675289100464723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 280597994812467437601239261 105224248054675289100464723)
        ·
          refine ⟨157836372082012933650697085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105224248054675289100464723 157836372082012933650697085)
          ·
            refine ⟨59188639530754850119011407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157836372082012933650697085 59188639530754850119011407)
            ·
              refine ⟨88782959296132275178517111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59188639530754850119011407 88782959296132275178517111)
              ·
                refine ⟨133174438944198412767775667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88782959296132275178517111 133174438944198412767775667)
                ·
                  refine ⟨199761658416297619151663501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133174438944198412767775667 199761658416297619151663501)
                  ·
                    refine ⟨74910621906111607181873813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 199761658416297619151663501 74910621906111607181873813)
                    ·
                      refine ⟨3511435401848981586650335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74910621906111607181873813 3511435401848981586650335)
                      ·
                        rfl

theorem cell23_6838496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 6].length) (baseStart_6838496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6838496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6838496 prefixEnd_6838496 := by exact prefixLift 6838496
  have htrace : WordTrace (prefixWord ++ tailWord_6838496) baseStart_6838496 baseEnd_6838496 := by
    simpa [prefixWord, tailWord_6838496, baseEnd_6838496] using wordTrace_append hprefix tailTrace_6838496
  have hstable : (prefixWord ++ tailWord_6838496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6838496).length < 2 ^ (prefixWord ++ tailWord_6838496).sum := by decide
  have hdescent : baseEnd_6838496 < baseStart_6838496 := by decide
  rcases family_descends (prefixWord ++ tailWord_6838496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6838610 : List Nat := [3, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5]
def baseStart_6838610 : Nat := 118140960795 + 6838610 * 2 ^ 59
def prefixEnd_6838610 : Nat := 4983230072969 + 3 ^ 40 * 6838610 * 2
def baseEnd_6838610 : Nat := 3511493938643594140624811

theorem tailTrace_6838610 : CollatzResearch.WordTrace tailWord_6838610 prefixEnd_6838610 3511493938643594140624811 := by
  unfold tailWord_6838610
  simp only [CollatzResearch.WordTrace]
  refine ⟨62356149438722846612132321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166283065169927590965686189 62356149438722846612132321)
  ·
    refine ⟨46767112079042134959099241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62356149438722846612132321 46767112079042134959099241)
    ·
      refine ⟨35075334059281601219324431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46767112079042134959099241 35075334059281601219324431)
      ·
        refine ⟨52613001088922401828986647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35075334059281601219324431 52613001088922401828986647)
        ·
          refine ⟨78919501633383602743479971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52613001088922401828986647 78919501633383602743479971)
          ·
            refine ⟨118379252450075404115219957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78919501633383602743479971 118379252450075404115219957)
            ·
              refine ⟨11098054917194569135801871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 118379252450075404115219957 11098054917194569135801871)
              ·
                refine ⟨16647082375791853703702807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11098054917194569135801871 16647082375791853703702807)
                ·
                  refine ⟨24970623563687780555554211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16647082375791853703702807 24970623563687780555554211)
                  ·
                    refine ⟨37455935345531670833331317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24970623563687780555554211 37455935345531670833331317)
                    ·
                      refine ⟨3511493938643594140624811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37455935345531670833331317 3511493938643594140624811)
                      ·
                        rfl

theorem cell23_6838610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5].length) (baseStart_6838610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6838610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6838610 prefixEnd_6838610 := by exact prefixLift 6838610
  have htrace : WordTrace (prefixWord ++ tailWord_6838610) baseStart_6838610 baseEnd_6838610 := by
    simpa [prefixWord, tailWord_6838610, baseEnd_6838610] using wordTrace_append hprefix tailTrace_6838610
  have hstable : (prefixWord ++ tailWord_6838610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6838610).length < 2 ^ (prefixWord ++ tailWord_6838610).sum := by decide
  have hdescent : baseEnd_6838610 < baseStart_6838610 := by decide
  rcases family_descends (prefixWord ++ tailWord_6838610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6838613 : List Nat := [1, 3, 2, 2, 4, 11]
def baseStart_6838613 : Nat := 118140960795 + 6838613 * 2 ^ 59
def prefixEnd_6838613 : Nat := 4983230072969 + 3 ^ 40 * 6838613 * 2
def baseEnd_6838613 : Nat := 14450598679364434686779

theorem tailTrace_6838613 : CollatzResearch.WordTrace tailWord_6838613 prefixEnd_6838613 14450598679364434686779 := by
  unfold tailWord_6838613
  simp only [CollatzResearch.WordTrace]
  refine ⟨249424707173880517960888493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166283138115920345307258995 249424707173880517960888493)
  ·
    refine ⟨93534265190205194235333185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249424707173880517960888493 93534265190205194235333185)
    ·
      refine ⟨70150698892653895676499889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93534265190205194235333185 70150698892653895676499889)
      ·
        refine ⟨52613024169490421757374917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70150698892653895676499889 52613024169490421757374917)
        ·
          refine ⟨9864942031779454079507797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52613024169490421757374917 9864942031779454079507797)
          ·
            refine ⟨14450598679364434686779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 9864942031779454079507797 14450598679364434686779)
            ·
              rfl

theorem cell23_6838613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 11].length) (baseStart_6838613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6838613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6838613 prefixEnd_6838613 := by exact prefixLift 6838613
  have htrace : WordTrace (prefixWord ++ tailWord_6838613) baseStart_6838613 baseEnd_6838613 := by
    simpa [prefixWord, tailWord_6838613, baseEnd_6838613] using wordTrace_append hprefix tailTrace_6838613
  have hstable : (prefixWord ++ tailWord_6838613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6838613).length < 2 ^ (prefixWord ++ tailWord_6838613).sum := by decide
  have hdescent : baseEnd_6838613 < baseStart_6838613 := by decide
  rcases family_descends (prefixWord ++ tailWord_6838613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6838640 : List Nat := [2, 1, 1, 1, 4, 3, 1, 3, 1, 3, 3]
def baseStart_6838640 : Nat := 118140960795 + 6838640 * 2 ^ 59
def prefixEnd_6838640 : Nat := 4983230072969 + 3 ^ 40 * 6838640 * 2
def baseEnd_6838640 : Nat := 3511509343063229023249673

theorem tailTrace_6838640 : CollatzResearch.WordTrace tailWord_6838640 prefixEnd_6838640 3511509343063229023249673 := by
  unfold tailWord_6838640
  simp only [CollatzResearch.WordTrace]
  refine ⟨124712845972391350786060687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166283794629855134381414249 124712845972391350786060687)
  ·
    refine ⟨187069268958587026179091031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124712845972391350786060687 187069268958587026179091031)
    ·
      refine ⟨280603903437880539268636547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187069268958587026179091031 280603903437880539268636547)
      ·
        refine ⟨420905855156820808902954821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280603903437880539268636547 420905855156820808902954821)
        ·
          refine ⟨78919847841903901669304029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 420905855156820808902954821 78919847841903901669304029)
          ·
            refine ⟨29594942940713963125989011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78919847841903901669304029 29594942940713963125989011)
            ·
              refine ⟨44392414411070944688983517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29594942940713963125989011 44392414411070944688983517)
              ·
                refine ⟨16647155404151604258368819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44392414411070944688983517 16647155404151604258368819)
                ·
                  refine ⟨24970733106227406387553229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16647155404151604258368819 24970733106227406387553229)
                  ·
                    refine ⟨9364024914835277395332461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24970733106227406387553229 9364024914835277395332461)
                    ·
                      refine ⟨3511509343063229023249673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9364024914835277395332461 3511509343063229023249673)
                      ·
                        rfl

theorem cell23_6838640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 3, 1, 3, 3].length) (baseStart_6838640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6838640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6838640 prefixEnd_6838640 := by exact prefixLift 6838640
  have htrace : WordTrace (prefixWord ++ tailWord_6838640) baseStart_6838640 baseEnd_6838640 := by
    simpa [prefixWord, tailWord_6838640, baseEnd_6838640] using wordTrace_append hprefix tailTrace_6838640
  have hstable : (prefixWord ++ tailWord_6838640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6838640).length < 2 ^ (prefixWord ++ tailWord_6838640).sum := by decide
  have hdescent : baseEnd_6838640 < baseStart_6838640 := by decide
  rcases family_descends (prefixWord ++ tailWord_6838640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6838657 : List Nat := [1, 2, 4, 3, 1, 1, 2, 2, 1, 3, 3]
def baseStart_6838657 : Nat := 118140960795 + 6838657 * 2 ^ 59
def prefixEnd_6838657 : Nat := 4983230072969 + 3 ^ 40 * 6838657 * 2
def baseEnd_6838657 : Nat := 3511518072234355456737095

theorem tailTrace_6838657 : CollatzResearch.WordTrace tailWord_6838657 prefixEnd_6838657 3511518072234355456737095 := by
  unfold tailWord_6838657
  simp only [CollatzResearch.WordTrace]
  refine ⟨249426311985721113475490225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166284207990480742316993483 249426311985721113475490225)
  ·
    refine ⟨187069733989290835106617669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249426311985721113475490225 187069733989290835106617669)
    ·
      refine ⟨35075575122992031582490813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 187069733989290835106617669 35075575122992031582490813)
      ·
        refine ⟨13153340671122011843434055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35075575122992031582490813 13153340671122011843434055)
        ·
          refine ⟨19730011006683017765151083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13153340671122011843434055 19730011006683017765151083)
          ·
            refine ⟨29595016510024526647726625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19730011006683017765151083 29595016510024526647726625)
            ·
              refine ⟨22196262382518394985794969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29595016510024526647726625 22196262382518394985794969)
              ·
                refine ⟨16647196786888796239346227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22196262382518394985794969 16647196786888796239346227)
                ·
                  refine ⟨24970795180333194359019341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16647196786888796239346227 24970795180333194359019341)
                  ·
                    refine ⟨9364048192624947884632253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24970795180333194359019341 9364048192624947884632253)
                    ·
                      refine ⟨3511518072234355456737095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9364048192624947884632253 3511518072234355456737095)
                      ·
                        rfl

theorem cell23_6838657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_6838657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6838657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6838657 prefixEnd_6838657 := by exact prefixLift 6838657
  have htrace : WordTrace (prefixWord ++ tailWord_6838657) baseStart_6838657 baseEnd_6838657 := by
    simpa [prefixWord, tailWord_6838657, baseEnd_6838657] using wordTrace_append hprefix tailTrace_6838657
  have hstable : (prefixWord ++ tailWord_6838657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6838657).length < 2 ^ (prefixWord ++ tailWord_6838657).sum := by decide
  have hdescent : baseEnd_6838657 < baseStart_6838657 := by decide
  rcases family_descends (prefixWord ++ tailWord_6838657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6838658 : List Nat := [3, 4, 2, 1, 2, 2, 2, 1, 1, 1, 4]
def baseStart_6838658 : Nat := 118140960795 + 6838658 * 2 ^ 59
def prefixEnd_6838658 : Nat := 4983230072969 + 3 ^ 40 * 6838658 * 2
def baseEnd_6838658 : Nat := 3511518585715009952824591

theorem tailTrace_6838658 : CollatzResearch.WordTrace tailWord_6838658 prefixEnd_6838658 3511518585715009952824591 := by
  unfold tailWord_6838658
  simp only [CollatzResearch.WordTrace]
  refine ⟨62356587114679372661569157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166284232305811660430851085 62356587114679372661569157)
  ·
    refine ⟨11691860084002382374044217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62356587114679372661569157 11691860084002382374044217)
    ·
      refine ⟨8768895063001786780533163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11691860084002382374044217 8768895063001786780533163)
      ·
        refine ⟨13153342594502680170799745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8768895063001786780533163 13153342594502680170799745)
        ·
          refine ⟨9865006945877010128099809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13153342594502680170799745 9865006945877010128099809)
          ·
            refine ⟨7398755209407757596074857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9865006945877010128099809 7398755209407757596074857)
            ·
              refine ⟨5549066407055818197056143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7398755209407757596074857 5549066407055818197056143)
              ·
                refine ⟨8323599610583727295584215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5549066407055818197056143 8323599610583727295584215)
                ·
                  refine ⟨12485399415875590943376323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8323599610583727295584215 12485399415875590943376323)
                  ·
                    refine ⟨18728099123813386415064485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12485399415875590943376323 18728099123813386415064485)
                    ·
                      refine ⟨3511518585715009952824591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18728099123813386415064485 3511518585715009952824591)
                      ·
                        rfl

theorem cell23_6838658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_6838658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6838658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6838658 prefixEnd_6838658 := by exact prefixLift 6838658
  have htrace : WordTrace (prefixWord ++ tailWord_6838658) baseStart_6838658 baseEnd_6838658 := by
    simpa [prefixWord, tailWord_6838658, baseEnd_6838658] using wordTrace_append hprefix tailTrace_6838658
  have hstable : (prefixWord ++ tailWord_6838658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6838658).length < 2 ^ (prefixWord ++ tailWord_6838658).sum := by decide
  have hdescent : baseEnd_6838658 < baseStart_6838658 := by decide
  rcases family_descends (prefixWord ++ tailWord_6838658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6838690 : List Nat := [3, 3, 1, 2, 1, 1, 1, 3, 2, 6]
def baseStart_6838690 : Nat := 118140960795 + 6838690 * 2 ^ 59
def prefixEnd_6838690 : Nat := 4983230072969 + 3 ^ 40 * 6838690 * 2
def baseEnd_6838690 : Nat := 1170511672365317942541481

theorem tailTrace_6838690 : CollatzResearch.WordTrace tailWord_6838690 prefixEnd_6838690 1170511672365317942541481 := by
  unfold tailWord_6838690
  simp only [CollatzResearch.WordTrace]
  refine ⟨62356878898650390027860381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166285010396401040074294349 62356878898650390027860381)
  ·
    refine ⟨23383829586993896260447643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62356878898650390027860381 23383829586993896260447643)
    ·
      refine ⟨35075744380490844390671465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23383829586993896260447643 35075744380490844390671465)
      ·
        refine ⟨26306808285368133293003599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35075744380490844390671465 26306808285368133293003599)
        ·
          refine ⟨39460212428052199939505399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26306808285368133293003599 39460212428052199939505399)
          ·
            refine ⟨59190318642078299909258099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39460212428052199939505399 59190318642078299909258099)
            ·
              refine ⟨88785477963117449863887149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59190318642078299909258099 88785477963117449863887149)
              ·
                refine ⟨33294554236169043698957681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88785477963117449863887149 33294554236169043698957681)
                ·
                  refine ⟨24970915677126782774218261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33294554236169043698957681 24970915677126782774218261)
                  ·
                    refine ⟨1170511672365317942541481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24970915677126782774218261 1170511672365317942541481)
                    ·
                      rfl

theorem cell23_6838690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 3, 2, 6].length) (baseStart_6838690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6838690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6838690 prefixEnd_6838690 := by exact prefixLift 6838690
  have htrace : WordTrace (prefixWord ++ tailWord_6838690) baseStart_6838690 baseEnd_6838690 := by
    simpa [prefixWord, tailWord_6838690, baseEnd_6838690] using wordTrace_append hprefix tailTrace_6838690
  have hstable : (prefixWord ++ tailWord_6838690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6838690).length < 2 ^ (prefixWord ++ tailWord_6838690).sum := by decide
  have hdescent : baseEnd_6838690 < baseStart_6838690 := by decide
  rcases family_descends (prefixWord ++ tailWord_6838690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6838698 : List Nat := [3, 1, 6, 1, 2, 1, 2, 7]
def baseStart_6838698 : Nat := 118140960795 + 6838698 * 2 ^ 59
def prefixEnd_6838698 : Nat := 4983230072969 + 3 ^ 40 * 6838698 * 2
def baseEnd_6838698 : Nat := 130057004627451473937941

theorem tailTrace_6838698 : CollatzResearch.WordTrace tailWord_6838698 prefixEnd_6838698 130057004627451473937941 := by
  unfold tailWord_6838698
  simp only [CollatzResearch.WordTrace]
  refine ⟨62356951844643144369433187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166285204919048384985155165 62356951844643144369433187)
  ·
    refine ⟨93535427766964716554149781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62356951844643144369433187 93535427766964716554149781)
    ·
      refine ⟨4384473176576471088475771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 93535427766964716554149781 4384473176576471088475771)
      ·
        refine ⟨6576709764864706632713657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4384473176576471088475771 6576709764864706632713657)
        ·
          refine ⟨4932532323648529974535243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6576709764864706632713657 4932532323648529974535243)
          ·
            refine ⟨7398798485472794961802865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4932532323648529974535243 7398798485472794961802865)
            ·
              refine ⟨5549098864104596221352149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7398798485472794961802865 5549098864104596221352149)
              ·
                refine ⟨130057004627451473937941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5549098864104596221352149 130057004627451473937941)
                ·
                  rfl

theorem cell23_6838698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 2, 7].length) (baseStart_6838698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6838698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6838698 prefixEnd_6838698 := by exact prefixLift 6838698
  have htrace : WordTrace (prefixWord ++ tailWord_6838698) baseStart_6838698 baseEnd_6838698 := by
    simpa [prefixWord, tailWord_6838698, baseEnd_6838698] using wordTrace_append hprefix tailTrace_6838698
  have hstable : (prefixWord ++ tailWord_6838698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6838698).length < 2 ^ (prefixWord ++ tailWord_6838698).sum := by decide
  have hdescent : baseEnd_6838698 < baseStart_6838698 := by decide
  rcases family_descends (prefixWord ++ tailWord_6838698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6838787 : List Nat := [1, 1, 1, 3, 2, 1, 4, 2, 2, 4, 2]
def baseStart_6838787 : Nat := 118140960795 + 6838787 * 2 ^ 59
def prefixEnd_6838787 : Nat := 4983230072969 + 3 ^ 40 * 6838787 * 2
def baseEnd_6838787 : Nat := 3511584824719439948111497

theorem tailTrace_6838787 : CollatzResearch.WordTrace tailWord_6838787 prefixEnd_6838787 3511584824719439948111497 := by
  unfold tailWord_6838787
  simp only [CollatzResearch.WordTrace]
  refine ⟨249431053475250145677722615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166287368983500097118481743 249431053475250145677722615)
  ·
    refine ⟨374146580212875218516583923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249431053475250145677722615 374146580212875218516583923)
    ·
      refine ⟨561219870319312827774875885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374146580212875218516583923 561219870319312827774875885)
      ·
        refine ⟨210457451369742310415578457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 561219870319312827774875885 210457451369742310415578457)
        ·
          refine ⟨157843088527306732811683843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210457451369742310415578457 157843088527306732811683843)
          ·
            refine ⟨236764632790960099217525765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157843088527306732811683843 236764632790960099217525765)
            ·
              refine ⟨44393368648305018603286081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 236764632790960099217525765 44393368648305018603286081)
              ·
                refine ⟨33295026486228763952464561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44393368648305018603286081 33295026486228763952464561)
                ·
                  refine ⟨24971269864671572964348421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33295026486228763952464561 24971269864671572964348421)
                  ·
                    refine ⟨4682113099625919930815329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24971269864671572964348421 4682113099625919930815329)
                    ·
                      refine ⟨3511584824719439948111497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4682113099625919930815329 3511584824719439948111497)
                      ·
                        rfl

theorem cell23_6838787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 2, 2, 4, 2].length) (baseStart_6838787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6838787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6838787 prefixEnd_6838787 := by exact prefixLift 6838787
  have htrace : WordTrace (prefixWord ++ tailWord_6838787) baseStart_6838787 baseEnd_6838787 := by
    simpa [prefixWord, tailWord_6838787, baseEnd_6838787] using wordTrace_append hprefix tailTrace_6838787
  have hstable : (prefixWord ++ tailWord_6838787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6838787).length < 2 ^ (prefixWord ++ tailWord_6838787).sum := by decide
  have hdescent : baseEnd_6838787 < baseStart_6838787 := by decide
  rcases family_descends (prefixWord ++ tailWord_6838787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6838824 : List Nat := [2, 1, 5, 2, 1, 2, 1, 1, 1, 4, 3]
def baseStart_6838824 : Nat := 118140960795 + 6838824 * 2 ^ 59
def prefixEnd_6838824 : Nat := 4983230072969 + 3 ^ 40 * 6838824 * 2
def baseEnd_6838824 : Nat := 3511603823503656303348827

theorem tailTrace_6838824 : CollatzResearch.WordTrace tailWord_6838824 prefixEnd_6838824 3511603823503656303348827 := by
  unfold tailWord_6838824
  simp only [CollatzResearch.WordTrace]
  refine ⟨124716201488058050498409763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166288268650744067331213017 124716201488058050498409763)
  ·
    refine ⟨187074302232087075747614645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124716201488058050498409763 187074302232087075747614645)
    ·
      refine ⟨17538215834258163351338873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 187074302232087075747614645 17538215834258163351338873)
      ·
        refine ⟨13153661875693622513504155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17538215834258163351338873 13153661875693622513504155)
        ·
          refine ⟨19730492813540433770256233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13153661875693622513504155 19730492813540433770256233)
          ·
            refine ⟨14797869610155325327692175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19730492813540433770256233 14797869610155325327692175)
            ·
              refine ⟨22196804415232987991538263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14797869610155325327692175 22196804415232987991538263)
              ·
                refine ⟨33295206622849481987307395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22196804415232987991538263 33295206622849481987307395)
                ·
                  refine ⟨49942809934274222980961093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33295206622849481987307395 49942809934274222980961093)
                  ·
                    refine ⟨9364276862676416808930205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49942809934274222980961093 9364276862676416808930205)
                    ·
                      refine ⟨3511603823503656303348827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9364276862676416808930205 3511603823503656303348827)
                      ·
                        rfl

theorem cell23_6838824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_6838824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6838824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6838824 prefixEnd_6838824 := by exact prefixLift 6838824
  have htrace : WordTrace (prefixWord ++ tailWord_6838824) baseStart_6838824 baseEnd_6838824 := by
    simpa [prefixWord, tailWord_6838824, baseEnd_6838824] using wordTrace_append hprefix tailTrace_6838824
  have hstable : (prefixWord ++ tailWord_6838824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6838824).length < 2 ^ (prefixWord ++ tailWord_6838824).sum := by decide
  have hdescent : baseEnd_6838824 < baseStart_6838824 := by decide
  rcases family_descends (prefixWord ++ tailWord_6838824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6838844 : List Nat := [2, 2, 2, 2, 3, 3, 1, 2, 6]
def baseStart_6838844 : Nat := 118140960795 + 6838844 * 2 ^ 59
def prefixEnd_6838844 : Nat := 4983230072969 + 3 ^ 40 * 6838844 * 2
def baseEnd_6838844 : Nat := 390179343679638469455415

theorem tailTrace_6838844 : CollatzResearch.WordTrace tailWord_6838844 prefixEnd_6838844 390179343679638469455415 := by
  unfold tailWord_6838844
  simp only [CollatzResearch.WordTrace]
  refine ⟨124716566218021822206273793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166288754957362429608365057 124716566218021822206273793)
  ·
    refine ⟨93537424663516366654705345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124716566218021822206273793 93537424663516366654705345)
    ·
      refine ⟨70153068497637274991029009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93537424663516366654705345 70153068497637274991029009)
      ·
        refine ⟨52614801373227956243271757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70153068497637274991029009 52614801373227956243271757)
        ·
          refine ⟨19730550514960483591226909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52614801373227956243271757 19730550514960483591226909)
          ·
            refine ⟨7398956443110181346710091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19730550514960483591226909 7398956443110181346710091)
            ·
              refine ⟨11098434664665272020065137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7398956443110181346710091 11098434664665272020065137)
              ·
                refine ⟨8323825998498954015048853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11098434664665272020065137 8323825998498954015048853)
                ·
                  refine ⟨390179343679638469455415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8323825998498954015048853 390179343679638469455415)
                  ·
                    rfl

theorem cell23_6838844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 2, 6].length) (baseStart_6838844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6838844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6838844 prefixEnd_6838844 := by exact prefixLift 6838844
  have htrace : WordTrace (prefixWord ++ tailWord_6838844) baseStart_6838844 baseEnd_6838844 := by
    simpa [prefixWord, tailWord_6838844, baseEnd_6838844] using wordTrace_append hprefix tailTrace_6838844
  have hstable : (prefixWord ++ tailWord_6838844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6838844).length < 2 ^ (prefixWord ++ tailWord_6838844).sum := by decide
  have hdescent : baseEnd_6838844 < baseStart_6838844 := by decide
  rcases family_descends (prefixWord ++ tailWord_6838844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6838861 : List Nat := [1, 6, 1, 1, 2, 2, 3, 1, 6]
def baseStart_6838861 : Nat := 118140960795 + 6838861 * 2 ^ 59
def prefixEnd_6838861 : Nat := 4983230072969 + 3 ^ 40 * 6838861 * 2
def baseEnd_6838861 : Nat := 390180313587541406509573

theorem tailTrace_6838861 : CollatzResearch.WordTrace tailWord_6838861 prefixEnd_6838861 390180313587541406509573 := by
  unfold tailWord_6838861
  simp only [CollatzResearch.WordTrace]
  refine ⟨249433752476982056315916437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166289168317988037543944291 249433752476982056315916437)
  ·
    refine ⟨11692207147358533889808583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 249433752476982056315916437 11692207147358533889808583)
    ·
      refine ⟨17538310721037800834712875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11692207147358533889808583 17538310721037800834712875)
      ·
        refine ⟨26307466081556701252069313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17538310721037800834712875 26307466081556701252069313)
        ·
          refine ⟨19730599561167525939051985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26307466081556701252069313 19730599561167525939051985)
          ·
            refine ⟨14797949670875644454288989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19730599561167525939051985 14797949670875644454288989)
            ·
              refine ⟨5549231126578366670358371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14797949670875644454288989 5549231126578366670358371)
              ·
                refine ⟨8323846689867550005537557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5549231126578366670358371 8323846689867550005537557)
                ·
                  refine ⟨390180313587541406509573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8323846689867550005537557 390180313587541406509573)
                  ·
                    rfl

theorem cell23_6838861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 3, 1, 6].length) (baseStart_6838861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6838861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6838861 prefixEnd_6838861 := by exact prefixLift 6838861
  have htrace : WordTrace (prefixWord ++ tailWord_6838861) baseStart_6838861 baseEnd_6838861 := by
    simpa [prefixWord, tailWord_6838861, baseEnd_6838861] using wordTrace_append hprefix tailTrace_6838861
  have hstable : (prefixWord ++ tailWord_6838861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6838861).length < 2 ^ (prefixWord ++ tailWord_6838861).sum := by decide
  have hdescent : baseEnd_6838861 < baseStart_6838861 := by decide
  rcases family_descends (prefixWord ++ tailWord_6838861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6838882 : List Nat := [3, 3, 2, 3, 2, 1, 1, 3, 1, 4]
def baseStart_6838882 : Nat := 118140960795 + 6838882 * 2 ^ 59
def prefixEnd_6838882 : Nat := 4983230072969 + 3 ^ 40 * 6838882 * 2
def baseEnd_6838882 : Nat := 1170544535127205692141187

theorem tailTrace_6838882 : CollatzResearch.WordTrace tailWord_6838882 prefixEnd_6838882 1170544535127205692141187 := by
  unfold tailWord_6838882
  simp only [CollatzResearch.WordTrace]
  refine ⟨62358629602476494225607725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166289678939937317934953933 62358629602476494225607725)
  ·
    refine ⟨23384486100928685334602897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62358629602476494225607725 23384486100928685334602897)
    ·
      refine ⟨17538364575696514000952173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23384486100928685334602897 17538364575696514000952173)
      ·
        refine ⟨6576886715886192750357065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17538364575696514000952173 6576886715886192750357065)
        ·
          refine ⟨4932665036914644562767799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6576886715886192750357065 4932665036914644562767799)
          ·
            refine ⟨7398997555371966844151699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4932665036914644562767799 7398997555371966844151699)
            ·
              refine ⟨11098496333057950266227549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7398997555371966844151699 11098496333057950266227549)
              ·
                refine ⟨4161936124896731349835331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11098496333057950266227549 4161936124896731349835331)
                ·
                  refine ⟨6242904187345097024752997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4161936124896731349835331 6242904187345097024752997)
                  ·
                    refine ⟨1170544535127205692141187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6242904187345097024752997 1170544535127205692141187)
                    ·
                      rfl

theorem cell23_6838882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_6838882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6838882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6838882 prefixEnd_6838882 := by exact prefixLift 6838882
  have htrace : WordTrace (prefixWord ++ tailWord_6838882) baseStart_6838882 baseEnd_6838882 := by
    simpa [prefixWord, tailWord_6838882, baseEnd_6838882] using wordTrace_append hprefix tailTrace_6838882
  have hstable : (prefixWord ++ tailWord_6838882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6838882).length < 2 ^ (prefixWord ++ tailWord_6838882).sum := by decide
  have hdescent : baseEnd_6838882 < baseStart_6838882 := by decide
  rcases family_descends (prefixWord ++ tailWord_6838882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6838897 : List Nat := [1, 2, 2, 2, 1, 1, 1, 1, 7, 2, 3]
def baseStart_6838897 : Nat := 118140960795 + 6838897 * 2 ^ 59
def prefixEnd_6838897 : Nat := 4983230072969 + 3 ^ 40 * 6838897 * 2
def baseEnd_6838897 : Nat := 3511641307591434517735991

theorem tailTrace_6838897 : CollatzResearch.WordTrace tailWord_6838897 prefixEnd_6838897 3511641307591434517735991 := by
  unfold tailWord_6838897
  simp only [CollatzResearch.WordTrace]
  refine ⟨249435065504851634464226945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166290043669901089642817963 249435065504851634464226945)
  ·
    refine ⟨187076299128638725848170209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249435065504851634464226945 187076299128638725848170209)
    ·
      refine ⟨140307224346479044386127657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187076299128638725848170209 140307224346479044386127657)
      ·
        refine ⟨105230418259859283289595743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140307224346479044386127657 105230418259859283289595743)
        ·
          refine ⟨157845627389788924934393615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105230418259859283289595743 157845627389788924934393615)
          ·
            refine ⟨236768441084683387401590423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157845627389788924934393615 236768441084683387401590423)
            ·
              refine ⟨355152661627025081102385635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 236768441084683387401590423 355152661627025081102385635)
              ·
                refine ⟨532728992440537621653578453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 355152661627025081102385635 532728992440537621653578453)
                ·
                  refine ⟨12485835760325100507505745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 532728992440537621653578453 12485835760325100507505745)
                  ·
                    refine ⟨9364376820243825380629309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12485835760325100507505745 9364376820243825380629309)
                    ·
                      refine ⟨3511641307591434517735991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9364376820243825380629309 3511641307591434517735991)
                      ·
                        rfl

theorem cell23_6838897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 7, 2, 3].length) (baseStart_6838897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6838897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6838897 prefixEnd_6838897 := by exact prefixLift 6838897
  have htrace : WordTrace (prefixWord ++ tailWord_6838897) baseStart_6838897 baseEnd_6838897 := by
    simpa [prefixWord, tailWord_6838897, baseEnd_6838897] using wordTrace_append hprefix tailTrace_6838897
  have hstable : (prefixWord ++ tailWord_6838897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6838897).length < 2 ^ (prefixWord ++ tailWord_6838897).sum := by decide
  have hdescent : baseEnd_6838897 < baseStart_6838897 := by decide
  rcases family_descends (prefixWord ++ tailWord_6838897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6838917 : List Nat := [1, 3, 1, 1, 4, 3, 2, 8]
def baseStart_6838917 : Nat := 118140960795 + 6838917 * 2 ^ 59
def prefixEnd_6838917 : Nat := 4983230072969 + 3 ^ 40 * 6838917 * 2
def baseEnd_6838917 : Nat := 130061169526093497758737

theorem tailTrace_6838917 : CollatzResearch.WordTrace tailWord_6838917 prefixEnd_6838917 130061169526093497758737 := by
  unfold tailWord_6838917
  simp only [CollatzResearch.WordTrace]
  refine ⟨249435794964779177879955005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166290529976519451919970003 249435794964779177879955005)
  ·
    refine ⟨93538423111792191704983127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249435794964779177879955005 93538423111792191704983127)
    ·
      refine ⟨140307634667688287557474691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93538423111792191704983127 140307634667688287557474691)
      ·
        refine ⟨210461452001532431336212037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140307634667688287557474691 210461452001532431336212037)
        ·
          refine ⟨39461522250287330875539757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 210461452001532431336212037 39461522250287330875539757)
          ·
            refine ⟨14798070843857749078327409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39461522250287330875539757 14798070843857749078327409)
            ·
              refine ⟨11098553132893311808745557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14798070843857749078327409 11098553132893311808745557)
              ·
                refine ⟨130061169526093497758737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11098553132893311808745557 130061169526093497758737)
                ·
                  rfl

theorem cell23_6838917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 8].length) (baseStart_6838917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6838917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6838917 prefixEnd_6838917 := by exact prefixLift 6838917
  have htrace : WordTrace (prefixWord ++ tailWord_6838917) baseStart_6838917 baseEnd_6838917 := by
    simpa [prefixWord, tailWord_6838917, baseEnd_6838917] using wordTrace_append hprefix tailTrace_6838917
  have hstable : (prefixWord ++ tailWord_6838917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6838917).length < 2 ^ (prefixWord ++ tailWord_6838917).sum := by decide
  have hdescent : baseEnd_6838917 < baseStart_6838917 := by decide
  rcases family_descends (prefixWord ++ tailWord_6838917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6839001 : List Nat := [1, 2, 1, 2, 3, 2, 2, 2, 4, 2, 2]
def baseStart_6839001 : Nat := 118140960795 + 6839001 * 2 ^ 59
def prefixEnd_6839001 : Nat := 4983230072969 + 3 ^ 40 * 6839001 * 2
def baseEnd_6839001 : Nat := 3511694709579502110835513

theorem tailTrace_6839001 : CollatzResearch.WordTrace tailWord_6839001 prefixEnd_6839001 3511694709579502110835513 := by
  unfold tailWord_6839001
  simp only [CollatzResearch.WordTrace]
  refine ⟨249438858696474860226012857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166292572464316573484008571 249438858696474860226012857)
  ·
    refine ⟨187079144022356145169509643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249438858696474860226012857 187079144022356145169509643)
    ·
      refine ⟨280618716033534217754264465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187079144022356145169509643 280618716033534217754264465)
      ·
        refine ⟨210464037025150663315698349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280618716033534217754264465 210464037025150663315698349)
        ·
          refine ⟨78924013884431498743386881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 210464037025150663315698349 78924013884431498743386881)
          ·
            refine ⟨59193010413323624057540161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78924013884431498743386881 59193010413323624057540161)
            ·
              refine ⟨44394757809992718043155121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59193010413323624057540161 44394757809992718043155121)
              ·
                refine ⟨33296068357494538532366341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44394757809992718043155121 33296068357494538532366341)
                ·
                  refine ⟨6243012817030225974818689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33296068357494538532366341 6243012817030225974818689)
                  ·
                    refine ⟨4682259612772669481114017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6243012817030225974818689 4682259612772669481114017)
                    ·
                      refine ⟨3511694709579502110835513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4682259612772669481114017 3511694709579502110835513)
                      ·
                        rfl

theorem cell23_6839001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 2, 4, 2, 2].length) (baseStart_6839001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6839001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6839001 prefixEnd_6839001 := by exact prefixLift 6839001
  have htrace : WordTrace (prefixWord ++ tailWord_6839001) baseStart_6839001 baseEnd_6839001 := by
    simpa [prefixWord, tailWord_6839001, baseEnd_6839001] using wordTrace_append hprefix tailTrace_6839001
  have hstable : (prefixWord ++ tailWord_6839001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6839001).length < 2 ^ (prefixWord ++ tailWord_6839001).sum := by decide
  have hdescent : baseEnd_6839001 < baseStart_6839001 := by decide
  rcases family_descends (prefixWord ++ tailWord_6839001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6839024 : List Nat := [2, 1, 1, 1, 3, 1, 3, 6, 5]
def baseStart_6839024 : Nat := 118140960795 + 6839024 * 2 ^ 59
def prefixEnd_6839024 : Nat := 4983230072969 + 3 ^ 40 * 6839024 * 2
def baseEnd_6839024 : Nat := 390189613292728391205323

theorem tailTrace_6839024 : CollatzResearch.WordTrace tailWord_6839024 prefixEnd_6839024 390189613292728391205323 := by
  unfold tailWord_6839024
  simp only [CollatzResearch.WordTrace]
  refine ⟨124719848787695767577050063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166293131716927690102733417 124719848787695767577050063)
  ·
    refine ⟨187079773181543651365575095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124719848787695767577050063 187079773181543651365575095)
    ·
      refine ⟨280619659772315477048362643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187079773181543651365575095 280619659772315477048362643)
      ·
        refine ⟨420929489658473215572543965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280619659772315477048362643 420929489658473215572543965)
        ·
          refine ⟨157848558621927455839703987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 420929489658473215572543965 157848558621927455839703987)
          ·
            refine ⟨236772837932891183759555981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157848558621927455839703987 236772837932891183759555981)
            ·
              refine ⟨88789814224834193909833493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 236772837932891183759555981 88789814224834193909833493)
              ·
                refine ⟨4162022541789102839523445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 88789814224834193909833493 4162022541789102839523445)
                ·
                  refine ⟨390189613292728391205323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4162022541789102839523445 390189613292728391205323)
                  ·
                    rfl

theorem cell23_6839024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 6, 5].length) (baseStart_6839024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6839024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6839024 prefixEnd_6839024 := by exact prefixLift 6839024
  have htrace : WordTrace (prefixWord ++ tailWord_6839024) baseStart_6839024 baseEnd_6839024 := by
    simpa [prefixWord, tailWord_6839024, baseEnd_6839024] using wordTrace_append hprefix tailTrace_6839024
  have hstable : (prefixWord ++ tailWord_6839024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6839024).length < 2 ^ (prefixWord ++ tailWord_6839024).sum := by decide
  have hdescent : baseEnd_6839024 < baseStart_6839024 := by decide
  rcases family_descends (prefixWord ++ tailWord_6839024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6839029 : List Nat := [1, 3, 6, 1, 1, 1, 3, 1, 2, 1, 3]
def baseStart_6839029 : Nat := 118140960795 + 6839029 * 2 ^ 59
def prefixEnd_6839029 : Nat := 4983230072969 + 3 ^ 40 * 6839029 * 2
def baseEnd_6839029 : Nat := 3511709087037828001285385

theorem tailTrace_6839029 : CollatzResearch.WordTrace tailWord_6839029 prefixEnd_6839029 3511709087037828001285385 := by
  unfold tailWord_6839029
  simp only [CollatzResearch.WordTrace]
  refine ⟨249439879940373421008032141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166293253293582280672021427 249439879940373421008032141)
  ·
    refine ⟨93539954977640032878012053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249439879940373421008032141 93539954977640032878012053)
    ·
      refine ⟨4384685389576876541156815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 93539954977640032878012053 4384685389576876541156815)
      ·
        refine ⟨6577028084365314811735223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4384685389576876541156815 6577028084365314811735223)
        ·
          refine ⟨9865542126547972217602835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6577028084365314811735223 9865542126547972217602835)
          ·
            refine ⟨14798313189821958326404253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9865542126547972217602835 14798313189821958326404253)
            ·
              refine ⟨5549367446183234372401595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14798313189821958326404253 5549367446183234372401595)
              ·
                refine ⟨8324051169274851558602393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5549367446183234372401595 8324051169274851558602393)
                ·
                  refine ⟨6243038376956138668951795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8324051169274851558602393 6243038376956138668951795)
                  ·
                    refine ⟨9364557565434208003427693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6243038376956138668951795 9364557565434208003427693)
                    ·
                      refine ⟨3511709087037828001285385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9364557565434208003427693 3511709087037828001285385)
                      ·
                        rfl

theorem cell23_6839029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_6839029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6839029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6839029 prefixEnd_6839029 := by exact prefixLift 6839029
  have htrace : WordTrace (prefixWord ++ tailWord_6839029) baseStart_6839029 baseEnd_6839029 := by
    simpa [prefixWord, tailWord_6839029, baseEnd_6839029] using wordTrace_append hprefix tailTrace_6839029
  have hstable : (prefixWord ++ tailWord_6839029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6839029).length < 2 ^ (prefixWord ++ tailWord_6839029).sum := by decide
  have hdescent : baseEnd_6839029 < baseStart_6839029 := by decide
  rcases family_descends (prefixWord ++ tailWord_6839029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6839034 : List Nat := [3, 1, 1, 1, 1, 3, 4, 1, 2, 3, 3]
def baseStart_6839034 : Nat := 118140960795 + 6839034 * 2 ^ 59
def prefixEnd_6839034 : Nat := 4983230072969 + 3 ^ 40 * 6839034 * 2
def baseEnd_6839034 : Nat := 3511711654441100481722861

theorem tailTrace_6839034 : CollatzResearch.WordTrace tailWord_6839034 prefixEnd_6839034 3511711654441100481722861 := by
  unfold tailWord_6839034
  simp only [CollatzResearch.WordTrace]
  refine ⟨62360015576338826715491039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166293374870236871241309437 62360015576338826715491039)
  ·
    refine ⟨93540023364508240073236559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62360015576338826715491039 93540023364508240073236559)
    ·
      refine ⟨140310035046762360109854839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93540023364508240073236559 140310035046762360109854839)
      ·
        refine ⟨210465052570143540164782259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140310035046762360109854839 210465052570143540164782259)
        ·
          refine ⟨315697578855215310247173389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210465052570143540164782259 315697578855215310247173389)
          ·
            refine ⟨118386592070705741342690021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 315697578855215310247173389 118386592070705741342690021)
            ·
              refine ⟨22197486013257326501754379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 118386592070705741342690021 22197486013257326501754379)
              ·
                refine ⟨33296229019885989752631569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22197486013257326501754379 33296229019885989752631569)
                ·
                  refine ⟨24972171764914492314473677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33296229019885989752631569 24972171764914492314473677)
                  ·
                    refine ⟨9364564411842934617927629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24972171764914492314473677 9364564411842934617927629)
                    ·
                      refine ⟨3511711654441100481722861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9364564411842934617927629 3511711654441100481722861)
                      ·
                        rfl

theorem cell23_6839034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 1, 2, 3, 3].length) (baseStart_6839034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6839034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6839034 prefixEnd_6839034 := by exact prefixLift 6839034
  have htrace : WordTrace (prefixWord ++ tailWord_6839034) baseStart_6839034 baseEnd_6839034 := by
    simpa [prefixWord, tailWord_6839034, baseEnd_6839034] using wordTrace_append hprefix tailTrace_6839034
  have hstable : (prefixWord ++ tailWord_6839034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6839034).length < 2 ^ (prefixWord ++ tailWord_6839034).sum := by decide
  have hdescent : baseEnd_6839034 < baseStart_6839034 := by decide
  rcases family_descends (prefixWord ++ tailWord_6839034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6839037 : List Nat := [1, 4, 1, 1, 1, 1, 3, 1, 3, 7]
def baseStart_6839037 : Nat := 118140960795 + 6839037 * 2 ^ 59
def prefixEnd_6839037 : Nat := 4983230072969 + 3 ^ 40 * 6839037 * 2
def baseEnd_6839037 : Nat := 1170571064961021323328449

theorem tailTrace_6839037 : CollatzResearch.WordTrace tailWord_6839037 prefixEnd_6839037 1170571064961021323328449 := by
  unfold tailWord_6839037
  simp only [CollatzResearch.WordTrace]
  refine ⟨249440171724344438374323365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166293447816229625582882243 249440171724344438374323365)
  ·
    refine ⟨46770032198314582195185631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 249440171724344438374323365 46770032198314582195185631)
    ·
      refine ⟨70155048297471873292778447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46770032198314582195185631 70155048297471873292778447)
      ·
        refine ⟨105232572446207809939167671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70155048297471873292778447 105232572446207809939167671)
        ·
          refine ⟨157848858669311714908751507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105232572446207809939167671 157848858669311714908751507)
          ·
            refine ⟨236773288003967572363127261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157848858669311714908751507 236773288003967572363127261)
            ·
              refine ⟨88789983001487839636172723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 236773288003967572363127261 88789983001487839636172723)
              ·
                refine ⟨133184974502231759454259085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88789983001487839636172723 133184974502231759454259085)
                ·
                  refine ⟨49944365438336909795347157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 133184974502231759454259085 49944365438336909795347157)
                  ·
                    refine ⟨1170571064961021323328449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49944365438336909795347157 1170571064961021323328449)
                    ·
                      rfl

theorem cell23_6839037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 3, 7].length) (baseStart_6839037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6839037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6839037 prefixEnd_6839037 := by exact prefixLift 6839037
  have htrace : WordTrace (prefixWord ++ tailWord_6839037) baseStart_6839037 baseEnd_6839037 := by
    simpa [prefixWord, tailWord_6839037, baseEnd_6839037] using wordTrace_append hprefix tailTrace_6839037
  have hstable : (prefixWord ++ tailWord_6839037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6839037).length < 2 ^ (prefixWord ++ tailWord_6839037).sum := by decide
  have hdescent : baseEnd_6839037 < baseStart_6839037 := by decide
  rcases family_descends (prefixWord ++ tailWord_6839037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6839054 : List Nat := [4, 1, 1, 2, 1, 1, 1, 5, 2, 5]
def baseStart_6839054 : Nat := 118140960795 + 6839054 * 2 ^ 59
def prefixEnd_6839054 : Nat := 4983230072969 + 3 ^ 40 * 6839054 * 2
def baseEnd_6839054 : Nat := 1170573974684730134490923

theorem tailTrace_6839054 : CollatzResearch.WordTrace tailWord_6839054 prefixEnd_6839054 1170573974684730134490923 := by
  unfold tailWord_6839054
  simp only [CollatzResearch.WordTrace]
  refine ⟨31180098970660356284711527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166293861176855233518461477 31180098970660356284711527)
  ·
    refine ⟨46770148455990534427067291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31180098970660356284711527 46770148455990534427067291)
    ·
      refine ⟨70155222683985801640600937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46770148455990534427067291 70155222683985801640600937)
      ·
        refine ⟨52616417012989351230450703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70155222683985801640600937 52616417012989351230450703)
        ·
          refine ⟨78924625519484026845676055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52616417012989351230450703 78924625519484026845676055)
          ·
            refine ⟨118386938279226040268514083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78924625519484026845676055 118386938279226040268514083)
            ·
              refine ⟨177580407418839060402771125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118386938279226040268514083 177580407418839060402771125)
              ·
                refine ⟨16648163195516161912759793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 177580407418839060402771125 16648163195516161912759793)
                ·
                  refine ⟨12486122396637121434569845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16648163195516161912759793 12486122396637121434569845)
                  ·
                    refine ⟨1170573974684730134490923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12486122396637121434569845 1170573974684730134490923)
                    ·
                      rfl

theorem cell23_6839054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 5, 2, 5].length) (baseStart_6839054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6839054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6839054 prefixEnd_6839054 := by exact prefixLift 6839054
  have htrace : WordTrace (prefixWord ++ tailWord_6839054) baseStart_6839054 baseEnd_6839054 := by
    simpa [prefixWord, tailWord_6839054, baseEnd_6839054] using wordTrace_append hprefix tailTrace_6839054
  have hstable : (prefixWord ++ tailWord_6839054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6839054).length < 2 ^ (prefixWord ++ tailWord_6839054).sum := by decide
  have hdescent : baseEnd_6839054 < baseStart_6839054 := by decide
  rcases family_descends (prefixWord ++ tailWord_6839054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6839151 : List Nat := [1, 1, 2, 1, 3, 1, 1, 4, 4, 3, 2]
def baseStart_6839151 : Nat := 118140960795 + 6839151 * 2 ^ 59
def prefixEnd_6839151 : Nat := 4983230072969 + 3 ^ 40 * 6839151 * 2
def baseEnd_6839151 : Nat := 3511771731677676523959823

theorem tailTrace_6839151 : CollatzResearch.WordTrace tailWord_6839151 prefixEnd_6839151 3511771731677676523959823 := by
  unfold tailWord_6839151
  simp only [CollatzResearch.WordTrace]
  refine ⟨249444329645931435843973307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166296219763954290562648871 249444329645931435843973307)
  ·
    refine ⟨374166494468897153765959961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249444329645931435843973307 374166494468897153765959961)
    ·
      refine ⟨280624870851672865324469971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 374166494468897153765959961 280624870851672865324469971)
      ·
        refine ⟨420937306277509297986704957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280624870851672865324469971 420937306277509297986704957)
        ·
          refine ⟨157851489854065986745014359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 420937306277509297986704957 157851489854065986745014359)
          ·
            refine ⟨236777234781098980117521539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157851489854065986745014359 236777234781098980117521539)
            ·
              refine ⟨355165852171648470176282309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 236777234781098980117521539 355165852171648470176282309)
              ·
                refine ⟨66593597282184088158052933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 355165852171648470176282309 66593597282184088158052933)
                ·
                  refine ⟨12486299490409516529634925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66593597282184088158052933 12486299490409516529634925)
                  ·
                    refine ⟨4682362308903568698613097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12486299490409516529634925 4682362308903568698613097)
                    ·
                      refine ⟨3511771731677676523959823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4682362308903568698613097 3511771731677676523959823)
                      ·
                        rfl

theorem cell23_6839151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 4, 3, 2].length) (baseStart_6839151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6839151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6839151 prefixEnd_6839151 := by exact prefixLift 6839151
  have htrace : WordTrace (prefixWord ++ tailWord_6839151) baseStart_6839151 baseEnd_6839151 := by
    simpa [prefixWord, tailWord_6839151, baseEnd_6839151] using wordTrace_append hprefix tailTrace_6839151
  have hstable : (prefixWord ++ tailWord_6839151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6839151).length < 2 ^ (prefixWord ++ tailWord_6839151).sum := by decide
  have hdescent : baseEnd_6839151 < baseStart_6839151 := by decide
  rcases family_descends (prefixWord ++ tailWord_6839151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6839175 : List Nat := [1, 1, 4, 2, 3, 1, 1, 5, 1, 1, 3]
def baseStart_6839175 : Nat := 118140960795 + 6839175 * 2 ^ 59
def prefixEnd_6839175 : Nat := 4983230072969 + 3 ^ 40 * 6839175 * 2
def baseEnd_6839175 : Nat := 3511784055213384430059713

theorem tailTrace_6839175 : CollatzResearch.WordTrace tailWord_6839175 prefixEnd_6839175 3511784055213384430059713 := by
  unfold tailWord_6839175
  simp only [CollatzResearch.WordTrace]
  refine ⟨249445204997844487942846979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166296803331896325295231319 249445204997844487942846979)
  ·
    refine ⟨374167807496766731914270469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249445204997844487942846979 374167807496766731914270469)
    ·
      refine ⟨70156463905643762233925713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 374167807496766731914270469 70156463905643762233925713)
      ·
        refine ⟨52617347929232821675444285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70156463905643762233925713 52617347929232821675444285)
        ·
          refine ⟨19731505473462308128291607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52617347929232821675444285 19731505473462308128291607)
          ·
            refine ⟨29597258210193462192437411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19731505473462308128291607 29597258210193462192437411)
            ·
              refine ⟨44395887315290193288656117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29597258210193462192437411 44395887315290193288656117)
              ·
                refine ⟨4162114435808455620811511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44395887315290193288656117 4162114435808455620811511)
                ·
                  refine ⟨6243171653712683431217267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4162114435808455620811511 6243171653712683431217267)
                  ·
                    refine ⟨9364757480569025146825901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6243171653712683431217267 9364757480569025146825901)
                    ·
                      refine ⟨3511784055213384430059713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9364757480569025146825901 3511784055213384430059713)
                      ·
                        rfl

theorem cell23_6839175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 5, 1, 1, 3].length) (baseStart_6839175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6839175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6839175 prefixEnd_6839175 := by exact prefixLift 6839175
  have htrace : WordTrace (prefixWord ++ tailWord_6839175) baseStart_6839175 baseEnd_6839175 := by
    simpa [prefixWord, tailWord_6839175, baseEnd_6839175] using wordTrace_append hprefix tailTrace_6839175
  have hstable : (prefixWord ++ tailWord_6839175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6839175).length < 2 ^ (prefixWord ++ tailWord_6839175).sum := by decide
  have hdescent : baseEnd_6839175 < baseStart_6839175 := by decide
  rcases family_descends (prefixWord ++ tailWord_6839175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6839178 : List Nat := [3, 1, 2, 4, 1, 2, 1, 3, 1, 5]
def baseStart_6839178 : Nat := 118140960795 + 6839178 * 2 ^ 59
def prefixEnd_6839178 : Nat := 4983230072969 + 3 ^ 40 * 6839178 * 2
def baseEnd_6839178 : Nat := 1170595198551782639440733

theorem tailTrace_6839178 : CollatzResearch.WordTrace tailWord_6839178 prefixEnd_6839178 1170595198551782639440733 := by
  unfold tailWord_6839178
  simp only [CollatzResearch.WordTrace]
  refine ⟨62361328604208404863801547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166296876277889079636804125 62361328604208404863801547)
  ·
    refine ⟨93541992906312607295702321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62361328604208404863801547 93541992906312607295702321)
    ·
      refine ⟨70156494679734455471776741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93541992906312607295702321 70156494679734455471776741)
      ·
        refine ⟨13154342752450210400958139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70156494679734455471776741 13154342752450210400958139)
        ·
          refine ⟨19731514128675315601437209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13154342752450210400958139 19731514128675315601437209)
          ·
            refine ⟨14798635596506486701077907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19731514128675315601437209 14798635596506486701077907)
            ·
              refine ⟨22197953394759730051616861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14798635596506486701077907 22197953394759730051616861)
              ·
                refine ⟨8324232523034898769356323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22197953394759730051616861 8324232523034898769356323)
                ·
                  refine ⟨12486348784552348154034485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8324232523034898769356323 12486348784552348154034485)
                  ·
                    refine ⟨1170595198551782639440733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12486348784552348154034485 1170595198551782639440733)
                    ·
                      rfl

theorem cell23_6839178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 3, 1, 5].length) (baseStart_6839178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6839178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6839178 prefixEnd_6839178 := by exact prefixLift 6839178
  have htrace : WordTrace (prefixWord ++ tailWord_6839178) baseStart_6839178 baseEnd_6839178 := by
    simpa [prefixWord, tailWord_6839178, baseEnd_6839178] using wordTrace_append hprefix tailTrace_6839178
  have hstable : (prefixWord ++ tailWord_6839178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6839178).length < 2 ^ (prefixWord ++ tailWord_6839178).sum := by decide
  have hdescent : baseEnd_6839178 < baseStart_6839178 := by decide
  rcases family_descends (prefixWord ++ tailWord_6839178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6839184 : List Nat := [2, 1, 1, 1, 1, 1, 2, 2, 1, 8, 3]
def baseStart_6839184 : Nat := 118140960795 + 6839184 * 2 ^ 59
def prefixEnd_6839184 : Nat := 4983230072969 + 3 ^ 40 * 6839184 * 2
def baseEnd_6839184 : Nat := 3511788676539274894847171

theorem tailTrace_6839184 : CollatzResearch.WordTrace tailWord_6839184 prefixEnd_6839184 3511788676539274894847171 := by
  unfold tailWord_6839184
  simp only [CollatzResearch.WordTrace]
  refine ⟨124722766627405941239962303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166297022169874588319949737 124722766627405941239962303)
  ·
    refine ⟨187084149941108911859943455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124722766627405941239962303 187084149941108911859943455)
    ·
      refine ⟨280626224911663367789915183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187084149941108911859943455 280626224911663367789915183)
      ·
        refine ⟨420939337367495051684872775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280626224911663367789915183 420939337367495051684872775)
        ·
          refine ⟨631409006051242577527309163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 420939337367495051684872775 631409006051242577527309163)
          ·
            refine ⟨947113509076863866290963745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 631409006051242577527309163 947113509076863866290963745)
            ·
              refine ⟨710335131807647899718222809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 947113509076863866290963745 710335131807647899718222809)
              ·
                refine ⟨532751348855735924788667107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 710335131807647899718222809 532751348855735924788667107)
                ·
                  refine ⟨799127023283603887183000661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 532751348855735924788667107 799127023283603887183000661)
                  ·
                    refine ⟨9364769804104733052925789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 799127023283603887183000661 9364769804104733052925789)
                    ·
                      refine ⟨3511788676539274894847171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9364769804104733052925789 3511788676539274894847171)
                      ·
                        rfl

theorem cell23_6839184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 1, 8, 3].length) (baseStart_6839184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6839184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6839184 prefixEnd_6839184 := by exact prefixLift 6839184
  have htrace : WordTrace (prefixWord ++ tailWord_6839184) baseStart_6839184 baseEnd_6839184 := by
    simpa [prefixWord, tailWord_6839184, baseEnd_6839184] using wordTrace_append hprefix tailTrace_6839184
  have hstable : (prefixWord ++ tailWord_6839184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6839184).length < 2 ^ (prefixWord ++ tailWord_6839184).sum := by decide
  have hdescent : baseEnd_6839184 < baseStart_6839184 := by decide
  rcases family_descends (prefixWord ++ tailWord_6839184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6839191 : List Nat := [1, 1, 3, 3, 1, 2, 3, 1, 4, 4]
def baseStart_6839191 : Nat := 118140960795 + 6839191 * 2 ^ 59
def prefixEnd_6839191 : Nat := 4983230072969 + 3 ^ 40 * 6839191 * 2
def baseEnd_6839191 : Nat := 1170597423634618789153213

theorem tailTrace_6839191 : CollatzResearch.WordTrace tailWord_6839191 prefixEnd_6839191 1170597423634618789153213 := by
  unfold tailWord_6839191
  simp only [CollatzResearch.WordTrace]
  refine ⟨249445788565786522675429427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166297192377191015116952951 249445788565786522675429427)
  ·
    refine ⟨374168682848679784013144141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249445788565786522675429427 374168682848679784013144141)
    ·
      refine ⟨140313256068254919004929053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 374168682848679784013144141 140313256068254919004929053)
      ·
        refine ⟨52617471025595594626848395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140313256068254919004929053 52617471025595594626848395)
        ·
          refine ⟨78926206538393391940272593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52617471025595594626848395 78926206538393391940272593)
          ·
            refine ⟨59194654903795043955204445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78926206538393391940272593 59194654903795043955204445)
            ·
              refine ⟨22197995588923141483201667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59194654903795043955204445 22197995588923141483201667)
              ·
                refine ⟨33296993383384712224802501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22197995588923141483201667 33296993383384712224802501)
                ·
                  refine ⟨6243186259384633542150469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33296993383384712224802501 6243186259384633542150469)
                  ·
                    refine ⟨1170597423634618789153213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6243186259384633542150469 1170597423634618789153213)
                    ·
                      rfl

theorem cell23_6839191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 1, 4, 4].length) (baseStart_6839191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6839191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6839191 prefixEnd_6839191 := by exact prefixLift 6839191
  have htrace : WordTrace (prefixWord ++ tailWord_6839191) baseStart_6839191 baseEnd_6839191 := by
    simpa [prefixWord, tailWord_6839191, baseEnd_6839191] using wordTrace_append hprefix tailTrace_6839191
  have hstable : (prefixWord ++ tailWord_6839191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6839191).length < 2 ^ (prefixWord ++ tailWord_6839191).sum := by decide
  have hdescent : baseEnd_6839191 < baseStart_6839191 := by decide
  rcases family_descends (prefixWord ++ tailWord_6839191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6839201 : List Nat := [1, 2, 3, 4, 1, 1, 1, 1, 3, 1, 5]
def baseStart_6839201 : Nat := 118140960795 + 6839201 * 2 ^ 59
def prefixEnd_6839201 : Nat := 4983230072969 + 3 ^ 40 * 6839201 * 2
def baseEnd_6839201 : Nat := 3511797405710401328334593

theorem tailTrace_6839201 : CollatzResearch.WordTrace tailWord_6839201 prefixEnd_6839201 3511797405710401328334593 := by
  unfold tailWord_6839201
  simp only [CollatzResearch.WordTrace]
  refine ⟨249446153295750294383293457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166297435530500196255528971 249446153295750294383293457)
  ·
    refine ⟨187084614971812720787470093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249446153295750294383293457 187084614971812720787470093)
    ·
      refine ⟨70156730614429770295301285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187084614971812720787470093 70156730614429770295301285)
      ·
        refine ⟨13154386990205581930368991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70156730614429770295301285 13154386990205581930368991)
        ·
          refine ⟨19731580485308372895553487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13154386990205581930368991 19731580485308372895553487)
          ·
            refine ⟨29597370727962559343330231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19731580485308372895553487 29597370727962559343330231)
            ·
              refine ⟨44396056091943839014995347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29597370727962559343330231 44396056091943839014995347)
              ·
                refine ⟨66594084137915758522493021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44396056091943839014995347 66594084137915758522493021)
                ·
                  refine ⟨24972781551718409445934883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66594084137915758522493021 24972781551718409445934883)
                  ·
                    refine ⟨37459172327577614168902325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24972781551718409445934883 37459172327577614168902325)
                    ·
                      refine ⟨3511797405710401328334593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37459172327577614168902325 3511797405710401328334593)
                      ·
                        rfl

theorem cell23_6839201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_6839201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6839201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6839201 prefixEnd_6839201 := by exact prefixLift 6839201
  have htrace : WordTrace (prefixWord ++ tailWord_6839201) baseStart_6839201 baseEnd_6839201 := by
    simpa [prefixWord, tailWord_6839201, baseEnd_6839201] using wordTrace_append hprefix tailTrace_6839201
  have hstable : (prefixWord ++ tailWord_6839201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6839201).length < 2 ^ (prefixWord ++ tailWord_6839201).sum := by decide
  have hdescent : baseEnd_6839201 < baseStart_6839201 := by decide
  rcases family_descends (prefixWord ++ tailWord_6839201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6839204 : List Nat := [2, 3, 1, 2, 1, 2, 2, 10]
def baseStart_6839204 : Nat := 118140960795 + 6839204 * 2 ^ 59
def prefixEnd_6839204 : Nat := 4983230072969 + 3 ^ 40 * 6839204 * 2
def baseEnd_6839204 : Nat := 130066627635272770985077

theorem tailTrace_6839204 : CollatzResearch.WordTrace tailWord_6839204 prefixEnd_6839204 130066627635272770985077 := by
  unfold tailWord_6839204
  simp only [CollatzResearch.WordTrace]
  refine ⟨124723131357369712947826333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166297508476492950597101777 124723131357369712947826333)
  ·
    refine ⟨46771174259013642355434875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124723131357369712947826333 46771174259013642355434875)
    ·
      refine ⟨70156761388520463533152313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46771174259013642355434875 70156761388520463533152313)
      ·
        refine ⟨52617571041390347649864235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70156761388520463533152313 52617571041390347649864235)
        ·
          refine ⟨78926356562085521474796353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52617571041390347649864235 78926356562085521474796353)
          ·
            refine ⟨59194767421564141106097265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78926356562085521474796353 59194767421564141106097265)
            ·
              refine ⟨44396075566173105829572949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59194767421564141106097265 44396075566173105829572949)
              ·
                refine ⟨130066627635272770985077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 44396075566173105829572949 130066627635272770985077)
                ·
                  rfl

theorem cell23_6839204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 10].length) (baseStart_6839204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6839204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6839204 prefixEnd_6839204 := by exact prefixLift 6839204
  have htrace : WordTrace (prefixWord ++ tailWord_6839204) baseStart_6839204 baseEnd_6839204 := by
    simpa [prefixWord, tailWord_6839204, baseEnd_6839204] using wordTrace_append hprefix tailTrace_6839204
  have hstable : (prefixWord ++ tailWord_6839204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6839204).length < 2 ^ (prefixWord ++ tailWord_6839204).sum := by decide
  have hdescent : baseEnd_6839204 < baseStart_6839204 := by decide
  rcases family_descends (prefixWord ++ tailWord_6839204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6839232 : List Nat := [2, 1, 1, 2, 3, 3, 3, 3, 1, 2, 2]
def baseStart_6839232 : Nat := 118140960795 + 6839232 * 2 ^ 59
def prefixEnd_6839232 : Nat := 4983230072969 + 3 ^ 40 * 6839232 * 2
def baseEnd_6839232 : Nat := 3511813323610690707046951

theorem tailTrace_6839232 : CollatzResearch.WordTrace tailWord_6839232 prefixEnd_6839232 3511813323610690707046951 := by
  unfold tailWord_6839232
  simp only [CollatzResearch.WordTrace]
  refine ⟨124723641979318993338835975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166298189305758657785114633 124723641979318993338835975)
  ·
    refine ⟨187085462968978490008253963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124723641979318993338835975 187085462968978490008253963)
    ·
      refine ⟨280628194453467735012380945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187085462968978490008253963 280628194453467735012380945)
      ·
        refine ⟨210471145840100801259285709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280628194453467735012380945 210471145840100801259285709)
        ·
          refine ⟨78926679690037800472232141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 210471145840100801259285709 78926679690037800472232141)
          ·
            refine ⟨29597504883764175177087053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78926679690037800472232141 29597504883764175177087053)
            ·
              refine ⟨11099064331411565691407645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29597504883764175177087053 11099064331411565691407645)
              ·
                refine ⟨4162149124279337134277867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11099064331411565691407645 4162149124279337134277867)
                ·
                  refine ⟨6243223686419005701416801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4162149124279337134277867 6243223686419005701416801)
                  ·
                    refine ⟨4682417764814254276062601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6243223686419005701416801 4682417764814254276062601)
                    ·
                      refine ⟨3511813323610690707046951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4682417764814254276062601 3511813323610690707046951)
                      ·
                        rfl

theorem cell23_6839232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 3, 1, 2, 2].length) (baseStart_6839232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6839232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6839232 prefixEnd_6839232 := by exact prefixLift 6839232
  have htrace : WordTrace (prefixWord ++ tailWord_6839232) baseStart_6839232 baseEnd_6839232 := by
    simpa [prefixWord, tailWord_6839232, baseEnd_6839232] using wordTrace_append hprefix tailTrace_6839232
  have hstable : (prefixWord ++ tailWord_6839232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6839232).length < 2 ^ (prefixWord ++ tailWord_6839232).sum := by decide
  have hdescent : baseEnd_6839232 < baseStart_6839232 := by decide
  rcases family_descends (prefixWord ++ tailWord_6839232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6839248 : List Nat := [2, 1, 1, 1, 1, 2, 3, 6, 2, 1, 3]
def baseStart_6839248 : Nat := 118140960795 + 6839248 * 2 ^ 59
def prefixEnd_6839248 : Nat := 4983230072969 + 3 ^ 40 * 6839248 * 2
def baseEnd_6839248 : Nat := 3511821539301162644446877

theorem tailTrace_6839248 : CollatzResearch.WordTrace tailWord_6839248 prefixEnd_6839248 3511821539301162644446877 := by
  unfold tailWord_6839248
  simp only [CollatzResearch.WordTrace]
  refine ⟨124723933763290010705127199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166298578351053347606836265 124723933763290010705127199)
  ·
    refine ⟨187085900644935016057690799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124723933763290010705127199 187085900644935016057690799)
    ·
      refine ⟨280628850967402524086536199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187085900644935016057690799 280628850967402524086536199)
      ·
        refine ⟨420943276451103786129804299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280628850967402524086536199 420943276451103786129804299)
        ·
          refine ⟨631414914676655679194706449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 420943276451103786129804299 631414914676655679194706449)
          ·
            refine ⟨473561186007491759396029837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 631414914676655679194706449 473561186007491759396029837)
            ·
              refine ⟨177585444752809409773511189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 473561186007491759396029837 177585444752809409773511189)
              ·
                refine ⟨8324317722787941083133337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 177585444752809409773511189 8324317722787941083133337)
                ·
                  refine ⟨6243238292090955812350003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8324317722787941083133337 6243238292090955812350003)
                  ·
                    refine ⟨9364857438136433718525005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6243238292090955812350003 9364857438136433718525005)
                    ·
                      refine ⟨3511821539301162644446877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9364857438136433718525005 3511821539301162644446877)
                      ·
                        rfl

theorem cell23_6839248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 6, 2, 1, 3].length) (baseStart_6839248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6839248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6839248 prefixEnd_6839248 := by exact prefixLift 6839248
  have htrace : WordTrace (prefixWord ++ tailWord_6839248) baseStart_6839248 baseEnd_6839248 := by
    simpa [prefixWord, tailWord_6839248, baseEnd_6839248] using wordTrace_append hprefix tailTrace_6839248
  have hstable : (prefixWord ++ tailWord_6839248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6839248).length < 2 ^ (prefixWord ++ tailWord_6839248).sum := by decide
  have hdescent : baseEnd_6839248 < baseStart_6839248 := by decide
  rcases family_descends (prefixWord ++ tailWord_6839248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6839269 : List Nat := [1, 3, 1, 6, 2, 1, 1, 2, 1, 2, 3]
def baseStart_6839269 : Nat := 118140960795 + 6839269 * 2 ^ 59
def prefixEnd_6839269 : Nat := 4983230072969 + 3 ^ 40 * 6839269 * 2
def baseEnd_6839269 : Nat := 3511832322394907062284281

theorem tailTrace_6839269 : CollatzResearch.WordTrace tailWord_6839269 prefixEnd_6839269 3511832322394907062284281 := by
  unfold tailWord_6839269
  simp only [CollatzResearch.WordTrace]
  refine ⟨249448633459503941996768861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166299088973002627997845907 249448633459503941996768861)
  ·
    refine ⟨93543237547313978248788323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249448633459503941996768861 93543237547313978248788323)
    ·
      refine ⟨140314856320970967373182485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93543237547313978248788323 140314856320970967373182485)
      ·
        refine ⟨6577258890045514095617929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 140314856320970967373182485 6577258890045514095617929)
        ·
          refine ⟨4932944167534135571713447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6577258890045514095617929 4932944167534135571713447)
          ·
            refine ⟨7399416251301203357570171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4932944167534135571713447 7399416251301203357570171)
            ·
              refine ⟨11099124376951805036355257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7399416251301203357570171 11099124376951805036355257)
              ·
                refine ⟨8324343282713853777266443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11099124376951805036355257 8324343282713853777266443)
                ·
                  refine ⟨12486514924070780665899665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8324343282713853777266443 12486514924070780665899665)
                  ·
                    refine ⟨9364886193053085499424749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12486514924070780665899665 9364886193053085499424749)
                    ·
                      refine ⟨3511832322394907062284281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9364886193053085499424749 3511832322394907062284281)
                      ·
                        rfl

theorem cell23_6839269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_6839269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6839269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6839269 prefixEnd_6839269 := by exact prefixLift 6839269
  have htrace : WordTrace (prefixWord ++ tailWord_6839269) baseStart_6839269 baseEnd_6839269 := by
    simpa [prefixWord, tailWord_6839269, baseEnd_6839269] using wordTrace_append hprefix tailTrace_6839269
  have hstable : (prefixWord ++ tailWord_6839269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6839269).length < 2 ^ (prefixWord ++ tailWord_6839269).sum := by decide
  have hdescent : baseEnd_6839269 < baseStart_6839269 := by decide
  rcases family_descends (prefixWord ++ tailWord_6839269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6839292 : List Nat := [2, 2, 2, 1, 2, 4, 3, 1, 1, 3, 2]
def baseStart_6839292 : Nat := 118140960795 + 6839292 * 2 ^ 59
def prefixEnd_6839292 : Nat := 4983230072969 + 3 ^ 40 * 6839292 * 2
def baseEnd_6839292 : Nat := 3511844132449960472296675

theorem tailTrace_6839292 : CollatzResearch.WordTrace tailWord_6839292 prefixEnd_6839292 3511844132449960472296675 := by
  unfold tailWord_6839292
  simp only [CollatzResearch.WordTrace]
  refine ⟨124724736169210308462428065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166299648225613744616570753 124724736169210308462428065)
  ·
    refine ⟨93543552126907731346821049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124724736169210308462428065 93543552126907731346821049)
    ·
      refine ⟨70157664095180798510115787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93543552126907731346821049 70157664095180798510115787)
      ·
        refine ⟨105236496142771197765173681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70157664095180798510115787 105236496142771197765173681)
        ·
          refine ⟨78927372107078398323880261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105236496142771197765173681 78927372107078398323880261)
          ·
            refine ⟨14798882270077199685727549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78927372107078398323880261 14798882270077199685727549)
            ·
              refine ⟨5549580851278949882147831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14798882270077199685727549 5549580851278949882147831)
              ·
                refine ⟨8324371276918424823221747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5549580851278949882147831 8324371276918424823221747)
                ·
                  refine ⟨12486556915377637234832621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8324371276918424823221747 12486556915377637234832621)
                  ·
                    refine ⟨4682458843266613963062233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12486556915377637234832621 4682458843266613963062233)
                    ·
                      refine ⟨3511844132449960472296675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4682458843266613963062233 3511844132449960472296675)
                      ·
                        rfl

theorem cell23_6839292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 3, 1, 1, 3, 2].length) (baseStart_6839292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6839292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6839292 prefixEnd_6839292 := by exact prefixLift 6839292
  have htrace : WordTrace (prefixWord ++ tailWord_6839292) baseStart_6839292 baseEnd_6839292 := by
    simpa [prefixWord, tailWord_6839292, baseEnd_6839292] using wordTrace_append hprefix tailTrace_6839292
  have hstable : (prefixWord ++ tailWord_6839292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6839292).length < 2 ^ (prefixWord ++ tailWord_6839292).sum := by decide
  have hdescent : baseEnd_6839292 < baseStart_6839292 := by decide
  rcases family_descends (prefixWord ++ tailWord_6839292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6839301 : List Nat := [1, 3, 1, 1, 2, 3, 2, 2, 2, 2, 4]
def baseStart_6839301 : Nat := 118140960795 + 6839301 * 2 ^ 59
def prefixEnd_6839301 : Nat := 4983230072969 + 3 ^ 40 * 6839301 * 2
def baseEnd_6839301 : Nat := 3511848753775850937084133

theorem tailTrace_6839301 : CollatzResearch.WordTrace tailWord_6839301 prefixEnd_6839301 3511848753775850937084133 := by
  unfold tailWord_6839301
  simp only [CollatzResearch.WordTrace]
  refine ⟨249449800595388011461933757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166299867063592007641289171 249449800595388011461933757)
  ·
    refine ⟨93543675223270504298225159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249449800595388011461933757 93543675223270504298225159)
    ·
      refine ⟨140315512834905756447337739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93543675223270504298225159 140315512834905756447337739)
      ·
        refine ⟨210473269252358634671006609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140315512834905756447337739 210473269252358634671006609)
        ·
          refine ⟨157854951939268976003254957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210473269252358634671006609 157854951939268976003254957)
          ·
            refine ⟨59195606977225866001220609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157854951939268976003254957 59195606977225866001220609)
            ·
              refine ⟨44396705232919399500915457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59195606977225866001220609 44396705232919399500915457)
              ·
                refine ⟨33297528924689549625686593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44396705232919399500915457 33297528924689549625686593)
                ·
                  refine ⟨24973146693517162219264945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33297528924689549625686593 24973146693517162219264945)
                  ·
                    refine ⟨18729860020137871664448709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24973146693517162219264945 18729860020137871664448709)
                    ·
                      refine ⟨3511848753775850937084133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18729860020137871664448709 3511848753775850937084133)
                      ·
                        rfl

theorem cell23_6839301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 2, 2, 2, 4].length) (baseStart_6839301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6839301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6839301 prefixEnd_6839301 := by exact prefixLift 6839301
  have htrace : WordTrace (prefixWord ++ tailWord_6839301) baseStart_6839301 baseEnd_6839301 := by
    simpa [prefixWord, tailWord_6839301, baseEnd_6839301] using wordTrace_append hprefix tailTrace_6839301
  have hstable : (prefixWord ++ tailWord_6839301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6839301).length < 2 ^ (prefixWord ++ tailWord_6839301).sum := by decide
  have hdescent : baseEnd_6839301 < baseStart_6839301 := by decide
  rcases family_descends (prefixWord ++ tailWord_6839301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6839321 : List Nat := [1, 2, 1, 2, 1, 1, 5, 1, 1, 5, 3]
def baseStart_6839321 : Nat := 118140960795 + 6839321 * 2 ^ 59
def prefixEnd_6839321 : Nat := 4983230072969 + 3 ^ 40 * 6839321 * 2
def baseEnd_6839321 : Nat := 3511859023388940858834041

theorem tailTrace_6839321 : CollatzResearch.WordTrace tailWord_6839321 prefixEnd_6839321 3511859023388940858834041 := by
  unfold tailWord_6839321
  simp only [CollatzResearch.WordTrace]
  refine ⟨249450530055315554877661817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166300353370210369918441211 249450530055315554877661817)
  ·
    refine ⟨187087897541486666158246363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249450530055315554877661817 187087897541486666158246363)
    ·
      refine ⟨280631846312229999237369545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187087897541486666158246363 280631846312229999237369545)
      ·
        refine ⟨210473884734172499428027159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280631846312229999237369545 210473884734172499428027159)
        ·
          refine ⟨315710827101258749142040739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210473884734172499428027159 315710827101258749142040739)
          ·
            refine ⟨473566240651888123713061109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315710827101258749142040739 473566240651888123713061109)
            ·
              refine ⟨44396835061114511598099479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 473566240651888123713061109 44396835061114511598099479)
              ·
                refine ⟨66595252591671767397149219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44396835061114511598099479 66595252591671767397149219)
                ·
                  refine ⟨99892878887507651095723829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66595252591671767397149219 99892878887507651095723829)
                  ·
                    refine ⟨9364957395703842290224109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 99892878887507651095723829 9364957395703842290224109)
                    ·
                      refine ⟨3511859023388940858834041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9364957395703842290224109 3511859023388940858834041)
                      ·
                        rfl

theorem cell23_6839321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 5, 3].length) (baseStart_6839321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6839321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6839321 prefixEnd_6839321 := by exact prefixLift 6839321
  have htrace : WordTrace (prefixWord ++ tailWord_6839321) baseStart_6839321 baseEnd_6839321 := by
    simpa [prefixWord, tailWord_6839321, baseEnd_6839321] using wordTrace_append hprefix tailTrace_6839321
  have hstable : (prefixWord ++ tailWord_6839321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6839321).length < 2 ^ (prefixWord ++ tailWord_6839321).sum := by decide
  have hdescent : baseEnd_6839321 < baseStart_6839321 := by decide
  rcases family_descends (prefixWord ++ tailWord_6839321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6839378 : List Nat := [3, 2, 2, 1, 3, 1, 1, 2, 1, 3, 4]
def baseStart_6839378 : Nat := 118140960795 + 6839378 * 2 ^ 59
def prefixEnd_6839378 : Nat := 4983230072969 + 3 ^ 40 * 6839378 * 2
def baseEnd_6839378 : Nat := 3511888291786247135821279

theorem tailTrace_6839378 : CollatzResearch.WordTrace tailWord_6839378 prefixEnd_6839378 3511888291786247135821279 := by
  unfold tailWord_6839378
  simp only [CollatzResearch.WordTrace]
  refine ⟨62363152254027263403121697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166301739344072702408324525 62363152254027263403121697)
  ·
    refine ⟨46772364190520447552341273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62363152254027263403121697 46772364190520447552341273)
    ·
      refine ⟨35079273142890335664255955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46772364190520447552341273 35079273142890335664255955)
      ·
        refine ⟨52618909714335503496383933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35079273142890335664255955 52618909714335503496383933)
        ·
          refine ⟨19732091142875813811143975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52618909714335503496383933 19732091142875813811143975)
          ·
            refine ⟨29598136714313720716715963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19732091142875813811143975 29598136714313720716715963)
            ·
              refine ⟨44397205071470581075073945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29598136714313720716715963 44397205071470581075073945)
              ·
                refine ⟨33297903803602935806305459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44397205071470581075073945 33297903803602935806305459)
                ·
                  refine ⟨49946855705404403709458189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33297903803602935806305459 49946855705404403709458189)
                  ·
                    refine ⟨18730070889526651391046821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49946855705404403709458189 18730070889526651391046821)
                    ·
                      refine ⟨3511888291786247135821279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18730070889526651391046821 3511888291786247135821279)
                      ·
                        rfl

theorem cell23_6839378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_6839378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6839378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6839378 prefixEnd_6839378 := by exact prefixLift 6839378
  have htrace : WordTrace (prefixWord ++ tailWord_6839378) baseStart_6839378 baseEnd_6839378 := by
    simpa [prefixWord, tailWord_6839378, baseEnd_6839378] using wordTrace_append hprefix tailTrace_6839378
  have hstable : (prefixWord ++ tailWord_6839378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6839378).length < 2 ^ (prefixWord ++ tailWord_6839378).sum := by decide
  have hdescent : baseEnd_6839378 < baseStart_6839378 := by decide
  rcases family_descends (prefixWord ++ tailWord_6839378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6839391 : List Nat := [1, 1, 2, 3, 1, 1, 3, 1, 2, 4, 4]
def baseStart_6839391 : Nat := 118140960795 + 6839391 * 2 ^ 59
def prefixEnd_6839391 : Nat := 4983230072969 + 3 ^ 40 * 6839391 * 2
def baseEnd_6839391 : Nat := 3511894967034755584958719

theorem tailTrace_6839391 : CollatzResearch.WordTrace tailWord_6839391 prefixEnd_6839391 3511894967034755584958719 := by
  unfold tailWord_6839391
  simp only [CollatzResearch.WordTrace]
  refine ⟨249453083165061956832710027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166302055443374637888473351 249453083165061956832710027)
  ·
    refine ⟨374179624747592935249065041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249453083165061956832710027 374179624747592935249065041)
    ·
      refine ⟨280634718560694701436798781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 374179624747592935249065041 280634718560694701436798781)
      ·
        refine ⟨105238019460260513038799543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 280634718560694701436798781 105238019460260513038799543)
        ·
          refine ⟨157857029190390769558199315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105238019460260513038799543 157857029190390769558199315)
          ·
            refine ⟨236785543785586154337298973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157857029190390769558199315 236785543785586154337298973)
            ·
              refine ⟨88794578919594807876487115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 236785543785586154337298973 88794578919594807876487115)
              ·
                refine ⟨133191868379392211814730673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88794578919594807876487115 133191868379392211814730673)
                ·
                  refine ⟨99893901284544158861048005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 133191868379392211814730673 99893901284544158861048005)
                  ·
                    refine ⟨18730106490852029786446501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 99893901284544158861048005 18730106490852029786446501)
                    ·
                      refine ⟨3511894967034755584958719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18730106490852029786446501 3511894967034755584958719)
                      ·
                        rfl

theorem cell23_6839391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 4, 4].length) (baseStart_6839391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6839391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6839391 prefixEnd_6839391 := by exact prefixLift 6839391
  have htrace : WordTrace (prefixWord ++ tailWord_6839391) baseStart_6839391 baseEnd_6839391 := by
    simpa [prefixWord, tailWord_6839391, baseEnd_6839391] using wordTrace_append hprefix tailTrace_6839391
  have hstable : (prefixWord ++ tailWord_6839391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6839391).length < 2 ^ (prefixWord ++ tailWord_6839391).sum := by decide
  have hdescent : baseEnd_6839391 < baseStart_6839391 := by decide
  rcases family_descends (prefixWord ++ tailWord_6839391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6839401 : List Nat := [1, 2, 1, 1, 1, 6, 1, 2, 8]
def baseStart_6839401 : Nat := 118140960795 + 6839401 * 2 ^ 59
def prefixEnd_6839401 : Nat := 4983230072969 + 3 ^ 40 * 6839401 * 2
def baseEnd_6839401 : Nat := 390211122426811171759297

theorem tailTrace_6839401 : CollatzResearch.WordTrace tailWord_6839401 prefixEnd_6839401 390211122426811171759297 := by
  unfold tailWord_6839401
  simp only [CollatzResearch.WordTrace]
  refine ⟨249453447895025728540574057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166302298596683819027049371 249453447895025728540574057)
  ·
    refine ⟨187090085921269296405430543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249453447895025728540574057 187090085921269296405430543)
    ·
      refine ⟨280635128881903944608145815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187090085921269296405430543 280635128881903944608145815)
      ·
        refine ⟨420952693322855916912218723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280635128881903944608145815 420952693322855916912218723)
        ·
          refine ⟨631429039984283875368328085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 420952693322855916912218723 631429039984283875368328085)
          ·
            refine ⟨29598236249263306657890379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 631429039984283875368328085 29598236249263306657890379)
            ·
              refine ⟨44397354373894959986835569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29598236249263306657890379 44397354373894959986835569)
              ·
                refine ⟨33298015780421219990126677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44397354373894959986835569 33298015780421219990126677)
                ·
                  refine ⟨390211122426811171759297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33298015780421219990126677 390211122426811171759297)
                  ·
                    rfl

theorem cell23_6839401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 2, 8].length) (baseStart_6839401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6839401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6839401 prefixEnd_6839401 := by exact prefixLift 6839401
  have htrace : WordTrace (prefixWord ++ tailWord_6839401) baseStart_6839401 baseEnd_6839401 := by
    simpa [prefixWord, tailWord_6839401, baseEnd_6839401] using wordTrace_append hprefix tailTrace_6839401
  have hstable : (prefixWord ++ tailWord_6839401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6839401).length < 2 ^ (prefixWord ++ tailWord_6839401).sum := by decide
  have hdescent : baseEnd_6839401 < baseStart_6839401 := by decide
  rcases family_descends (prefixWord ++ tailWord_6839401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6839431 : List Nat := [1, 1, 4, 2, 1, 1, 1, 1, 2, 9]
def baseStart_6839431 : Nat := 118140960795 + 6839431 * 2 ^ 59
def prefixEnd_6839431 : Nat := 4983230072969 + 3 ^ 40 * 6839431 * 2
def baseEnd_6839431 : Nat := 1170638502086978476152845

theorem tailTrace_6839431 : CollatzResearch.WordTrace tailWord_6839431 prefixEnd_6839431 1170638502086978476152845 := by
  unfold tailWord_6839431
  simp only [CollatzResearch.WordTrace]
  refine ⟨249454542084917043664166147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166303028056611362442777431 249454542084917043664166147)
  ·
    refine ⟨374181813127375565496249221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249454542084917043664166147 374181813127375565496249221)
    ·
      refine ⟨70159089961382918530546729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 374181813127375565496249221 70159089961382918530546729)
      ·
        refine ⟨52619317471037188897910047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70159089961382918530546729 52619317471037188897910047)
        ·
          refine ⟨78928976206555783346865071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52619317471037188897910047 78928976206555783346865071)
          ·
            refine ⟨118393464309833675020297607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78928976206555783346865071 118393464309833675020297607)
            ·
              refine ⟨177590196464750512530446411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118393464309833675020297607 177590196464750512530446411)
              ·
                refine ⟨266385294697125768795669617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177590196464750512530446411 266385294697125768795669617)
                ·
                  refine ⟨199788971022844326596752213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 266385294697125768795669617 199788971022844326596752213)
                  ·
                    refine ⟨1170638502086978476152845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 199788971022844326596752213 1170638502086978476152845)
                    ·
                      rfl

theorem cell23_6839431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 9].length) (baseStart_6839431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6839431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6839431 prefixEnd_6839431 := by exact prefixLift 6839431
  have htrace : WordTrace (prefixWord ++ tailWord_6839431) baseStart_6839431 baseEnd_6839431 := by
    simpa [prefixWord, tailWord_6839431, baseEnd_6839431] using wordTrace_append hprefix tailTrace_6839431
  have hstable : (prefixWord ++ tailWord_6839431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6839431).length < 2 ^ (prefixWord ++ tailWord_6839431).sum := by decide
  have hdescent : baseEnd_6839431 < baseStart_6839431 := by decide
  rcases family_descends (prefixWord ++ tailWord_6839431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6839491 : List Nat := [1, 1, 1, 3, 1, 1, 1, 14]
def baseStart_6839491 : Nat := 118140960795 + 6839491 * 2 ^ 59
def prefixEnd_6839491 : Nat := 4983230072969 + 3 ^ 40 * 6839491 * 2
def baseEnd_6839491 : Nat := 130072085744452044211417

theorem tailTrace_6839491 : CollatzResearch.WordTrace tailWord_6839491 prefixEnd_6839491 130072085744452044211417 := by
  unfold tailWord_6839491
  simp only [CollatzResearch.WordTrace]
  refine ⟨249456730464699673911350327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166304486976466449274233551 249456730464699673911350327)
  ·
    refine ⟨374185095697049510867025491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249456730464699673911350327 374185095697049510867025491)
    ·
      refine ⟨561277643545574266300538237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374185095697049510867025491 561277643545574266300538237)
      ·
        refine ⟨210479116329590349862701839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 561277643545574266300538237 210479116329590349862701839)
        ·
          refine ⟨315718674494385524794052759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210479116329590349862701839 315718674494385524794052759)
          ·
            refine ⟨473578011741578287191079139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315718674494385524794052759 473578011741578287191079139)
            ·
              refine ⟨710367017612367430786618709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 473578011741578287191079139 710367017612367430786618709)
              ·
                refine ⟨130072085744452044211417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 14 710367017612367430786618709 130072085744452044211417)
                ·
                  rfl

theorem cell23_6839491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 14].length) (baseStart_6839491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6839491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6839491 prefixEnd_6839491 := by exact prefixLift 6839491
  have htrace : WordTrace (prefixWord ++ tailWord_6839491) baseStart_6839491 baseEnd_6839491 := by
    simpa [prefixWord, tailWord_6839491, baseEnd_6839491] using wordTrace_append hprefix tailTrace_6839491
  have hstable : (prefixWord ++ tailWord_6839491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6839491).length < 2 ^ (prefixWord ++ tailWord_6839491).sum := by decide
  have hdescent : baseEnd_6839491 < baseStart_6839491 := by decide
  rcases family_descends (prefixWord ++ tailWord_6839491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6839505 : List Nat := [1, 2, 2, 1, 2, 2, 1, 6, 1, 2, 3]
def baseStart_6839505 : Nat := 118140960795 + 6839505 * 2 ^ 59
def prefixEnd_6839505 : Nat := 4983230072969 + 3 ^ 40 * 6839505 * 2
def baseEnd_6839505 : Nat := 3511953503829368138933195

theorem tailTrace_6839505 : CollatzResearch.WordTrace tailWord_6839505 prefixEnd_6839505 3511953503829368138933195 := by
  unfold tailWord_6839505
  simp only [CollatzResearch.WordTrace]
  refine ⟨249457241086648954302359969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166304827391099302868239979 249457241086648954302359969)
  ·
    refine ⟨187092930814986715726769977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249457241086648954302359969 187092930814986715726769977)
    ·
      refine ⟨140319698111240036795077483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187092930814986715726769977 140319698111240036795077483)
      ·
        refine ⟨210479547166860055192616225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140319698111240036795077483 210479547166860055192616225)
        ·
          refine ⟨157859660375145041394462169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210479547166860055192616225 157859660375145041394462169)
          ·
            refine ⟨118394745281358781045846627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157859660375145041394462169 118394745281358781045846627)
            ·
              refine ⟨177592117922038171568769941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118394745281358781045846627 177592117922038171568769941)
              ·
                refine ⟨8324630527595539292286091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 177592117922038171568769941 8324630527595539292286091)
                ·
                  refine ⟨12486945791393308938429137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8324630527595539292286091 12486945791393308938429137)
                  ·
                    refine ⟨9365209343544981703821853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12486945791393308938429137 9365209343544981703821853)
                    ·
                      refine ⟨3511953503829368138933195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9365209343544981703821853 3511953503829368138933195)
                      ·
                        rfl

theorem cell23_6839505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 6, 1, 2, 3].length) (baseStart_6839505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6839505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6839505 prefixEnd_6839505 := by exact prefixLift 6839505
  have htrace : WordTrace (prefixWord ++ tailWord_6839505) baseStart_6839505 baseEnd_6839505 := by
    simpa [prefixWord, tailWord_6839505, baseEnd_6839505] using wordTrace_append hprefix tailTrace_6839505
  have hstable : (prefixWord ++ tailWord_6839505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6839505).length < 2 ^ (prefixWord ++ tailWord_6839505).sum := by decide
  have hdescent : baseEnd_6839505 < baseStart_6839505 := by decide
  rcases family_descends (prefixWord ++ tailWord_6839505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6839519 : List Nat := [1, 1, 2, 3, 2, 1, 3, 5, 1, 2, 2]
def baseStart_6839519 : Nat := 118140960795 + 6839519 * 2 ^ 59
def prefixEnd_6839519 : Nat := 4983230072969 + 3 ^ 40 * 6839519 * 2
def baseEnd_6839519 : Nat := 3511960692558531084158131

theorem tailTrace_6839519 : CollatzResearch.WordTrace tailWord_6839519 prefixEnd_6839519 3511960692558531084158131 := by
  unfold tailWord_6839519
  simp only [CollatzResearch.WordTrace]
  refine ⟨249457751708598234693369611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166305167805732156462246407 249457751708598234693369611)
  ·
    refine ⟨374186627562897352040054417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249457751708598234693369611 374186627562897352040054417)
    ·
      refine ⟨280639970672173014030040813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 374186627562897352040054417 280639970672173014030040813)
      ·
        refine ⟨105239989002064880261265305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 280639970672173014030040813 105239989002064880261265305)
        ·
          refine ⟨78929991751548660195948979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105239989002064880261265305 78929991751548660195948979)
          ·
            refine ⟨118394987627322990293923469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78929991751548660195948979 118394987627322990293923469)
            ·
              refine ⟨44398120360246121360221301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118394987627322990293923469 44398120360246121360221301)
              ·
                refine ⟨4162323783773073877520747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44398120360246121360221301 4162323783773073877520747)
                ·
                  refine ⟨6243485675659610816281121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4162323783773073877520747 6243485675659610816281121)
                  ·
                    refine ⟨4682614256744708112210841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6243485675659610816281121 4682614256744708112210841)
                    ·
                      refine ⟨3511960692558531084158131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4682614256744708112210841 3511960692558531084158131)
                      ·
                        rfl

theorem cell23_6839519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 5, 1, 2, 2].length) (baseStart_6839519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6839519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6839519 prefixEnd_6839519 := by exact prefixLift 6839519
  have htrace : WordTrace (prefixWord ++ tailWord_6839519) baseStart_6839519 baseEnd_6839519 := by
    simpa [prefixWord, tailWord_6839519, baseEnd_6839519] using wordTrace_append hprefix tailTrace_6839519
  have hstable : (prefixWord ++ tailWord_6839519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6839519).length < 2 ^ (prefixWord ++ tailWord_6839519).sum := by decide
  have hdescent : baseEnd_6839519 < baseStart_6839519 := by decide
  rcases family_descends (prefixWord ++ tailWord_6839519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6839613 : List Nat := [1, 4, 1, 5, 1, 2, 1, 2, 1, 3, 2]
def baseStart_6839613 : Nat := 118140960795 + 6839613 * 2 ^ 59
def prefixEnd_6839613 : Nat := 4983230072969 + 3 ^ 40 * 6839613 * 2
def baseEnd_6839613 : Nat := 3512008959740053716382699

theorem tailTrace_6839613 : CollatzResearch.WordTrace tailWord_6839613 prefixEnd_6839613 3512008959740053716382699 := by
  unfold tailWord_6839613
  simp only [CollatzResearch.WordTrace]
  refine ⟨249461180170257688747291493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166307453446838459164860995 249461180170257688747291493)
  ·
    refine ⟨46773971281923316640117155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 249461180170257688747291493 46773971281923316640117155)
    ·
      refine ⟨70160956922884974960175733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46773971281923316640117155 70160956922884974960175733)
      ·
        refine ⟨6577589711520466402516475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 70160956922884974960175733 6577589711520466402516475)
        ·
          refine ⟨9866384567280699603774713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6577589711520466402516475 9866384567280699603774713)
          ·
            refine ⟨7399788425460524702831035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9866384567280699603774713 7399788425460524702831035)
            ·
              refine ⟨11099682638190787054246553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7399788425460524702831035 11099682638190787054246553)
              ·
                refine ⟨8324761978643090290684915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11099682638190787054246553 8324761978643090290684915)
                ·
                  refine ⟨12487142967964635436027373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8324761978643090290684915 12487142967964635436027373)
                  ·
                    refine ⟨4682678612986738288510265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12487142967964635436027373 4682678612986738288510265)
                    ·
                      refine ⟨3512008959740053716382699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4682678612986738288510265 3512008959740053716382699)
                      ·
                        rfl

theorem cell23_6839613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_6839613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6839613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6839613 prefixEnd_6839613 := by exact prefixLift 6839613
  have htrace : WordTrace (prefixWord ++ tailWord_6839613) baseStart_6839613 baseEnd_6839613 := by
    simpa [prefixWord, tailWord_6839613, baseEnd_6839613] using wordTrace_append hprefix tailTrace_6839613
  have hstable : (prefixWord ++ tailWord_6839613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6839613).length < 2 ^ (prefixWord ++ tailWord_6839613).sum := by decide
  have hdescent : baseEnd_6839613 < baseStart_6839613 := by decide
  rcases family_descends (prefixWord ++ tailWord_6839613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6839652 : List Nat := [2, 3, 1, 1, 3, 2, 1, 1, 2, 5, 2]
def baseStart_6839652 : Nat := 118140960795 + 6839652 * 2 ^ 59
def prefixEnd_6839652 : Nat := 4983230072969 + 3 ^ 40 * 6839652 * 2
def baseEnd_6839652 : Nat := 3512028985485579063795019

theorem tailTrace_6839652 : CollatzResearch.WordTrace tailWord_6839652 prefixEnd_6839652 3512028985485579063795019 := by
  unfold tailWord_6839652
  simp only [CollatzResearch.WordTrace]
  refine ⟨124731301308558199203980605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166308401744744265605307473 124731301308558199203980605)
  ·
    refine ⟨46774237990709324701492727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124731301308558199203980605 46774237990709324701492727)
    ·
      refine ⟨70161356986063987052239091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46774237990709324701492727 70161356986063987052239091)
      ·
        refine ⟨105242035479095980578358637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70161356986063987052239091 105242035479095980578358637)
        ·
          refine ⟨39465763304660992716884489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105242035479095980578358637 39465763304660992716884489)
          ·
            refine ⟨29599322478495744537663367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39465763304660992716884489 29599322478495744537663367)
            ·
              refine ⟨44398983717743616806495051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29599322478495744537663367 44398983717743616806495051)
              ·
                refine ⟨66598475576615425209742577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44398983717743616806495051 66598475576615425209742577)
                ·
                  refine ⟨49948856682461568907306933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66598475576615425209742577 49948856682461568907306933)
                  ·
                    refine ⟨4682705313980772085060025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49948856682461568907306933 4682705313980772085060025)
                    ·
                      refine ⟨3512028985485579063795019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4682705313980772085060025 3512028985485579063795019)
                      ·
                        rfl

theorem cell23_6839652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 2, 5, 2].length) (baseStart_6839652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6839652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6839652 prefixEnd_6839652 := by exact prefixLift 6839652
  have htrace : WordTrace (prefixWord ++ tailWord_6839652) baseStart_6839652 baseEnd_6839652 := by
    simpa [prefixWord, tailWord_6839652, baseEnd_6839652] using wordTrace_append hprefix tailTrace_6839652
  have hstable : (prefixWord ++ tailWord_6839652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6839652).length < 2 ^ (prefixWord ++ tailWord_6839652).sum := by decide
  have hdescent : baseEnd_6839652 < baseStart_6839652 := by decide
  rcases family_descends (prefixWord ++ tailWord_6839652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6839665 : List Nat := [1, 2, 2, 2, 1, 2, 2, 2, 4, 1, 4]
def baseStart_6839665 : Nat := 118140960795 + 6839665 * 2 ^ 59
def prefixEnd_6839665 : Nat := 4983230072969 + 3 ^ 40 * 6839665 * 2
def baseEnd_6839665 : Nat := 3512035660734087512932459

theorem tailTrace_6839665 : CollatzResearch.WordTrace tailWord_6839665 prefixEnd_6839665 3512035660734087512932459 := by
  unfold tailWord_6839665
  simp only [CollatzResearch.WordTrace]
  refine ⟨249463076766069301628184449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166308717844046201085456299 249463076766069301628184449)
  ·
    refine ⟨187097307574551976221138337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249463076766069301628184449 187097307574551976221138337)
    ·
      refine ⟨140322980680913982165853753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187097307574551976221138337 140322980680913982165853753)
      ·
        refine ⟨105242235510685486624390315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140322980680913982165853753 105242235510685486624390315)
        ·
          refine ⟨157863353266028229936585473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105242235510685486624390315 157863353266028229936585473)
          ·
            refine ⟨118397514949521172452439105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157863353266028229936585473 118397514949521172452439105)
            ·
              refine ⟨88798136212140879339329329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118397514949521172452439105 88798136212140879339329329)
              ·
                refine ⟨66598602159105659504496997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88798136212140879339329329 66598602159105659504496997)
                ·
                  refine ⟨12487237904832311157093187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66598602159105659504496997 12487237904832311157093187)
                  ·
                    refine ⟨18730856857248466735639781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12487237904832311157093187 18730856857248466735639781)
                    ·
                      refine ⟨3512035660734087512932459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18730856857248466735639781 3512035660734087512932459)
                      ·
                        rfl

theorem cell23_6839665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 4, 1, 4].length) (baseStart_6839665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6839665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6839665 prefixEnd_6839665 := by exact prefixLift 6839665
  have htrace : WordTrace (prefixWord ++ tailWord_6839665) baseStart_6839665 baseEnd_6839665 := by
    simpa [prefixWord, tailWord_6839665, baseEnd_6839665] using wordTrace_append hprefix tailTrace_6839665
  have hstable : (prefixWord ++ tailWord_6839665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6839665).length < 2 ^ (prefixWord ++ tailWord_6839665).sum := by decide
  have hdescent : baseEnd_6839665 < baseStart_6839665 := by decide
  rcases family_descends (prefixWord ++ tailWord_6839665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6839705 : List Nat := [1, 2, 1, 2, 1, 6, 1, 1, 8]
def baseStart_6839705 : Nat := 118140960795 + 6839705 * 2 ^ 59
def prefixEnd_6839705 : Nat := 4983230072969 + 3 ^ 40 * 6839705 * 2
def baseEnd_6839705 : Nat := 390228466662251928492475

theorem tailTrace_6839705 : CollatzResearch.WordTrace tailWord_6839705 prefixEnd_6839705 390228466662251928492475 := by
  unfold tailWord_6839705
  simp only [CollatzResearch.WordTrace]
  refine ⟨249464535685924388459640569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166309690457282925639760379 249464535685924388459640569)
  ·
    refine ⟨187098401764443291344730427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249464535685924388459640569 187098401764443291344730427)
    ·
      refine ⟨280647602646664937017095641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187098401764443291344730427 280647602646664937017095641)
      ·
        refine ⟨210485701984998702762821731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280647602646664937017095641 210485701984998702762821731)
        ·
          refine ⟨315728552977498054144232597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210485701984998702762821731 315728552977498054144232597)
          ·
            refine ⟨14799775920820221288010903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 315728552977498054144232597 14799775920820221288010903)
            ·
              refine ⟨22199663881230331932016355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14799775920820221288010903 22199663881230331932016355)
              ·
                refine ⟨33299495821845497898024533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22199663881230331932016355 33299495821845497898024533)
                ·
                  refine ⟨390228466662251928492475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33299495821845497898024533 390228466662251928492475)
                  ·
                    rfl

theorem cell23_6839705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 1, 8].length) (baseStart_6839705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6839705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6839705 prefixEnd_6839705 := by exact prefixLift 6839705
  have htrace : WordTrace (prefixWord ++ tailWord_6839705) baseStart_6839705 baseEnd_6839705 := by
    simpa [prefixWord, tailWord_6839705, baseEnd_6839705] using wordTrace_append hprefix tailTrace_6839705
  have hstable : (prefixWord ++ tailWord_6839705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6839705).length < 2 ^ (prefixWord ++ tailWord_6839705).sum := by decide
  have hdescent : baseEnd_6839705 < baseStart_6839705 := by decide
  rcases family_descends (prefixWord ++ tailWord_6839705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6839709 : List Nat := [1, 4, 2, 1, 3, 2, 2, 1, 3, 4]
def baseStart_6839709 : Nat := 118140960795 + 6839709 * 2 ^ 59
def prefixEnd_6839709 : Nat := 4983230072969 + 3 ^ 40 * 6839709 * 2
def baseEnd_6839709 : Nat := 1170686084627628446927419

theorem tailTrace_6839709 : CollatzResearch.WordTrace tailWord_6839709 prefixEnd_6839709 1170686084627628446927419 := by
  unfold tailWord_6839709
  simp only [CollatzResearch.WordTrace]
  refine ⟨249464681577909897142786181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166309787718606598095190787 249464681577909897142786181)
  ·
    refine ⟨46774627795858105714272409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 249464681577909897142786181 46774627795858105714272409)
    ·
      refine ⟨35080970846893579285704307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46774627795858105714272409 35080970846893579285704307)
      ·
        refine ⟨52621456270340368928556461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35080970846893579285704307 52621456270340368928556461)
        ·
          refine ⟨19733046101377638348208673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52621456270340368928556461 19733046101377638348208673)
          ·
            refine ⟨14799784576033228761156505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19733046101377638348208673 14799784576033228761156505)
            ·
              refine ⟨11099838432024921570867379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14799784576033228761156505 11099838432024921570867379)
              ·
                refine ⟨16649757648037382356301069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11099838432024921570867379 16649757648037382356301069)
                ·
                  refine ⟨6243659118014018383612901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16649757648037382356301069 6243659118014018383612901)
                  ·
                    refine ⟨1170686084627628446927419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6243659118014018383612901 1170686084627628446927419)
                    ·
                      rfl

theorem cell23_6839709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 1, 3, 4].length) (baseStart_6839709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6839709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6839709 prefixEnd_6839709 := by exact prefixLift 6839709
  have htrace : WordTrace (prefixWord ++ tailWord_6839709) baseStart_6839709 baseEnd_6839709 := by
    simpa [prefixWord, tailWord_6839709, baseEnd_6839709] using wordTrace_append hprefix tailTrace_6839709
  have hstable : (prefixWord ++ tailWord_6839709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6839709).length < 2 ^ (prefixWord ++ tailWord_6839709).sum := by decide
  have hdescent : baseEnd_6839709 < baseStart_6839709 := by decide
  rcases family_descends (prefixWord ++ tailWord_6839709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6839752 : List Nat := [2, 1, 3, 1, 3, 1, 1, 5, 1, 5]
def baseStart_6839752 : Nat := 118140960795 + 6839752 * 2 ^ 59
def prefixEnd_6839752 : Nat := 4983230072969 + 3 ^ 40 * 6839752 * 2
def baseEnd_6839752 : Nat := 1170693444517009557514853

theorem tailTrace_6839752 : CollatzResearch.WordTrace tailWord_6839752 prefixEnd_6839752 1170693444517009557514853 := by
  unfold tailWord_6839752
  simp only [CollatzResearch.WordTrace]
  refine ⟨124733124958377057743300755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166310833277836076991067673 124733124958377057743300755)
  ·
    refine ⟨187099687437565586614951133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124733124958377057743300755 187099687437565586614951133)
    ·
      refine ⟨70162382789087094980606675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187099687437565586614951133 70162382789087094980606675)
      ·
        refine ⟨105243574183630642470910013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70162382789087094980606675 105243574183630642470910013)
        ·
          refine ⟨39466340318861490926591255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105243574183630642470910013 39466340318861490926591255)
          ·
            refine ⟨59199510478292236389886883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39466340318861490926591255 59199510478292236389886883)
            ·
              refine ⟨88799265717438354584830325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59199510478292236389886883 88799265717438354584830325)
              ·
                refine ⟨8324931161009845742327843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 88799265717438354584830325 8324931161009845742327843)
                ·
                  refine ⟨12487396741514768613491765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8324931161009845742327843 12487396741514768613491765)
                  ·
                    refine ⟨1170693444517009557514853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12487396741514768613491765 1170693444517009557514853)
                    ·
                      rfl

theorem cell23_6839752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 5, 1, 5].length) (baseStart_6839752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6839752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6839752 prefixEnd_6839752 := by exact prefixLift 6839752
  have htrace : WordTrace (prefixWord ++ tailWord_6839752) baseStart_6839752 baseEnd_6839752 := by
    simpa [prefixWord, tailWord_6839752, baseEnd_6839752] using wordTrace_append hprefix tailTrace_6839752
  have hstable : (prefixWord ++ tailWord_6839752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6839752).length < 2 ^ (prefixWord ++ tailWord_6839752).sum := by decide
  have hdescent : baseEnd_6839752 < baseStart_6839752 := by decide
  rcases family_descends (prefixWord ++ tailWord_6839752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6839786 : List Nat := [3, 1, 3, 1, 4, 2, 1, 2, 1, 5]
def baseStart_6839786 : Nat := 118140960795 + 6839786 * 2 ^ 59
def prefixEnd_6839786 : Nat := 4983230072969 + 3 ^ 40 * 6839786 * 2
def baseEnd_6839786 : Nat := 1170699263964427179839801

theorem tailTrace_6839786 : CollatzResearch.WordTrace tailWord_6839786 prefixEnd_6839786 1170699263964427179839801 := by
  unfold tailWord_6839786
  simp only [CollatzResearch.WordTrace]
  refine ⟨62366872499657734823334803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166311659999087292862226141 62366872499657734823334803)
  ·
    refine ⟨93550308749486602235002205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62366872499657734823334803 93550308749486602235002205)
    ·
      refine ⟨35081365781057475838125827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93550308749486602235002205 35081365781057475838125827)
      ·
        refine ⟨52622048671586213757188741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35081365781057475838125827 52622048671586213757188741)
        ·
          refine ⟨9866634125922415079472889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52622048671586213757188741 9866634125922415079472889)
          ·
            refine ⟨7399975594441811309604667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9866634125922415079472889 7399975594441811309604667)
            ·
              refine ⟨11099963391662716964407001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7399975594441811309604667 11099963391662716964407001)
              ·
                refine ⟨8324972543747037723305251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11099963391662716964407001 8324972543747037723305251)
                ·
                  refine ⟨12487458815620556584957877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8324972543747037723305251 12487458815620556584957877)
                  ·
                    refine ⟨1170699263964427179839801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12487458815620556584957877 1170699263964427179839801)
                    ·
                      rfl

theorem cell23_6839786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 2, 1, 5].length) (baseStart_6839786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6839786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6839786 prefixEnd_6839786 := by exact prefixLift 6839786
  have htrace : WordTrace (prefixWord ++ tailWord_6839786) baseStart_6839786 baseEnd_6839786 := by
    simpa [prefixWord, tailWord_6839786, baseEnd_6839786] using wordTrace_append hprefix tailTrace_6839786
  have hstable : (prefixWord ++ tailWord_6839786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6839786).length < 2 ^ (prefixWord ++ tailWord_6839786).sum := by decide
  have hdescent : baseEnd_6839786 < baseStart_6839786 := by decide
  rcases family_descends (prefixWord ++ tailWord_6839786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6839802 : List Nat := [3, 1, 1, 1, 1, 2, 5, 2, 1, 2, 4]
def baseStart_6839802 : Nat := 118140960795 + 6839802 * 2 ^ 59
def prefixEnd_6839802 : Nat := 4983230072969 + 3 ^ 40 * 6839802 * 2
def baseEnd_6839802 : Nat := 3512106007583753476919329

theorem tailTrace_6839802 : CollatzResearch.WordTrace tailWord_6839802 prefixEnd_6839802 3512106007583753476919329 := by
  unfold tailWord_6839802
  simp only [CollatzResearch.WordTrace]
  refine ⟨62367018391643243506480415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166312049044381982683947773 62367018391643243506480415)
  ·
    refine ⟨93550527587464865259720623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62367018391643243506480415 93550527587464865259720623)
    ·
      refine ⟨140325791381197297889580935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93550527587464865259720623 140325791381197297889580935)
      ·
        refine ⟨210488687071795946834371403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140325791381197297889580935 210488687071795946834371403)
        ·
          refine ⟨315733030607693920251557105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210488687071795946834371403 315733030607693920251557105)
          ·
            refine ⟨236799772955770440188667829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 315733030607693920251557105 236799772955770440188667829)
            ·
              refine ⟨22199978714603478767687609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 236799772955770440188667829 22199978714603478767687609)
              ·
                refine ⟨16649984035952609075765707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22199978714603478767687609 16649984035952609075765707)
                ·
                  refine ⟨24974976053928913613648561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16649984035952609075765707 24974976053928913613648561)
                  ·
                    refine ⟨18731232040446685210236421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24974976053928913613648561 18731232040446685210236421)
                    ·
                      refine ⟨3512106007583753476919329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18731232040446685210236421 3512106007583753476919329)
                      ·
                        rfl

theorem cell23_6839802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 2, 1, 2, 4].length) (baseStart_6839802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6839802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6839802 prefixEnd_6839802 := by exact prefixLift 6839802
  have htrace : WordTrace (prefixWord ++ tailWord_6839802) baseStart_6839802 baseEnd_6839802 := by
    simpa [prefixWord, tailWord_6839802, baseEnd_6839802] using wordTrace_append hprefix tailTrace_6839802
  have hstable : (prefixWord ++ tailWord_6839802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6839802).length < 2 ^ (prefixWord ++ tailWord_6839802).sum := by decide
  have hdescent : baseEnd_6839802 < baseStart_6839802 := by decide
  rcases family_descends (prefixWord ++ tailWord_6839802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6839812 : List Nat := [2, 3, 2, 3, 2, 11]
def baseStart_6839812 : Nat := 118140960795 + 6839812 * 2 ^ 59
def prefixEnd_6839812 : Nat := 4983230072969 + 3 ^ 40 * 6839812 * 2
def baseEnd_6839812 : Nat := 14453132273211104682281

theorem tailTrace_6839812 : CollatzResearch.WordTrace tailWord_6839812 prefixEnd_6839812 14453132273211104682281 := by
  unfold tailWord_6839812
  simp only [CollatzResearch.WordTrace]
  refine ⟨124734219148268372866892845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166312292197691163822523793 124734219148268372866892845)
  ·
    refine ⟨46775332180600639825084817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124734219148268372866892845 46775332180600639825084817)
    ·
      refine ⟨35081499135450479868813613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46775332180600639825084817 35081499135450479868813613)
      ·
        refine ⟨13155562175793929950805105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35081499135450479868813613 13155562175793929950805105)
        ·
          refine ⟨9866671631845447463103829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13155562175793929950805105 9866671631845447463103829)
          ·
            refine ⟨14453132273211104682281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 9866671631845447463103829 14453132273211104682281)
            ·
              rfl

theorem cell23_6839812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 11].length) (baseStart_6839812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6839812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6839812 prefixEnd_6839812 := by exact prefixLift 6839812
  have htrace : WordTrace (prefixWord ++ tailWord_6839812) baseStart_6839812 baseEnd_6839812 := by
    simpa [prefixWord, tailWord_6839812, baseEnd_6839812] using wordTrace_append hprefix tailTrace_6839812
  have hstable : (prefixWord ++ tailWord_6839812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6839812).length < 2 ^ (prefixWord ++ tailWord_6839812).sum := by decide
  have hdescent : baseEnd_6839812 < baseStart_6839812 := by decide
  rcases family_descends (prefixWord ++ tailWord_6839812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6839825 : List Nat := [1, 2, 2, 1, 1, 2, 3, 1, 1, 9]
def baseStart_6839825 : Nat := 118140960795 + 6839825 * 2 ^ 59
def prefixEnd_6839825 : Nat := 4983230072969 + 3 ^ 40 * 6839825 * 2
def baseEnd_6839825 : Nat := 1170705939212935628977241

theorem tailTrace_6839825 : CollatzResearch.WordTrace tailWord_6839825 prefixEnd_6839825 1170705939212935628977241 := by
  unfold tailWord_6839825
  simp only [CollatzResearch.WordTrace]
  refine ⟨249468912445489648954008929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166312608296993099302672619 249468912445489648954008929)
  ·
    refine ⟨187101684334117236715506697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249468912445489648954008929 187101684334117236715506697)
    ·
      refine ⟨140326263250587927536630023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187101684334117236715506697 140326263250587927536630023)
      ·
        refine ⟨210489394875881891304945035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140326263250587927536630023 210489394875881891304945035)
        ·
          refine ⟨315734092313822836957417553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210489394875881891304945035 315734092313822836957417553)
          ·
            refine ⟨236800569235367127718063165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 315734092313822836957417553 236800569235367127718063165)
            ·
              refine ⟨88800213463262672894273687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 236800569235367127718063165 88800213463262672894273687)
              ·
                refine ⟨133200320194894009341410531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88800213463262672894273687 133200320194894009341410531)
                ·
                  refine ⟨199800480292341014012115797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133200320194894009341410531 199800480292341014012115797)
                  ·
                    refine ⟨1170705939212935628977241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 199800480292341014012115797 1170705939212935628977241)
                    ·
                      rfl

theorem cell23_6839825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 9].length) (baseStart_6839825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6839825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6839825 prefixEnd_6839825 := by exact prefixLift 6839825
  have htrace : WordTrace (prefixWord ++ tailWord_6839825) baseStart_6839825 baseEnd_6839825 := by
    simpa [prefixWord, tailWord_6839825, baseEnd_6839825] using wordTrace_append hprefix tailTrace_6839825
  have hstable : (prefixWord ++ tailWord_6839825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6839825).length < 2 ^ (prefixWord ++ tailWord_6839825).sum := by decide
  have hdescent : baseEnd_6839825 < baseStart_6839825 := by decide
  rcases family_descends (prefixWord ++ tailWord_6839825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6839866 : List Nat := [3, 1, 1, 1, 3, 2, 3, 3, 1, 3, 2]
def baseStart_6839866 : Nat := 118140960795 + 6839866 * 2 ^ 59
def prefixEnd_6839866 : Nat := 4983230072969 + 3 ^ 40 * 6839866 * 2
def baseEnd_6839866 : Nat := 3512138870345641226519035

theorem tailTrace_6839866 : CollatzResearch.WordTrace tailWord_6839866 prefixEnd_6839866 3512138870345641226519035 := by
  unfold tailWord_6839866
  simp only [CollatzResearch.WordTrace]
  refine ⟨62367601959585278239062863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166313605225560741970834301 62367601959585278239062863)
  ·
    refine ⟨93551402939377917358594295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62367601959585278239062863 93551402939377917358594295)
    ·
      refine ⟨140327104409066876037891443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93551402939377917358594295 140327104409066876037891443)
      ·
        refine ⟨210490656613600314056837165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140327104409066876037891443 210490656613600314056837165)
        ·
          refine ⟨78933996230100117771313937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 210490656613600314056837165 78933996230100117771313937)
          ·
            refine ⟨59200497172575088328485453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78933996230100117771313937 59200497172575088328485453)
            ·
              refine ⟨22200186439715658123182045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59200497172575088328485453 22200186439715658123182045)
              ·
                refine ⟨8325069914893371796193267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22200186439715658123182045 8325069914893371796193267)
                ·
                  refine ⟨12487604872340057694289901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8325069914893371796193267 12487604872340057694289901)
                  ·
                    refine ⟨4682851827127521635358713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12487604872340057694289901 4682851827127521635358713)
                    ·
                      refine ⟨3512138870345641226519035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4682851827127521635358713 3512138870345641226519035)
                      ·
                        rfl

theorem cell23_6839866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 3, 1, 3, 2].length) (baseStart_6839866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6839866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6839866 prefixEnd_6839866 := by exact prefixLift 6839866
  have htrace : WordTrace (prefixWord ++ tailWord_6839866) baseStart_6839866 baseEnd_6839866 := by
    simpa [prefixWord, tailWord_6839866, baseEnd_6839866] using wordTrace_append hprefix tailTrace_6839866
  have hstable : (prefixWord ++ tailWord_6839866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6839866).length < 2 ^ (prefixWord ++ tailWord_6839866).sum := by decide
  have hdescent : baseEnd_6839866 < baseStart_6839866 := by decide
  rcases family_descends (prefixWord ++ tailWord_6839866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6839936 : List Nat := [2, 1, 1, 2, 1, 4, 5, 2, 5]
def baseStart_6839936 : Nat := 118140960795 + 6839936 * 2 ^ 59
def prefixEnd_6839936 : Nat := 4983230072969 + 3 ^ 40 * 6839936 * 2
def baseEnd_6839936 : Nat := 390241645999050661404857

theorem tailTrace_6839936 : CollatzResearch.WordTrace tailWord_6839936 prefixEnd_6839936 390241645999050661404857 := by
  unfold tailWord_6839936
  simp only [CollatzResearch.WordTrace]
  refine ⟨124736480474043757455649831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166315307298725009940866441 124736480474043757455649831)
  ·
    refine ⟨187104720711065636183474747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124736480474043757455649831 187104720711065636183474747)
    ·
      refine ⟨280657081066598454275212121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187104720711065636183474747 280657081066598454275212121)
      ·
        refine ⟨210492810799948840706409091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280657081066598454275212121 210492810799948840706409091)
        ·
          refine ⟨315739216199923261059613637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210492810799948840706409091 315739216199923261059613637)
          ·
            refine ⟨59201103037485611448677557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 315739216199923261059613637 59201103037485611448677557)
            ·
              refine ⟨5550103409764276073313521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59201103037485611448677557 5550103409764276073313521)
              ·
                refine ⟨4162577557323207054985141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5550103409764276073313521 4162577557323207054985141)
                ·
                  refine ⟨390241645999050661404857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4162577557323207054985141 390241645999050661404857)
                  ·
                    rfl

theorem cell23_6839936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 5, 2, 5].length) (baseStart_6839936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6839936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6839936 prefixEnd_6839936 := by exact prefixLift 6839936
  have htrace : WordTrace (prefixWord ++ tailWord_6839936) baseStart_6839936 baseEnd_6839936 := by
    simpa [prefixWord, tailWord_6839936, baseEnd_6839936] using wordTrace_append hprefix tailTrace_6839936
  have hstable : (prefixWord ++ tailWord_6839936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6839936).length < 2 ^ (prefixWord ++ tailWord_6839936).sum := by decide
  have hdescent : baseEnd_6839936 < baseStart_6839936 := by decide
  rcases family_descends (prefixWord ++ tailWord_6839936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6839939 : List Nat := [1, 1, 1, 3, 3, 1, 1, 3, 2, 5, 2]
def baseStart_6839939 : Nat := 118140960795 + 6839939 * 2 ^ 59
def prefixEnd_6839939 : Nat := 4983230072969 + 3 ^ 40 * 6839939 * 2
def baseEnd_6839939 : Nat := 3512176354433419440906199

theorem tailTrace_6839939 : CollatzResearch.WordTrace tailWord_6839939 prefixEnd_6839939 3512176354433419440906199 := by
  unfold tailWord_6839939
  simp only [CollatzResearch.WordTrace]
  refine ⟨249473070367076646423658871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166315380244717764282439247 249473070367076646423658871)
  ·
    refine ⟨374209605550614969635488307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249473070367076646423658871 374209605550614969635488307)
    ·
      refine ⟨561314408325922454453232461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374209605550614969635488307 561314408325922454453232461)
      ·
        refine ⟨210492903122220920419962173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 561314408325922454453232461 210492903122220920419962173)
        ·
          refine ⟨78934838670832845157485815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 210492903122220920419962173 78934838670832845157485815)
          ·
            refine ⟨118402258006249267736228723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78934838670832845157485815 118402258006249267736228723)
            ·
              refine ⟨177603387009373901604343085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118402258006249267736228723 177603387009373901604343085)
              ·
                refine ⟨66601270128515213101628657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 177603387009373901604343085 66601270128515213101628657)
                ·
                  refine ⟨49950952596386409826221493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66601270128515213101628657 49950952596386409826221493)
                  ·
                    refine ⟨4682901805911225921208265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49950952596386409826221493 4682901805911225921208265)
                    ·
                      refine ⟨3512176354433419440906199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4682901805911225921208265 3512176354433419440906199)
                      ·
                        rfl

theorem cell23_6839939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 2, 5, 2].length) (baseStart_6839939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6839939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6839939 prefixEnd_6839939 := by exact prefixLift 6839939
  have htrace : WordTrace (prefixWord ++ tailWord_6839939) baseStart_6839939 baseEnd_6839939 := by
    simpa [prefixWord, tailWord_6839939, baseEnd_6839939] using wordTrace_append hprefix tailTrace_6839939
  have hstable : (prefixWord ++ tailWord_6839939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6839939).length < 2 ^ (prefixWord ++ tailWord_6839939).sum := by decide
  have hdescent : baseEnd_6839939 < baseStart_6839939 := by decide
  rcases family_descends (prefixWord ++ tailWord_6839939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6839952 : List Nat := [2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 4]
def baseStart_6839952 : Nat := 118140960795 + 6839952 * 2 ^ 59
def prefixEnd_6839952 : Nat := 4983230072969 + 3 ^ 40 * 6839952 * 2
def baseEnd_6839952 : Nat := 3512183029681927890043639

theorem tailTrace_6839952 : CollatzResearch.WordTrace tailWord_6839952 prefixEnd_6839952 3512183029681927890043639 := by
  unfold tailWord_6839952
  simp only [CollatzResearch.WordTrace]
  refine ⟨124736772258014774821941055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166315696344019699762588073 124736772258014774821941055)
  ·
    refine ⟨187105158387022162232911583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124736772258014774821941055 187105158387022162232911583)
    ·
      refine ⟨280657737580533243349367375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187105158387022162232911583 280657737580533243349367375)
      ·
        refine ⟨420986606370799865024051063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280657737580533243349367375 420986606370799865024051063)
        ·
          refine ⟨631479909556199797536076595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 420986606370799865024051063 631479909556199797536076595)
          ·
            refine ⟨947219864334299696304114893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 631479909556199797536076595 947219864334299696304114893)
            ·
              refine ⟨355207449125362386114043085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 947219864334299696304114893 355207449125362386114043085)
              ·
                refine ⟨133202793422010894792766157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 355207449125362386114043085 133202793422010894792766157)
                ·
                  refine ⟨49951047533254085547287309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 133202793422010894792766157 49951047533254085547287309)
                  ·
                    refine ⟨18731642824970282080232741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49951047533254085547287309 18731642824970282080232741)
                    ·
                      refine ⟨3512183029681927890043639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18731642824970282080232741 3512183029681927890043639)
                      ·
                        rfl

theorem cell23_6839952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 4].length) (baseStart_6839952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6839952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6839952 prefixEnd_6839952 := by exact prefixLift 6839952
  have htrace : WordTrace (prefixWord ++ tailWord_6839952) baseStart_6839952 baseEnd_6839952 := by
    simpa [prefixWord, tailWord_6839952, baseEnd_6839952] using wordTrace_append hprefix tailTrace_6839952
  have hstable : (prefixWord ++ tailWord_6839952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6839952).length < 2 ^ (prefixWord ++ tailWord_6839952).sum := by decide
  have hdescent : baseEnd_6839952 < baseStart_6839952 := by decide
  rcases family_descends (prefixWord ++ tailWord_6839952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6839966 : List Nat := [4, 3, 1, 1, 1, 2, 1, 3, 2, 5]
def baseStart_6839966 : Nat := 118140960795 + 6839966 * 2 ^ 59
def prefixEnd_6839966 : Nat := 4983230072969 + 3 ^ 40 * 6839966 * 2
def baseEnd_6839966 : Nat := 1170730072803696945089525

theorem tailTrace_6839966 : CollatzResearch.WordTrace tailWord_6839966 prefixEnd_6839966 1170730072803696945089525 := by
  unfold tailWord_6839966
  simp only [CollatzResearch.WordTrace]
  refine ⟨31184256892247353754361469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166316036758652553356594501 31184256892247353754361469)
  ·
    refine ⟨11694096334592757657885551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31184256892247353754361469 11694096334592757657885551)
    ·
      refine ⟨17541144501889136486828327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11694096334592757657885551 17541144501889136486828327)
      ·
        refine ⟨26311716752833704730242491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17541144501889136486828327 26311716752833704730242491)
        ·
          refine ⟨39467575129250557095363737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26311716752833704730242491 39467575129250557095363737)
          ·
            refine ⟨29600681346937917821522803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39467575129250557095363737 29600681346937917821522803)
            ·
              refine ⟨44401022020406876732284205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29600681346937917821522803 44401022020406876732284205)
              ·
                refine ⟨16650383257652578774606577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44401022020406876732284205 16650383257652578774606577)
                ·
                  refine ⟨12487787443239434080954933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16650383257652578774606577 12487787443239434080954933)
                  ·
                    refine ⟨1170730072803696945089525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12487787443239434080954933 1170730072803696945089525)
                    ·
                      rfl

theorem cell23_6839966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_6839966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6839966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6839966 prefixEnd_6839966 := by exact prefixLift 6839966
  have htrace : WordTrace (prefixWord ++ tailWord_6839966) baseStart_6839966 baseEnd_6839966 := by
    simpa [prefixWord, tailWord_6839966, baseEnd_6839966] using wordTrace_append hprefix tailTrace_6839966
  have hstable : (prefixWord ++ tailWord_6839966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6839966).length < 2 ^ (prefixWord ++ tailWord_6839966).sum := by decide
  have hdescent : baseEnd_6839966 < baseStart_6839966 := by decide
  rcases family_descends (prefixWord ++ tailWord_6839966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6839992 : List Nat := [2, 1, 2, 1, 2, 1, 1, 5, 8]
def baseStart_6839992 : Nat := 118140960795 + 6839992 * 2 ^ 59
def prefixEnd_6839992 : Nat := 4983230072969 + 3 ^ 40 * 6839992 * 2
def baseEnd_6839992 : Nat := 390244840989789748171495

theorem tailTrace_6839992 : CollatzResearch.WordTrace tailWord_6839992 prefixEnd_6839992 390244840989789748171495 := by
  unfold tailWord_6839992
  simp only [CollatzResearch.WordTrace]
  refine ⟨124737501717942318237669115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166316668957256424316892153 124737501717942318237669115)
  ·
    refine ⟨187106252576913477356503673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124737501717942318237669115 187106252576913477356503673)
    ·
      refine ⟨140329689432685108017377755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187106252576913477356503673 140329689432685108017377755)
      ·
        refine ⟨210494534149027662026066633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140329689432685108017377755 210494534149027662026066633)
        ·
          refine ⟨157870900611770746519549975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210494534149027662026066633 157870900611770746519549975)
          ·
            refine ⟨236806350917656119779324963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157870900611770746519549975 236806350917656119779324963)
            ·
              refine ⟨355209526376484179668987445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 236806350917656119779324963 355209526376484179668987445)
              ·
                refine ⟨33300893097795391843967573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 355209526376484179668987445 33300893097795391843967573)
                ·
                  refine ⟨390244840989789748171495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33300893097795391843967573 390244840989789748171495)
                  ·
                    rfl

theorem cell23_6839992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 5, 8].length) (baseStart_6839992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6839992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6839992 prefixEnd_6839992 := by exact prefixLift 6839992
  have htrace : WordTrace (prefixWord ++ tailWord_6839992) baseStart_6839992 baseEnd_6839992 := by
    simpa [prefixWord, tailWord_6839992, baseEnd_6839992] using wordTrace_append hprefix tailTrace_6839992
  have hstable : (prefixWord ++ tailWord_6839992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6839992).length < 2 ^ (prefixWord ++ tailWord_6839992).sum := by decide
  have hdescent : baseEnd_6839992 < baseStart_6839992 := by decide
  rcases family_descends (prefixWord ++ tailWord_6839992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6840013 : List Nat := [1, 6, 2, 1, 1, 1, 1, 1, 5, 4]
def baseStart_6840013 : Nat := 118140960795 + 6840013 * 2 ^ 59
def prefixEnd_6840013 : Nat := 4983230072969 + 3 ^ 40 * 6840013 * 2
def baseEnd_6840013 : Nat := 1170738117333950717126953

theorem tailTrace_6840013 : CollatzResearch.WordTrace tailWord_6840013 prefixEnd_6840013 1170738117333950717126953 := by
  unfold tailWord_6840013
  simp only [CollatzResearch.WordTrace]
  refine ⟨249475769368808557061852693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166317179579205704707901795 249475769368808557061852693)
  ·
    refine ⟨11694176689162901112274345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 249475769368808557061852693 11694176689162901112274345)
    ·
      refine ⟨8770632516872175834205759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11694176689162901112274345 8770632516872175834205759)
      ·
        refine ⟨13155948775308263751308639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8770632516872175834205759 13155948775308263751308639)
        ·
          refine ⟨19733923162962395626962959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13155948775308263751308639 19733923162962395626962959)
          ·
            refine ⟨29600884744443593440444439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19733923162962395626962959 29600884744443593440444439)
            ·
              refine ⟨44401327116665390160666659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29600884744443593440444439 44401327116665390160666659)
              ·
                refine ⟨66601990674998085240999989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44401327116665390160666659 66601990674998085240999989)
                ·
                  refine ⟨6243936625781070491343749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66601990674998085240999989 6243936625781070491343749)
                  ·
                    refine ⟨1170738117333950717126953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6243936625781070491343749 1170738117333950717126953)
                    ·
                      rfl

theorem cell23_6840013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_6840013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6840013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6840013 prefixEnd_6840013 := by exact prefixLift 6840013
  have htrace : WordTrace (prefixWord ++ tailWord_6840013) baseStart_6840013 baseEnd_6840013 := by
    simpa [prefixWord, tailWord_6840013, baseEnd_6840013] using wordTrace_append hprefix tailTrace_6840013
  have hstable : (prefixWord ++ tailWord_6840013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6840013).length < 2 ^ (prefixWord ++ tailWord_6840013).sum := by decide
  have hdescent : baseEnd_6840013 < baseStart_6840013 := by decide
  rcases family_descends (prefixWord ++ tailWord_6840013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6840036 : List Nat := [2, 3, 1, 1, 1, 3, 1, 2, 5, 1, 3]
def baseStart_6840036 : Nat := 118140960795 + 6840036 * 2 ^ 59
def prefixEnd_6840036 : Nat := 4983230072969 + 3 ^ 40 * 6840036 * 2
def baseEnd_6840036 : Nat := 3512226162056905561393253

theorem tailTrace_6840036 : CollatzResearch.WordTrace tailWord_6840036 prefixEnd_6840036 3512226162056905561393253 := by
  unfold tailWord_6840036
  simp only [CollatzResearch.WordTrace]
  refine ⟨124738304123862615994969981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166317738831816821326626641 124738304123862615994969981)
  ·
    refine ⟨46776864046448480998113743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124738304123862615994969981 46776864046448480998113743)
    ·
      refine ⟨70165296069672721497170615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46776864046448480998113743 70165296069672721497170615)
      ·
        refine ⟨105247944104509082245755923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70165296069672721497170615 105247944104509082245755923)
        ·
          refine ⟨157871916156763623368633885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105247944104509082245755923 157871916156763623368633885)
          ·
            refine ⟨59201968558786358763237707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157871916156763623368633885 59201968558786358763237707)
            ·
              refine ⟨88802952838179538144856561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59201968558786358763237707 88802952838179538144856561)
              ·
                refine ⟨66602214628634653608642421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88802952838179538144856561 66602214628634653608642421)
                ·
                  refine ⟨6243957621434498775810227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66602214628634653608642421 6243957621434498775810227)
                  ·
                    refine ⟨9365936432151748163715341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6243957621434498775810227 9365936432151748163715341)
                    ·
                      refine ⟨3512226162056905561393253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9365936432151748163715341 3512226162056905561393253)
                      ·
                        rfl

theorem cell23_6840036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 5, 1, 3].length) (baseStart_6840036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6840036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6840036 prefixEnd_6840036 := by exact prefixLift 6840036
  have htrace : WordTrace (prefixWord ++ tailWord_6840036) baseStart_6840036 baseEnd_6840036 := by
    simpa [prefixWord, tailWord_6840036, baseEnd_6840036] using wordTrace_append hprefix tailTrace_6840036
  have hstable : (prefixWord ++ tailWord_6840036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6840036).length < 2 ^ (prefixWord ++ tailWord_6840036).sum := by decide
  have hdescent : baseEnd_6840036 < baseStart_6840036 := by decide
  rcases family_descends (prefixWord ++ tailWord_6840036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6840059 : List Nat := [1, 1, 1, 1, 1, 3, 1, 6, 3, 1, 4]
def baseStart_6840059 : Nat := 118140960795 + 6840059 * 2 ^ 59
def prefixEnd_6840059 : Nat := 4983230072969 + 3 ^ 40 * 6840059 * 2
def baseEnd_6840059 : Nat := 3512237972111958971405647

theorem tailTrace_6840059 : CollatzResearch.WordTrace tailWord_6840059 prefixEnd_6840059 3512237972111958971405647 := by
  unfold tailWord_6840059
  simp only [CollatzResearch.WordTrace]
  refine ⟨249477447126641906918027231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166318298084427937945351487 249477447126641906918027231)
  ·
    refine ⟨374216170689962860377040847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249477447126641906918027231 374216170689962860377040847)
    ·
      refine ⟨561324256034944290565561271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374216170689962860377040847 561324256034944290565561271)
      ·
        refine ⟨841986384052416435848341907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 561324256034944290565561271 841986384052416435848341907)
        ·
          refine ⟨1262979576078624653772512861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 841986384052416435848341907 1262979576078624653772512861)
          ·
            refine ⟨473617341029484245164692323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1262979576078624653772512861 473617341029484245164692323)
            ·
              refine ⟨710426011544226367747038485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 473617341029484245164692323 710426011544226367747038485)
              ·
                refine ⟨33301219291135610988142429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 710426011544226367747038485 33301219291135610988142429)
                ·
                  refine ⟨12487957234175854120553411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33301219291135610988142429 12487957234175854120553411)
                  ·
                    refine ⟨18731935851263781180830117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12487957234175854120553411 18731935851263781180830117)
                    ·
                      refine ⟨3512237972111958971405647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18731935851263781180830117 3512237972111958971405647)
                      ·
                        rfl

theorem cell23_6840059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 3, 1, 4].length) (baseStart_6840059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6840059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6840059 prefixEnd_6840059 := by exact prefixLift 6840059
  have htrace : WordTrace (prefixWord ++ tailWord_6840059) baseStart_6840059 baseEnd_6840059 := by
    simpa [prefixWord, tailWord_6840059, baseEnd_6840059] using wordTrace_append hprefix tailTrace_6840059
  have hstable : (prefixWord ++ tailWord_6840059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6840059).length < 2 ^ (prefixWord ++ tailWord_6840059).sum := by decide
  have hdescent : baseEnd_6840059 < baseStart_6840059 := by decide
  rcases family_descends (prefixWord ++ tailWord_6840059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6840076 : List Nat := [2, 2, 1, 2, 2, 1, 3, 4, 1, 1, 4]
def baseStart_6840076 : Nat := 118140960795 + 6840076 * 2 ^ 59
def prefixEnd_6840076 : Nat := 4983230072969 + 3 ^ 40 * 6840076 * 2
def baseEnd_6840076 : Nat := 3512246701283085404893069

theorem tailTrace_6840076 : CollatzResearch.WordTrace tailWord_6840076 prefixEnd_6840076 3512246701283085404893069 := by
  unfold tailWord_6840076
  simp only [CollatzResearch.WordTrace]
  refine ⟨124739033583790159410698041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166318711445053545880930721 124739033583790159410698041)
  ·
    refine ⟨93554275187842619558023531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124739033583790159410698041 93554275187842619558023531)
    ·
      refine ⟨140331412781763929337035297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93554275187842619558023531 140331412781763929337035297)
      ·
        refine ⟨105248559586322947002776473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140331412781763929337035297 105248559586322947002776473)
        ·
          refine ⟨78936419689742210252082355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105248559586322947002776473 78936419689742210252082355)
          ·
            refine ⟨118404629534613315378123533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78936419689742210252082355 118404629534613315378123533)
            ·
              refine ⟨44401736075479993266796325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118404629534613315378123533 44401736075479993266796325)
              ·
                refine ⟨8325325514152498737524311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44401736075479993266796325 8325325514152498737524311)
                ·
                  refine ⟨12487988271228748106286467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8325325514152498737524311 12487988271228748106286467)
                  ·
                    refine ⟨18731982406843122159429701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12487988271228748106286467 18731982406843122159429701)
                    ·
                      refine ⟨3512246701283085404893069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18731982406843122159429701 3512246701283085404893069)
                      ·
                        rfl

theorem cell23_6840076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 4, 1, 1, 4].length) (baseStart_6840076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6840076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6840076 prefixEnd_6840076 := by exact prefixLift 6840076
  have htrace : WordTrace (prefixWord ++ tailWord_6840076) baseStart_6840076 baseEnd_6840076 := by
    simpa [prefixWord, tailWord_6840076, baseEnd_6840076] using wordTrace_append hprefix tailTrace_6840076
  have hstable : (prefixWord ++ tailWord_6840076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6840076).length < 2 ^ (prefixWord ++ tailWord_6840076).sum := by decide
  have hdescent : baseEnd_6840076 < baseStart_6840076 := by decide
  rcases family_descends (prefixWord ++ tailWord_6840076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6840087 : List Nat := [1, 1, 3, 4, 2, 3, 1, 3, 1, 1, 3]
def baseStart_6840087 : Nat := 118140960795 + 6840087 * 2 ^ 59
def prefixEnd_6840087 : Nat := 4983230072969 + 3 ^ 40 * 6840087 * 2
def baseEnd_6840087 : Nat := 3512252349570284861855519

theorem tailTrace_6840087 : CollatzResearch.WordTrace tailWord_6840087 prefixEnd_6840087 3512252349570284861855519 := by
  unfold tailWord_6840087
  simp only [CollatzResearch.WordTrace]
  refine ⟨249478468370540467700046515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166318978913693645133364343 249478468370540467700046515)
  ·
    refine ⟨374217702555810701550069773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249478468370540467700046515 374217702555810701550069773)
    ·
      refine ⟨140331638458429013081276165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 374217702555810701550069773 140331638458429013081276165)
      ·
        refine ⟨26312182210955439952739281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140331638458429013081276165 26312182210955439952739281)
        ·
          refine ⟨19734136658216579964554461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26312182210955439952739281 19734136658216579964554461)
          ·
            refine ⟨7400301246831217486707923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19734136658216579964554461 7400301246831217486707923)
            ·
              refine ⟨11100451870246826230061885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7400301246831217486707923 11100451870246826230061885)
              ·
                refine ⟨4162669451342559836273207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11100451870246826230061885 4162669451342559836273207)
                ·
                  refine ⟨6244004177013839754409811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4162669451342559836273207 6244004177013839754409811)
                  ·
                    refine ⟨9366006265520759631614717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6244004177013839754409811 9366006265520759631614717)
                    ·
                      refine ⟨3512252349570284861855519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9366006265520759631614717 3512252349570284861855519)
                      ·
                        rfl

theorem cell23_6840087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 3, 1, 1, 3].length) (baseStart_6840087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6840087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6840087 prefixEnd_6840087 := by exact prefixLift 6840087
  have htrace : WordTrace (prefixWord ++ tailWord_6840087) baseStart_6840087 baseEnd_6840087 := by
    simpa [prefixWord, tailWord_6840087, baseEnd_6840087] using wordTrace_append hprefix tailTrace_6840087
  have hstable : (prefixWord ++ tailWord_6840087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6840087).length < 2 ^ (prefixWord ++ tailWord_6840087).sum := by decide
  have hdescent : baseEnd_6840087 < baseStart_6840087 := by decide
  rcases family_descends (prefixWord ++ tailWord_6840087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6840096 : List Nat := [2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 5]
def baseStart_6840096 : Nat := 118140960795 + 6840096 * 2 ^ 59
def prefixEnd_6840096 : Nat := 4983230072969 + 3 ^ 40 * 6840096 * 2
def baseEnd_6840096 : Nat := 3512256970896175326642977

theorem tailTrace_6840096 : CollatzResearch.WordTrace tailWord_6840096 prefixEnd_6840096 3512256970896175326642977 := by
  unfold tailWord_6840096
  simp only [CollatzResearch.WordTrace]
  refine ⟨124739398313753931118562071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166319197751671908158082761 124739398313753931118562071)
  ·
    refine ⟨187109097470630896677843107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124739398313753931118562071 187109097470630896677843107)
    ·
      refine ⟨280663646205946345016764661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187109097470630896677843107 280663646205946345016764661)
      ·
        refine ⟨26312216831807469845321687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 280663646205946345016764661 26312216831807469845321687)
        ·
          refine ⟨39468325247711204767982531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26312216831807469845321687 39468325247711204767982531)
          ·
            refine ⟨59202487871566807151973797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39468325247711204767982531 59202487871566807151973797)
            ·
              refine ⟨11100466475918776340995087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59202487871566807151973797 11100466475918776340995087)
              ·
                refine ⟨16650699713878164511492631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11100466475918776340995087 16650699713878164511492631)
                ·
                  refine ⟨24976049570817246767238947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16650699713878164511492631 24976049570817246767238947)
                  ·
                    refine ⟨37464074356225870150858421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24976049570817246767238947 37464074356225870150858421)
                    ·
                      refine ⟨3512256970896175326642977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37464074356225870150858421 3512256970896175326642977)
                      ·
                        rfl

theorem cell23_6840096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_6840096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6840096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6840096 prefixEnd_6840096 := by exact prefixLift 6840096
  have htrace : WordTrace (prefixWord ++ tailWord_6840096) baseStart_6840096 baseEnd_6840096 := by
    simpa [prefixWord, tailWord_6840096, baseEnd_6840096] using wordTrace_append hprefix tailTrace_6840096
  have hstable : (prefixWord ++ tailWord_6840096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6840096).length < 2 ^ (prefixWord ++ tailWord_6840096).sum := by decide
  have hdescent : baseEnd_6840096 < baseStart_6840096 := by decide
  rcases family_descends (prefixWord ++ tailWord_6840096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6840116 : List Nat := [2, 5, 1, 1, 2, 1, 1, 10]
def baseStart_6840116 : Nat := 118140960795 + 6840116 * 2 ^ 59
def prefixEnd_6840116 : Nat := 4983230072969 + 3 ^ 40 * 6840116 * 2
def baseEnd_6840116 : Nat := 130083971870713527718255

theorem tailTrace_6840116 : CollatzResearch.WordTrace tailWord_6840116 prefixEnd_6840116 130083971870713527718255 := by
  unfold tailWord_6840116
  simp only [CollatzResearch.WordTrace]
  refine ⟨124739763043717702826426101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166319684058290270435234801 124739763043717702826426101)
  ·
    refine ⟨11694352785348534639977447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 124739763043717702826426101 11694352785348534639977447)
    ·
      refine ⟨17541529178022801959966171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11694352785348534639977447 17541529178022801959966171)
      ·
        refine ⟨26312293767034202939949257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17541529178022801959966171 26312293767034202939949257)
        ·
          refine ⟨19734220325275652204961943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26312293767034202939949257 19734220325275652204961943)
          ·
            refine ⟨29601330487913478307442915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19734220325275652204961943 29601330487913478307442915)
            ·
              refine ⟨44401995731870217461164373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29601330487913478307442915 44401995731870217461164373)
              ·
                refine ⟨130083971870713527718255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 44401995731870217461164373 130083971870713527718255)
                ·
                  rfl

theorem cell23_6840116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 10].length) (baseStart_6840116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6840116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6840116 prefixEnd_6840116 := by exact prefixLift 6840116
  have htrace : WordTrace (prefixWord ++ tailWord_6840116) baseStart_6840116 baseEnd_6840116 := by
    simpa [prefixWord, tailWord_6840116, baseEnd_6840116] using wordTrace_append hprefix tailTrace_6840116
  have hstable : (prefixWord ++ tailWord_6840116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6840116).length < 2 ^ (prefixWord ++ tailWord_6840116).sum := by decide
  have hdescent : baseEnd_6840116 < baseStart_6840116 := by decide
  rcases family_descends (prefixWord ++ tailWord_6840116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6840120 : List Nat := [2, 1, 2, 1, 3, 5, 2, 1, 2, 4]
def baseStart_6840120 : Nat := 118140960795 + 6840120 * 2 ^ 59
def prefixEnd_6840120 : Nat := 4983230072969 + 3 ^ 40 * 6840120 * 2
def baseEnd_6840120 : Nat := 1170756431477294410914289

theorem tailTrace_6840120 : CollatzResearch.WordTrace tailWord_6840120 prefixEnd_6840120 1170756431477294410914289 := by
  unfold tailWord_6840120
  simp only [CollatzResearch.WordTrace]
  refine ⟨124739835989710457167998907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166319781319613942890665209 124739835989710457167998907)
  ·
    refine ⟨187109753984565685751998361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124739835989710457167998907 187109753984565685751998361)
    ·
      refine ⟨140332315488424264313998771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187109753984565685751998361 140332315488424264313998771)
      ·
        refine ⟨210498473232636396470998157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140332315488424264313998771 210498473232636396470998157)
        ·
          refine ⟨78936927462238648676624309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 210498473232636396470998157 78936927462238648676624309)
          ·
            refine ⟨7400336949584873313433529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 78936927462238648676624309 7400336949584873313433529)
            ·
              refine ⟨5550252712188654985075147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7400336949584873313433529 5550252712188654985075147)
              ·
                refine ⟨8325379068282982477612721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5550252712188654985075147 8325379068282982477612721)
                ·
                  refine ⟨6244034301212236858209541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8325379068282982477612721 6244034301212236858209541)
                  ·
                    refine ⟨1170756431477294410914289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6244034301212236858209541 1170756431477294410914289)
                    ·
                      rfl

theorem cell23_6840120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 2, 1, 2, 4].length) (baseStart_6840120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6840120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6840120 prefixEnd_6840120 := by exact prefixLift 6840120
  have htrace : WordTrace (prefixWord ++ tailWord_6840120) baseStart_6840120 baseEnd_6840120 := by
    simpa [prefixWord, tailWord_6840120, baseEnd_6840120] using wordTrace_append hprefix tailTrace_6840120
  have hstable : (prefixWord ++ tailWord_6840120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6840120).length < 2 ^ (prefixWord ++ tailWord_6840120).sum := by decide
  have hdescent : baseEnd_6840120 < baseStart_6840120 := by decide
  rcases family_descends (prefixWord ++ tailWord_6840120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6840160 : List Nat := [2, 1, 1, 3, 3, 3, 2, 2, 2, 1, 3]
def baseStart_6840160 : Nat := 118140960795 + 6840160 * 2 ^ 59
def prefixEnd_6840160 : Nat := 4983230072969 + 3 ^ 40 * 6840160 * 2
def baseEnd_6840160 : Nat := 3512289833658063076242683

theorem tailTrace_6840160 : CollatzResearch.WordTrace tailWord_6840160 prefixEnd_6840160 3512289833658063076242683 := by
  unfold tailWord_6840160
  simp only [CollatzResearch.WordTrace]
  refine ⟨124740565449638000583726967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166320753932850667444969289 124740565449638000583726967)
  ·
    refine ⟨187110848174457000875590451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124740565449638000583726967 187110848174457000875590451)
    ·
      refine ⟨280666272261685501313385677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187110848174457000875590451 280666272261685501313385677)
      ·
        refine ⟨105249852098132062992519629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 280666272261685501313385677 105249852098132062992519629)
        ·
          refine ⟨39468694536799523622194861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105249852098132062992519629 39468694536799523622194861)
          ·
            refine ⟨14800760451299821358323073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39468694536799523622194861 14800760451299821358323073)
            ·
              refine ⟨11100570338474866018742305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14800760451299821358323073 11100570338474866018742305)
              ·
                refine ⟨8325427753856149514056729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11100570338474866018742305 8325427753856149514056729)
                ·
                  refine ⟨6244070815392112135542547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8325427753856149514056729 6244070815392112135542547)
                  ·
                    refine ⟨9366106223088168203313821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6244070815392112135542547 9366106223088168203313821)
                    ·
                      refine ⟨3512289833658063076242683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9366106223088168203313821 3512289833658063076242683)
                      ·
                        rfl

theorem cell23_6840160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 2, 2, 1, 3].length) (baseStart_6840160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6840160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6840160 prefixEnd_6840160 := by exact prefixLift 6840160
  have htrace : WordTrace (prefixWord ++ tailWord_6840160) baseStart_6840160 baseEnd_6840160 := by
    simpa [prefixWord, tailWord_6840160, baseEnd_6840160] using wordTrace_append hprefix tailTrace_6840160
  have hstable : (prefixWord ++ tailWord_6840160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6840160).length < 2 ^ (prefixWord ++ tailWord_6840160).sum := by decide
  have hdescent : baseEnd_6840160 < baseStart_6840160 := by decide
  rcases family_descends (prefixWord ++ tailWord_6840160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6840169 : List Nat := [1, 2, 1, 1, 1, 3, 1, 4, 1, 3, 5]
def baseStart_6840169 : Nat := 118140960795 + 6840169 * 2 ^ 59
def prefixEnd_6840169 : Nat := 4983230072969 + 3 ^ 40 * 6840169 * 2
def baseEnd_6840169 : Nat := 3512294454983953541030141

theorem tailTrace_6840169 : CollatzResearch.WordTrace tailWord_6840169 prefixEnd_6840169 3512294454983953541030141 := by
  unfold tailWord_6840169
  simp only [CollatzResearch.WordTrace]
  refine ⟨249481459156243395704531561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166320972770828930469687707 249481459156243395704531561)
  ·
    refine ⟨187111094367182546778398671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249481459156243395704531561 187111094367182546778398671)
    ·
      refine ⟨280666641550773820167598007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187111094367182546778398671 280666641550773820167598007)
      ·
        refine ⟨420999962326160730251397011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280666641550773820167598007 420999962326160730251397011)
        ·
          refine ⟨631499943489241095377095517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 420999962326160730251397011 631499943489241095377095517)
          ·
            refine ⟨236812478808465410766410819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 631499943489241095377095517 236812478808465410766410819)
            ·
              refine ⟨355218718212698116149616229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 236812478808465410766410819 355218718212698116149616229)
              ·
                refine ⟨66603509664880896778053043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 355218718212698116149616229 66603509664880896778053043)
                ·
                  refine ⟨99905264497321345167079565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66603509664880896778053043 99905264497321345167079565)
                  ·
                    refine ⟨37464474186495504437654837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 99905264497321345167079565 37464474186495504437654837)
                    ·
                      refine ⟨3512294454983953541030141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37464474186495504437654837 3512294454983953541030141)
                      ·
                        rfl

theorem cell23_6840169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 3, 5].length) (baseStart_6840169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6840169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6840169 prefixEnd_6840169 := by exact prefixLift 6840169
  have htrace : WordTrace (prefixWord ++ tailWord_6840169) baseStart_6840169 baseEnd_6840169 := by
    simpa [prefixWord, tailWord_6840169, baseEnd_6840169] using wordTrace_append hprefix tailTrace_6840169
  have hstable : (prefixWord ++ tailWord_6840169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6840169).length < 2 ^ (prefixWord ++ tailWord_6840169).sum := by decide
  have hdescent : baseEnd_6840169 < baseStart_6840169 := by decide
  rcases family_descends (prefixWord ++ tailWord_6840169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6840183 : List Nat := [1, 1, 3, 1, 1, 2, 1, 1, 8, 2, 2]
def baseStart_6840183 : Nat := 118140960795 + 6840183 * 2 ^ 59
def prefixEnd_6840183 : Nat := 4983230072969 + 3 ^ 40 * 6840183 * 2
def baseEnd_6840183 : Nat := 3512301643713116486255077

theorem tailTrace_6840183 : CollatzResearch.WordTrace tailWord_6840183 prefixEnd_6840183 3512301643713116486255077 := by
  unfold tailWord_6840183
  simp only [CollatzResearch.WordTrace]
  refine ⟨249481969778192676095541203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166321313185461784063694135 249481969778192676095541203)
  ·
    refine ⟨374222954667289014143311805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249481969778192676095541203 374222954667289014143311805)
    ·
      refine ⟨140333608000233380303741927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 374222954667289014143311805 140333608000233380303741927)
      ·
        refine ⟨210500412000350070455612891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140333608000233380303741927 210500412000350070455612891)
        ·
          refine ⟨315750618000525105683419337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210500412000350070455612891 315750618000525105683419337)
          ·
            refine ⟨236812963500393829262564503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 315750618000525105683419337 236812963500393829262564503)
            ·
              refine ⟨355219445250590743893846755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 236812963500393829262564503 355219445250590743893846755)
              ·
                refine ⟨532829167875886115840770133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 355219445250590743893846755 532829167875886115840770133)
                ·
                  refine ⟨6244091811045540420009025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 532829167875886115840770133 6244091811045540420009025)
                  ·
                    refine ⟨4683068858284155315006769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6244091811045540420009025 4683068858284155315006769)
                    ·
                      refine ⟨3512301643713116486255077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4683068858284155315006769 3512301643713116486255077)
                      ·
                        rfl

theorem cell23_6840183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 8, 2, 2].length) (baseStart_6840183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6840183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6840183 prefixEnd_6840183 := by exact prefixLift 6840183
  have htrace : WordTrace (prefixWord ++ tailWord_6840183) baseStart_6840183 baseEnd_6840183 := by
    simpa [prefixWord, tailWord_6840183, baseEnd_6840183] using wordTrace_append hprefix tailTrace_6840183
  have hstable : (prefixWord ++ tailWord_6840183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6840183).length < 2 ^ (prefixWord ++ tailWord_6840183).sum := by decide
  have hdescent : baseEnd_6840183 < baseStart_6840183 := by decide
  rcases family_descends (prefixWord ++ tailWord_6840183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6840223 : List Nat := [1, 1, 2, 5, 3, 1, 2, 1, 7]
def baseStart_6840223 : Nat := 118140960795 + 6840223 * 2 ^ 59
def prefixEnd_6840223 : Nat := 4983230072969 + 3 ^ 40 * 6840223 * 2
def baseEnd_6840223 : Nat := 390258020326588481083877

theorem tailTrace_6840223 : CollatzResearch.WordTrace tailWord_6840223 prefixEnd_6840223 390258020326588481083877 := by
  unfold tailWord_6840223
  simp only [CollatzResearch.WordTrace]
  refine ⟨249483428698047762926997323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166322285798698508617998215 249483428698047762926997323)
  ·
    refine ⟨374225143047071644390495985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249483428698047762926997323 374225143047071644390495985)
    ·
      refine ⟨280668857285303733292871989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 374225143047071644390495985 280668857285303733292871989)
      ·
        refine ⟨26312705370497224996206749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 280668857285303733292871989 26312705370497224996206749)
        ·
          refine ⟨9867264513936459373577531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26312705370497224996206749 9867264513936459373577531)
          ·
            refine ⟨14800896770904689060366297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9867264513936459373577531 14800896770904689060366297)
            ·
              refine ⟨11100672578178516795274723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14800896770904689060366297 11100672578178516795274723)
              ·
                refine ⟨16651008867267775192912085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11100672578178516795274723 16651008867267775192912085)
                ·
                  refine ⟨390258020326588481083877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16651008867267775192912085 390258020326588481083877)
                  ·
                    rfl

theorem cell23_6840223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 1, 7].length) (baseStart_6840223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6840223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6840223 prefixEnd_6840223 := by exact prefixLift 6840223
  have htrace : WordTrace (prefixWord ++ tailWord_6840223) baseStart_6840223 baseEnd_6840223 := by
    simpa [prefixWord, tailWord_6840223, baseEnd_6840223] using wordTrace_append hprefix tailTrace_6840223
  have hstable : (prefixWord ++ tailWord_6840223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6840223).length < 2 ^ (prefixWord ++ tailWord_6840223).sum := by decide
  have hdescent : baseEnd_6840223 < baseStart_6840223 := by decide
  rcases family_descends (prefixWord ++ tailWord_6840223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6840256 : List Nat := [2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 4]
def baseStart_6840256 : Nat := 118140960795 + 6840256 * 2 ^ 59
def prefixEnd_6840256 : Nat := 4983230072969 + 3 ^ 40 * 6840256 * 2
def baseEnd_6840256 : Nat := 3512339127800894700642241

theorem tailTrace_6840256 : CollatzResearch.WordTrace tailWord_6840256 prefixEnd_6840256 3512339127800894700642241 := by
  unfold tailWord_6840256
  simp only [CollatzResearch.WordTrace]
  refine ⟨124742316153464104781474311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166323088204618806375299081 124742316153464104781474311)
  ·
    refine ⟨187113474230196157172211467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124742316153464104781474311 187113474230196157172211467)
    ·
      refine ⟨280670211345294235758317201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187113474230196157172211467 280670211345294235758317201)
      ·
        refine ⟨210502658508970676818737901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280670211345294235758317201 210502658508970676818737901)
        ·
          refine ⟨78938496940864003807026713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 210502658508970676818737901 78938496940864003807026713)
          ·
            refine ⟨59203872705648002855270035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78938496940864003807026713 59203872705648002855270035)
            ·
              refine ⟨88805809058472004282905053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59203872705648002855270035 88805809058472004282905053)
              ·
                refine ⟨33302178396927001606089395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88805809058472004282905053 33302178396927001606089395)
                ·
                  refine ⟨49953267595390502409134093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33302178396927001606089395 49953267595390502409134093)
                  ·
                    refine ⟨18732475348271438403425285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49953267595390502409134093 18732475348271438403425285)
                    ·
                      refine ⟨3512339127800894700642241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18732475348271438403425285 3512339127800894700642241)
                      ·
                        rfl

theorem cell23_6840256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 4].length) (baseStart_6840256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6840256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6840256 prefixEnd_6840256 := by exact prefixLift 6840256
  have htrace : WordTrace (prefixWord ++ tailWord_6840256) baseStart_6840256 baseEnd_6840256 := by
    simpa [prefixWord, tailWord_6840256, baseEnd_6840256] using wordTrace_append hprefix tailTrace_6840256
  have hstable : (prefixWord ++ tailWord_6840256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6840256).length < 2 ^ (prefixWord ++ tailWord_6840256).sum := by decide
  have hdescent : baseEnd_6840256 < baseStart_6840256 := by decide
  rcases family_descends (prefixWord ++ tailWord_6840256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6840273 : List Nat := [1, 2, 2, 1, 2, 1, 2, 4, 2, 4, 2]
def baseStart_6840273 : Nat := 118140960795 + 6840273 * 2 ^ 59
def prefixEnd_6840273 : Nat := 4983230072969 + 3 ^ 40 * 6840273 * 2
def baseEnd_6840273 : Nat := 3512347856972021134129663

theorem tailTrace_6840273 : CollatzResearch.WordTrace tailWord_6840273 prefixEnd_6840273 3512347856972021134129663 := by
  unfold tailWord_6840273
  simp only [CollatzResearch.WordTrace]
  refine ⟨249485252347866621466317473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166323501565244414310878315 249485252347866621466317473)
  ·
    refine ⟨187113939260899966099738105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249485252347866621466317473 187113939260899966099738105)
    ·
      refine ⟨140335454445674974574803579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187113939260899966099738105 140335454445674974574803579)
      ·
        refine ⟨210503181668512461862205369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140335454445674974574803579 210503181668512461862205369)
        ·
          refine ⟨157877386251384346396654027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210503181668512461862205369 157877386251384346396654027)
          ·
            refine ⟨236816079377076519594981041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157877386251384346396654027 236816079377076519594981041)
            ·
              refine ⟨177612059532807389696235781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 236816079377076519594981041 177612059532807389696235781)
              ·
                refine ⟨33302261162401385568044209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 177612059532807389696235781 33302261162401385568044209)
                ·
                  refine ⟨24976695871801039176033157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33302261162401385568044209 24976695871801039176033157)
                  ·
                    refine ⟨4683130475962694845506217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24976695871801039176033157 4683130475962694845506217)
                    ·
                      refine ⟨3512347856972021134129663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4683130475962694845506217 3512347856972021134129663)
                      ·
                        rfl

theorem cell23_6840273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 4, 2, 4, 2].length) (baseStart_6840273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6840273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6840273 prefixEnd_6840273 := by exact prefixLift 6840273
  have htrace : WordTrace (prefixWord ++ tailWord_6840273) baseStart_6840273 baseEnd_6840273 := by
    simpa [prefixWord, tailWord_6840273, baseEnd_6840273] using wordTrace_append hprefix tailTrace_6840273
  have hstable : (prefixWord ++ tailWord_6840273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6840273).length < 2 ^ (prefixWord ++ tailWord_6840273).sum := by decide
  have hdescent : baseEnd_6840273 < baseStart_6840273 := by decide
  rcases family_descends (prefixWord ++ tailWord_6840273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6840330 : List Nat := [3, 1, 2, 2, 4, 1, 2, 2, 6]
def baseStart_6840330 : Nat := 118140960795 + 6840330 * 2 ^ 59
def prefixEnd_6840330 : Nat := 4983230072969 + 3 ^ 40 * 6840330 * 2
def baseEnd_6840330 : Nat := 390264125041036379012989

theorem tailTrace_6840330 : CollatzResearch.WordTrace tailWord_6840330 prefixEnd_6840330 390264125041036379012989 := by
  unfold tailWord_6840330
  simp only [CollatzResearch.WordTrace]
  refine ⟨62371832827165030050285611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166324887539106746800761629 62371832827165030050285611)
  ·
    refine ⟨93557749240747545075428417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62371832827165030050285611 93557749240747545075428417)
    ·
      refine ⟨70168311930560658806571313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93557749240747545075428417 70168311930560658806571313)
      ·
        refine ⟨52626233947920494104928485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70168311930560658806571313 52626233947920494104928485)
        ·
          refine ⟨9867418865235092644674091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52626233947920494104928485 9867418865235092644674091)
          ·
            refine ⟨14801128297852638967011137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9867418865235092644674091 14801128297852638967011137)
            ·
              refine ⟨11100846223389479225258353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14801128297852638967011137 11100846223389479225258353)
              ·
                refine ⟨8325634667542109418943765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11100846223389479225258353 8325634667542109418943765)
                ·
                  refine ⟨390264125041036379012989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8325634667542109418943765 390264125041036379012989)
                  ·
                    rfl

theorem cell23_6840330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 2, 6].length) (baseStart_6840330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6840330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6840330 prefixEnd_6840330 := by exact prefixLift 6840330
  have htrace : WordTrace (prefixWord ++ tailWord_6840330) baseStart_6840330 baseEnd_6840330 := by
    simpa [prefixWord, tailWord_6840330, baseEnd_6840330] using wordTrace_append hprefix tailTrace_6840330
  have hstable : (prefixWord ++ tailWord_6840330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6840330).length < 2 ^ (prefixWord ++ tailWord_6840330).sum := by decide
  have hdescent : baseEnd_6840330 < baseStart_6840330 := by decide
  rcases family_descends (prefixWord ++ tailWord_6840330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6840363 : List Nat := [1, 1, 1, 1, 2, 1, 4, 1, 1, 8, 2]
def baseStart_6840363 : Nat := 118140960795 + 6840363 * 2 ^ 59
def prefixEnd_6840363 : Nat := 4983230072969 + 3 ^ 40 * 6840363 * 2
def baseEnd_6840363 : Nat := 3512394070230925782004249

theorem tailTrace_6840363 : CollatzResearch.WordTrace tailWord_6840363 prefixEnd_6840363 3512394070230925782004249 := by
  unfold tailWord_6840363
  simp only [CollatzResearch.WordTrace]
  refine ⟨249488534917540566837093743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166325689945027044558062495 249488534917540566837093743)
  ·
    refine ⟨374232802376310850255640615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249488534917540566837093743 374232802376310850255640615)
    ·
      refine ⟨561349203564466275383460923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374232802376310850255640615 561349203564466275383460923)
      ·
        refine ⟨842023805346699413075191385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 561349203564466275383460923 842023805346699413075191385)
        ·
          refine ⟨631517854010024559806393539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 842023805346699413075191385 631517854010024559806393539)
          ·
            refine ⟨947276781015036839709590309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 631517854010024559806393539 947276781015036839709590309)
            ·
              refine ⟨177614396440319407445548183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 947276781015036839709590309 177614396440319407445548183)
              ·
                refine ⟨266421594660479111168322275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177614396440319407445548183 266421594660479111168322275)
                ·
                  refine ⟨399632391990718666752483413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 266421594660479111168322275 399632391990718666752483413)
                  ·
                    refine ⟨4683192093641234376005665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 399632391990718666752483413 4683192093641234376005665)
                    ·
                      refine ⟨3512394070230925782004249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4683192093641234376005665 3512394070230925782004249)
                      ·
                        rfl

theorem cell23_6840363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 8, 2].length) (baseStart_6840363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6840363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6840363 prefixEnd_6840363 := by exact prefixLift 6840363
  have htrace : WordTrace (prefixWord ++ tailWord_6840363) baseStart_6840363 baseEnd_6840363 := by
    simpa [prefixWord, tailWord_6840363, baseEnd_6840363] using wordTrace_append hprefix tailTrace_6840363
  have hstable : (prefixWord ++ tailWord_6840363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6840363).length < 2 ^ (prefixWord ++ tailWord_6840363).sum := by decide
  have hdescent : baseEnd_6840363 < baseStart_6840363 := by decide
  rcases family_descends (prefixWord ++ tailWord_6840363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6840373 : List Nat := [1, 3, 3, 1, 1, 1, 4, 2, 1, 6]
def baseStart_6840373 : Nat := 118140960795 + 6840373 * 2 ^ 59
def prefixEnd_6840373 : Nat := 4983230072969 + 3 ^ 40 * 6840373 * 2
def baseEnd_6840373 : Nat := 1170799735012490247626401

theorem tailTrace_6840373 : CollatzResearch.WordTrace tailWord_6840373 prefixEnd_6840373 1170799735012490247626401 := by
  unfold tailWord_6840373
  simp only [CollatzResearch.WordTrace]
  refine ⟨249488899647504338544957773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166325933098336225696638515 249488899647504338544957773)
  ·
    refine ⟨93558337367814126954359165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249488899647504338544957773 93558337367814126954359165)
    ·
      refine ⟨35084376512930297607884687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93558337367814126954359165 35084376512930297607884687)
      ·
        refine ⟨52626564769395446411827031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35084376512930297607884687 52626564769395446411827031)
        ·
          refine ⟨78939847154093169617740547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52626564769395446411827031 78939847154093169617740547)
          ·
            refine ⟨118409770731139754426610821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78939847154093169617740547 118409770731139754426610821)
            ·
              refine ⟨22201832012088703954989529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 118409770731139754426610821 22201832012088703954989529)
              ·
                refine ⟨16651374009066527966242147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22201832012088703954989529 16651374009066527966242147)
                ·
                  refine ⟨24977061013599791949363221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16651374009066527966242147 24977061013599791949363221)
                  ·
                    refine ⟨1170799735012490247626401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24977061013599791949363221 1170799735012490247626401)
                    ·
                      rfl

theorem cell23_6840373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 2, 1, 6].length) (baseStart_6840373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6840373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6840373 prefixEnd_6840373 := by exact prefixLift 6840373
  have htrace : WordTrace (prefixWord ++ tailWord_6840373) baseStart_6840373 baseEnd_6840373 := by
    simpa [prefixWord, tailWord_6840373, baseEnd_6840373] using wordTrace_append hprefix tailTrace_6840373
  have hstable : (prefixWord ++ tailWord_6840373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6840373).length < 2 ^ (prefixWord ++ tailWord_6840373).sum := by decide
  have hdescent : baseEnd_6840373 < baseStart_6840373 := by decide
  rcases family_descends (prefixWord ++ tailWord_6840373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6840380 : List Nat := [2, 2, 2, 2, 2, 1, 3, 3, 1, 1, 4]
def baseStart_6840380 : Nat := 118140960795 + 6840380 * 2 ^ 59
def prefixEnd_6840380 : Nat := 4983230072969 + 3 ^ 40 * 6840380 * 2
def baseEnd_6840380 : Nat := 3512402799402052215491671

theorem tailTrace_6840380 : CollatzResearch.WordTrace tailWord_6840380 prefixEnd_6840380 3512402799402052215491671 := by
  unfold tailWord_6840380
  simp only [CollatzResearch.WordTrace]
  refine ⟨124744577479239489370231297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166326103305652652493641729 124744577479239489370231297)
  ·
    refine ⟨93558433109429617027673473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124744577479239489370231297 93558433109429617027673473)
    ·
      refine ⟨70168824832072212770755105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93558433109429617027673473 70168824832072212770755105)
      ·
        refine ⟨52626618624054159578066329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70168824832072212770755105 52626618624054159578066329)
        ·
          refine ⟨39469963968040619683549747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52626618624054159578066329 39469963968040619683549747)
          ·
            refine ⟨59204945952060929525324621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39469963968040619683549747 59204945952060929525324621)
            ·
              refine ⟨22201854732022848571996733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59204945952060929525324621 22201854732022848571996733)
              ·
                refine ⟨8325695524508568214498775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22201854732022848571996733 8325695524508568214498775)
                ·
                  refine ⟨12488543286762852321748163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8325695524508568214498775 12488543286762852321748163)
                  ·
                    refine ⟨18732814930144278482622245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12488543286762852321748163 18732814930144278482622245)
                    ·
                      refine ⟨3512402799402052215491671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18732814930144278482622245 3512402799402052215491671)
                      ·
                        rfl

theorem cell23_6840380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 3, 1, 1, 4].length) (baseStart_6840380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6840380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6840380 prefixEnd_6840380 := by exact prefixLift 6840380
  have htrace : WordTrace (prefixWord ++ tailWord_6840380) baseStart_6840380 baseEnd_6840380 := by
    simpa [prefixWord, tailWord_6840380, baseEnd_6840380] using wordTrace_append hprefix tailTrace_6840380
  have hstable : (prefixWord ++ tailWord_6840380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6840380).length < 2 ^ (prefixWord ++ tailWord_6840380).sum := by decide
  have hdescent : baseEnd_6840380 < baseStart_6840380 := by decide
  rcases family_descends (prefixWord ++ tailWord_6840380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6840430 : List Nat := [4, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3]
def baseStart_6840430 : Nat := 118140960795 + 6840430 * 2 ^ 59
def prefixEnd_6840430 : Nat := 4983230072969 + 3 ^ 40 * 6840430 * 2
def baseEnd_6840430 : Nat := 3512428473434777019866441

theorem tailTrace_6840430 : CollatzResearch.WordTrace tailWord_6840430 prefixEnd_6840430 3512428473434777019866441 := by
  unfold tailWord_6840430
  simp only [CollatzResearch.WordTrace]
  refine ⟨31186372326037229659972843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166327319072198558186521829 31186372326037229659972843)
  ·
    refine ⟨46779558489055844489959265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31186372326037229659972843 46779558489055844489959265)
    ·
      refine ⟨35084668866791883367469449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46779558489055844489959265 35084668866791883367469449)
      ·
        refine ⟨26313501650093912525602087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35084668866791883367469449 26313501650093912525602087)
        ·
          refine ⟨39470252475140868788403131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26313501650093912525602087 39470252475140868788403131)
          ·
            refine ⟨59205378712711303182604697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39470252475140868788403131 59205378712711303182604697)
            ·
              refine ⟨44404034034533477386953523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59205378712711303182604697 44404034034533477386953523)
              ·
                refine ⟨66606051051800216080430285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44404034034533477386953523 66606051051800216080430285)
                ·
                  refine ⟨24977269144425081030161357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66606051051800216080430285 24977269144425081030161357)
                  ·
                    refine ⟨9366475929159405386310509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24977269144425081030161357 9366475929159405386310509)
                    ·
                      refine ⟨3512428473434777019866441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9366475929159405386310509 3512428473434777019866441)
                      ·
                        rfl

theorem cell23_6840430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_6840430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6840430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6840430 prefixEnd_6840430 := by exact prefixLift 6840430
  have htrace : WordTrace (prefixWord ++ tailWord_6840430) baseStart_6840430 baseEnd_6840430 := by
    simpa [prefixWord, tailWord_6840430, baseEnd_6840430] using wordTrace_append hprefix tailTrace_6840430
  have hstable : (prefixWord ++ tailWord_6840430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6840430).length < 2 ^ (prefixWord ++ tailWord_6840430).sum := by decide
  have hdescent : baseEnd_6840430 < baseStart_6840430 := by decide
  rcases family_descends (prefixWord ++ tailWord_6840430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6840431 : List Nat := [1, 1, 2, 1, 3, 6, 1, 3, 1, 2, 2]
def baseStart_6840431 : Nat := 118140960795 + 6840431 * 2 ^ 59
def prefixEnd_6840431 : Nat := 4983230072969 + 3 ^ 40 * 6840431 * 2
def baseEnd_6840431 : Nat := 3512428986915431515953937

theorem tailTrace_6840431 : CollatzResearch.WordTrace tailWord_6840431 prefixEnd_6840431 3512428986915431515953937 := by
  unfold tailWord_6840431
  simp only [CollatzResearch.WordTrace]
  refine ⟨249491015081294214450569147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166327343387529476300379431 249491015081294214450569147)
  ·
    refine ⟨374236522621941321675853721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249491015081294214450569147 374236522621941321675853721)
    ·
      refine ⟨280677391966455991256890291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 374236522621941321675853721 280677391966455991256890291)
      ·
        refine ⟨421016087949683986885335437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280677391966455991256890291 421016087949683986885335437)
        ·
          refine ⟨157881032981131495082000789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 421016087949683986885335437 157881032981131495082000789)
          ·
            refine ⟨7400673420990538831968787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 157881032981131495082000789 7400673420990538831968787)
            ·
              refine ⟨11101010131485808247953181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7400673420990538831968787 11101010131485808247953181)
              ·
                refine ⟨4162878799307178092982443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11101010131485808247953181 4162878799307178092982443)
                ·
                  refine ⟨6244318198960767139473665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4162878799307178092982443 6244318198960767139473665)
                  ·
                    refine ⟨4683238649220575354605249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6244318198960767139473665 4683238649220575354605249)
                    ·
                      refine ⟨3512428986915431515953937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4683238649220575354605249 3512428986915431515953937)
                      ·
                        rfl

theorem cell23_6840431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 3, 1, 2, 2].length) (baseStart_6840431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6840431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6840431 prefixEnd_6840431 := by exact prefixLift 6840431
  have htrace : WordTrace (prefixWord ++ tailWord_6840431) baseStart_6840431 baseEnd_6840431 := by
    simpa [prefixWord, tailWord_6840431, baseEnd_6840431] using wordTrace_append hprefix tailTrace_6840431
  have hstable : (prefixWord ++ tailWord_6840431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6840431).length < 2 ^ (prefixWord ++ tailWord_6840431).sum := by decide
  have hdescent : baseEnd_6840431 < baseStart_6840431 := by decide
  rcases family_descends (prefixWord ++ tailWord_6840431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6840440 : List Nat := [2, 1, 2, 1, 1, 1, 3, 2, 5, 3, 2]
def baseStart_6840440 : Nat := 118140960795 + 6840440 * 2 ^ 59
def prefixEnd_6840440 : Nat := 4983230072969 + 3 ^ 40 * 6840440 * 2
def baseEnd_6840440 : Nat := 3512433608241321980741395

theorem tailTrace_6840440 : CollatzResearch.WordTrace tailWord_6840440 prefixEnd_6840440 3512433608241321980741395 := by
  unfold tailWord_6840440
  simp only [CollatzResearch.WordTrace]
  refine ⟨124745671669130804493823387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166327562225507739325097849 124745671669130804493823387)
  ·
    refine ⟨187118507503696206740735081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124745671669130804493823387 187118507503696206740735081)
    ·
      refine ⟨140338880627772155055551311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187118507503696206740735081 140338880627772155055551311)
      ·
        refine ⟨210508320941658232583326967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140338880627772155055551311 210508320941658232583326967)
        ·
          refine ⟨315762481412487348874990451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210508320941658232583326967 315762481412487348874990451)
          ·
            refine ⟨473643722118731023312485677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315762481412487348874990451 473643722118731023312485677)
            ·
              refine ⟨177616395794524133742182129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 473643722118731023312485677 177616395794524133742182129)
              ·
                refine ⟨133212296845893100306636597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 177616395794524133742182129 133212296845893100306636597)
                ·
                  refine ⟨12488652829302478153747181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 133212296845893100306636597 12488652829302478153747181)
                  ·
                    refine ⟨4683244810988429307655193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12488652829302478153747181 4683244810988429307655193)
                    ·
                      refine ⟨3512433608241321980741395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4683244810988429307655193 3512433608241321980741395)
                      ·
                        rfl

theorem cell23_6840440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 5, 3, 2].length) (baseStart_6840440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6840440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6840440 prefixEnd_6840440 := by exact prefixLift 6840440
  have htrace : WordTrace (prefixWord ++ tailWord_6840440) baseStart_6840440 baseEnd_6840440 := by
    simpa [prefixWord, tailWord_6840440, baseEnd_6840440] using wordTrace_append hprefix tailTrace_6840440
  have hstable : (prefixWord ++ tailWord_6840440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6840440).length < 2 ^ (prefixWord ++ tailWord_6840440).sum := by decide
  have hdescent : baseEnd_6840440 < baseStart_6840440 := by decide
  rcases family_descends (prefixWord ++ tailWord_6840440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6840468 : List Nat := [2, 4, 2, 3, 2, 1, 1, 2, 1, 2, 3]
def baseStart_6840468 : Nat := 118140960795 + 6840468 * 2 ^ 59
def prefixEnd_6840468 : Nat := 4983230072969 + 3 ^ 40 * 6840468 * 2
def baseEnd_6840468 : Nat := 3512447985699647871191267

theorem tailTrace_6840468 : CollatzResearch.WordTrace tailWord_6840468 prefixEnd_6840468 3512447985699647871191267 := by
  unfold tailWord_6840468
  simp only [CollatzResearch.WordTrace]
  refine ⟨124746182291080084884833029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166328243054773446513110705 124746182291080084884833029)
  ·
    refine ⟨23389909179577515915906193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124746182291080084884833029 23389909179577515915906193)
    ·
      refine ⟨17542431884683136936929645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23389909179577515915906193 17542431884683136936929645)
      ·
        refine ⟨6578411956756176351348617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17542431884683136936929645 6578411956756176351348617)
        ·
          refine ⟨4933808967567132263511463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6578411956756176351348617 4933808967567132263511463)
          ·
            refine ⟨7400713451350698395267195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4933808967567132263511463 7400713451350698395267195)
            ·
              refine ⟨11101070177026047592900793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7400713451350698395267195 11101070177026047592900793)
              ·
                refine ⟨8325802632769535694675595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11101070177026047592900793 8325802632769535694675595)
                ·
                  refine ⟨12488703949154303542013393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8325802632769535694675595 12488703949154303542013393)
                  ·
                    refine ⟨9366527961865727656510045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12488703949154303542013393 9366527961865727656510045)
                    ·
                      refine ⟨3512447985699647871191267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9366527961865727656510045 3512447985699647871191267)
                      ·
                        rfl

theorem cell23_6840468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_6840468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6840468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6840468 prefixEnd_6840468 := by exact prefixLift 6840468
  have htrace : WordTrace (prefixWord ++ tailWord_6840468) baseStart_6840468 baseEnd_6840468 := by
    simpa [prefixWord, tailWord_6840468, baseEnd_6840468] using wordTrace_append hprefix tailTrace_6840468
  have hstable : (prefixWord ++ tailWord_6840468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6840468).length < 2 ^ (prefixWord ++ tailWord_6840468).sum := by decide
  have hdescent : baseEnd_6840468 < baseStart_6840468 := by decide
  rcases family_descends (prefixWord ++ tailWord_6840468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6840474 : List Nat := [3, 1, 1, 5, 2, 1, 1, 1, 3, 3, 2]
def baseStart_6840474 : Nat := 118140960795 + 6840474 * 2 ^ 59
def prefixEnd_6840474 : Nat := 4983230072969 + 3 ^ 40 * 6840474 * 2
def baseEnd_6840474 : Nat := 3512451066583574847716239

theorem tailTrace_6840474 : CollatzResearch.WordTrace tailWord_6840474 prefixEnd_6840474 3512451066583574847716239 := by
  unfold tailWord_6840474
  simp only [CollatzResearch.WordTrace]
  refine ⟨62373145855034608198596119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166328388946758955196256317 62373145855034608198596119)
  ·
    refine ⟨93559718782551912297894179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62373145855034608198596119 93559718782551912297894179)
    ·
      refine ⟨140339578173827868446841269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93559718782551912297894179 140339578173827868446841269)
      ·
        refine ⟨13156835453796362666891369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 140339578173827868446841269 13156835453796362666891369)
        ·
          refine ⟨9867626590347272000168527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13156835453796362666891369 9867626590347272000168527)
          ·
            refine ⟨14801439885520908000252791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9867626590347272000168527 14801439885520908000252791)
            ·
              refine ⟨22202159828281362000379187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14801439885520908000252791 22202159828281362000379187)
              ·
                refine ⟨33303239742422043000568781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22202159828281362000379187 33303239742422043000568781)
                ·
                  refine ⟨12488714903408266125213293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33303239742422043000568781 12488714903408266125213293)
                  ·
                    refine ⟨4683268088778099796954985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12488714903408266125213293 4683268088778099796954985)
                    ·
                      refine ⟨3512451066583574847716239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4683268088778099796954985 3512451066583574847716239)
                      ·
                        rfl

theorem cell23_6840474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_6840474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6840474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6840474 prefixEnd_6840474 := by exact prefixLift 6840474
  have htrace : WordTrace (prefixWord ++ tailWord_6840474) baseStart_6840474 baseEnd_6840474 := by
    simpa [prefixWord, tailWord_6840474, baseEnd_6840474] using wordTrace_append hprefix tailTrace_6840474
  have hstable : (prefixWord ++ tailWord_6840474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6840474).length < 2 ^ (prefixWord ++ tailWord_6840474).sum := by decide
  have hdescent : baseEnd_6840474 < baseStart_6840474 := by decide
  rcases family_descends (prefixWord ++ tailWord_6840474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6840483 : List Nat := [1, 1, 1, 4, 1, 1, 1, 1, 6, 2, 4]
def baseStart_6840483 : Nat := 118140960795 + 6840483 * 2 ^ 59
def prefixEnd_6840483 : Nat := 4983230072969 + 3 ^ 40 * 6840483 * 2
def baseEnd_6840483 : Nat := 3512455687909465312503697

theorem tailTrace_6840483 : CollatzResearch.WordTrace tailWord_6840483 prefixEnd_6840483 3512455687909465312503697 := by
  unfold tailWord_6840483
  simp only [CollatzResearch.WordTrace]
  refine ⟨249492911677105827331462103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166328607784737218220974735 249492911677105827331462103)
  ·
    refine ⟨374239367515658740997193155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249492911677105827331462103 374239367515658740997193155)
    ·
      refine ⟨561359051273488111495789733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374239367515658740997193155 561359051273488111495789733)
      ·
        refine ⟨105254822113779020905460575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 561359051273488111495789733 105254822113779020905460575)
        ·
          refine ⟨157882233170668531358190863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105254822113779020905460575 157882233170668531358190863)
          ·
            refine ⟨236823349756002797037286295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157882233170668531358190863 236823349756002797037286295)
            ·
              refine ⟨355235024634004195555929443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 236823349756002797037286295 355235024634004195555929443)
              ·
                refine ⟨532852536951006293333894165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 355235024634004195555929443 532852536951006293333894165)
                ·
                  refine ⟨24977462669578420000026289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 532852536951006293333894165 24977462669578420000026289)
                  ·
                    refine ⟨18733097002183815000019717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24977462669578420000026289 18733097002183815000019717)
                    ·
                      refine ⟨3512455687909465312503697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18733097002183815000019717 3512455687909465312503697)
                      ·
                        rfl

theorem cell23_6840483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 6, 2, 4].length) (baseStart_6840483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6840483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6840483 prefixEnd_6840483 := by exact prefixLift 6840483
  have htrace : WordTrace (prefixWord ++ tailWord_6840483) baseStart_6840483 baseEnd_6840483 := by
    simpa [prefixWord, tailWord_6840483, baseEnd_6840483] using wordTrace_append hprefix tailTrace_6840483
  have hstable : (prefixWord ++ tailWord_6840483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6840483).length < 2 ^ (prefixWord ++ tailWord_6840483).sum := by decide
  have hdescent : baseEnd_6840483 < baseStart_6840483 := by decide
  rcases family_descends (prefixWord ++ tailWord_6840483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6840504 : List Nat := [2, 1, 2, 1, 2, 1, 6, 2, 2, 2, 2]
def baseStart_6840504 : Nat := 118140960795 + 6840504 * 2 ^ 59
def prefixEnd_6840504 : Nat := 4983230072969 + 3 ^ 40 * 6840504 * 2
def baseEnd_6840504 : Nat := 3512466471003209730341101

theorem tailTrace_6840504 : CollatzResearch.WordTrace tailWord_6840504 prefixEnd_6840504 3512466471003209730341101 := by
  unfold tailWord_6840504
  simp only [CollatzResearch.WordTrace]
  refine ⟨124746838805014873958988283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166329118406686498611984377 124746838805014873958988283)
  ·
    refine ⟨187120258207522310938482425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124746838805014873958988283 187120258207522310938482425)
    ·
      refine ⟨140340193655641733203861819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187120258207522310938482425 140340193655641733203861819)
      ·
        refine ⟨210510290483462599805792729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140340193655641733203861819 210510290483462599805792729)
        ·
          refine ⟨157882717862596949854344547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210510290483462599805792729 157882717862596949854344547)
          ·
            refine ⟨236824076793895424781516821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157882717862596949854344547 236824076793895424781516821)
            ·
              refine ⟨11101128599713848036633601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 236824076793895424781516821 11101128599713848036633601)
              ·
                refine ⟨8325846449785386027475201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11101128599713848036633601 8325846449785386027475201)
                ·
                  refine ⟨6244384837339039520606401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8325846449785386027475201 6244384837339039520606401)
                  ·
                    refine ⟨4683288628004279640454801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6244384837339039520606401 4683288628004279640454801)
                    ·
                      refine ⟨3512466471003209730341101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4683288628004279640454801 3512466471003209730341101)
                      ·
                        rfl

theorem cell23_6840504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 2, 2, 2, 2].length) (baseStart_6840504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6840504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6840504 prefixEnd_6840504 := by exact prefixLift 6840504
  have htrace : WordTrace (prefixWord ++ tailWord_6840504) baseStart_6840504 baseEnd_6840504 := by
    simpa [prefixWord, tailWord_6840504, baseEnd_6840504] using wordTrace_append hprefix tailTrace_6840504
  have hstable : (prefixWord ++ tailWord_6840504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6840504).length < 2 ^ (prefixWord ++ tailWord_6840504).sum := by decide
  have hdescent : baseEnd_6840504 < baseStart_6840504 := by decide
  rcases family_descends (prefixWord ++ tailWord_6840504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6840514 : List Nat := [3, 5, 1, 1, 1, 2, 1, 1, 2, 6]
def baseStart_6840514 : Nat := 118140960795 + 6840514 * 2 ^ 59
def prefixEnd_6840514 : Nat := 4983230072969 + 3 ^ 40 * 6840514 * 2
def baseEnd_6840514 : Nat := 1170823868603251563738685

theorem tailTrace_6840514 : CollatzResearch.WordTrace tailWord_6840514 prefixEnd_6840514 1170823868603251563738685 := by
  unfold tailWord_6840514
  simp only [CollatzResearch.WordTrace]
  refine ⟨62373510584998379906460149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166329361559995679750560397 62373510584998379906460149)
  ·
    refine ⟨5847516617343598116230639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62373510584998379906460149 5847516617343598116230639)
    ·
      refine ⟨8771274926015397174345959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5847516617343598116230639 8771274926015397174345959)
      ·
        refine ⟨13156912389023095761518939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8771274926015397174345959 13156912389023095761518939)
        ·
          refine ⟨19735368583534643642278409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13156912389023095761518939 19735368583534643642278409)
          ·
            refine ⟨14801526437650982731708807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19735368583534643642278409 14801526437650982731708807)
            ·
              refine ⟨22202289656476474097563211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14801526437650982731708807 22202289656476474097563211)
              ·
                refine ⟨33303434484714711146344817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22202289656476474097563211 33303434484714711146344817)
                ·
                  refine ⟨24977575863536033359758613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33303434484714711146344817 24977575863536033359758613)
                  ·
                    refine ⟨1170823868603251563738685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24977575863536033359758613 1170823868603251563738685)
                    ·
                      rfl

theorem cell23_6840514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_6840514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6840514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6840514 prefixEnd_6840514 := by exact prefixLift 6840514
  have htrace : WordTrace (prefixWord ++ tailWord_6840514) baseStart_6840514 baseEnd_6840514 := by
    simpa [prefixWord, tailWord_6840514, baseEnd_6840514] using wordTrace_append hprefix tailTrace_6840514
  have hstable : (prefixWord ++ tailWord_6840514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6840514).length < 2 ^ (prefixWord ++ tailWord_6840514).sum := by decide
  have hdescent : baseEnd_6840514 < baseStart_6840514 := by decide
  rcases family_descends (prefixWord ++ tailWord_6840514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6840523 : List Nat := [1, 1, 1, 1, 3, 2, 4, 2, 1, 7]
def baseStart_6840523 : Nat := 118140960795 + 6840523 * 2 ^ 59
def prefixEnd_6840523 : Nat := 4983230072969 + 3 ^ 40 * 6840523 * 2
def baseEnd_6840523 : Nat := 1170825409045215052001171

theorem tailTrace_6840523 : CollatzResearch.WordTrace tailWord_6840523 prefixEnd_6840523 1170825409045215052001171 := by
  unfold tailWord_6840523
  simp only [CollatzResearch.WordTrace]
  refine ⟨249494370596960914162918223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166329580397973942775278815 249494370596960914162918223)
  ·
    refine ⟨374241555895441371244377335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249494370596960914162918223 374241555895441371244377335)
    ·
      refine ⟨561362333843162056866566003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374241555895441371244377335 561362333843162056866566003)
      ·
        refine ⟨842043500764743085299849005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 561362333843162056866566003 842043500764743085299849005)
        ·
          refine ⟨315766312786778656987443377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 842043500764743085299849005 315766312786778656987443377)
          ·
            refine ⟨236824734590083992740582533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 315766312786778656987443377 236824734590083992740582533)
            ·
              refine ⟨44404637735640748638859225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 236824734590083992740582533 44404637735640748638859225)
              ·
                refine ⟨33303478301730561479144419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44404637735640748638859225 33303478301730561479144419)
                ·
                  refine ⟨49955217452595842218716629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33303478301730561479144419 49955217452595842218716629)
                  ·
                    refine ⟨1170825409045215052001171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49955217452595842218716629 1170825409045215052001171)
                    ·
                      rfl

theorem cell23_6840523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 2, 1, 7].length) (baseStart_6840523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6840523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6840523 prefixEnd_6840523 := by exact prefixLift 6840523
  have htrace : WordTrace (prefixWord ++ tailWord_6840523) baseStart_6840523 baseEnd_6840523 := by
    simpa [prefixWord, tailWord_6840523, baseEnd_6840523] using wordTrace_append hprefix tailTrace_6840523
  have hstable : (prefixWord ++ tailWord_6840523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6840523).length < 2 ^ (prefixWord ++ tailWord_6840523).sum := by decide
  have hdescent : baseEnd_6840523 < baseStart_6840523 := by decide
  rcases family_descends (prefixWord ++ tailWord_6840523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6840560 : List Nat := [2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 4]
def baseStart_6840560 : Nat := 118140960795 + 6840560 * 2 ^ 59
def prefixEnd_6840560 : Nat := 4983230072969 + 3 ^ 40 * 6840560 * 2
def baseEnd_6840560 : Nat := 3512495225919861511240843

theorem tailTrace_6840560 : CollatzResearch.WordTrace tailWord_6840560 prefixEnd_6840560 3512495225919861511240843 := by
  unfold tailWord_6840560
  simp only [CollatzResearch.WordTrace]
  refine ⟨124747860048913434741007567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166330480065217912988010089 124747860048913434741007567)
  ·
    refine ⟨187121790073370152111511351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124747860048913434741007567 187121790073370152111511351)
    ·
      refine ⟨280682685110055228167267027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187121790073370152111511351 280682685110055228167267027)
      ·
        refine ⟨421024027665082842250900541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280682685110055228167267027 421024027665082842250900541)
        ·
          refine ⟨157884010374406065844087703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 421024027665082842250900541 157884010374406065844087703)
          ·
            refine ⟨236826015561609098766131555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157884010374406065844087703 236826015561609098766131555)
            ·
              refine ⟨355239023342413648149197333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 236826015561609098766131555 355239023342413648149197333)
              ·
                refine ⟨16651829219175639756993625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 355239023342413648149197333 16651829219175639756993625)
                ·
                  refine ⟨12488871914381729817745219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16651829219175639756993625 12488871914381729817745219)
                  ·
                    refine ⟨18733307871572594726617829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12488871914381729817745219 18733307871572594726617829)
                    ·
                      refine ⟨3512495225919861511240843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18733307871572594726617829 3512495225919861511240843)
                      ·
                        rfl

theorem cell23_6840560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 4].length) (baseStart_6840560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6840560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6840560 prefixEnd_6840560 := by exact prefixLift 6840560
  have htrace : WordTrace (prefixWord ++ tailWord_6840560) baseStart_6840560 baseEnd_6840560 := by
    simpa [prefixWord, tailWord_6840560, baseEnd_6840560] using wordTrace_append hprefix tailTrace_6840560
  have hstable : (prefixWord ++ tailWord_6840560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6840560).length < 2 ^ (prefixWord ++ tailWord_6840560).sum := by decide
  have hdescent : baseEnd_6840560 < baseStart_6840560 := by decide
  rcases family_descends (prefixWord ++ tailWord_6840560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6840577 : List Nat := [1, 2, 4, 1, 1, 2, 1, 3, 2, 4, 2]
def baseStart_6840577 : Nat := 118140960795 + 6840577 * 2 ^ 59
def prefixEnd_6840577 : Nat := 4983230072969 + 3 ^ 40 * 6840577 * 2
def baseEnd_6840577 : Nat := 3512503955090987944728265

theorem tailTrace_6840577 : CollatzResearch.WordTrace tailWord_6840577 prefixEnd_6840577 3512503955090987944728265 := by
  unfold tailWord_6840577
  simp only [CollatzResearch.WordTrace]
  refine ⟨249496340138765281385383985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166330893425843520923589323 249496340138765281385383985)
  ·
    refine ⟨187122255104073961039037989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249496340138765281385383985 187122255104073961039037989)
    ·
      refine ⟨35085422832013867694819623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 187122255104073961039037989 35085422832013867694819623)
      ·
        refine ⟨52628134248020801542229435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35085422832013867694819623 52628134248020801542229435)
        ·
          refine ⟨78942201372031202313344153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52628134248020801542229435 78942201372031202313344153)
          ·
            refine ⟨59206651029023401735008115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78942201372031202313344153 59206651029023401735008115)
            ·
              refine ⟨88809976543535102602512173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59206651029023401735008115 88809976543535102602512173)
              ·
                refine ⟨33303741203825663475942065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88809976543535102602512173 33303741203825663475942065)
                ·
                  refine ⟨24977805902869247606956549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33303741203825663475942065 24977805902869247606956549)
                  ·
                    refine ⟨4683338606787983926304353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24977805902869247606956549 4683338606787983926304353)
                    ·
                      refine ⟨3512503955090987944728265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4683338606787983926304353 3512503955090987944728265)
                      ·
                        rfl

theorem cell23_6840577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 3, 2, 4, 2].length) (baseStart_6840577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6840577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6840577 prefixEnd_6840577 := by exact prefixLift 6840577
  have htrace : WordTrace (prefixWord ++ tailWord_6840577) baseStart_6840577 baseEnd_6840577 := by
    simpa [prefixWord, tailWord_6840577, baseEnd_6840577] using wordTrace_append hprefix tailTrace_6840577
  have hstable : (prefixWord ++ tailWord_6840577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6840577).length < 2 ^ (prefixWord ++ tailWord_6840577).sum := by decide
  have hdescent : baseEnd_6840577 < baseStart_6840577 := by decide
  rcases family_descends (prefixWord ++ tailWord_6840577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6840590 : List Nat := [4, 1, 1, 2, 1, 2, 1, 1, 2, 4, 4]
def baseStart_6840590 : Nat := 118140960795 + 6840590 * 2 ^ 59
def prefixEnd_6840590 : Nat := 4983230072969 + 3 ^ 40 * 6840590 * 2
def baseEnd_6840590 : Nat := 3512510630339496393865705

theorem tailTrace_6840590 : CollatzResearch.WordTrace tailWord_6840590 prefixEnd_6840590 3512510630339496393865705 := by
  unfold tailWord_6840590
  simp only [CollatzResearch.WordTrace]
  refine ⟨31187101785964773075700903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166331209525145456403738149 31187101785964773075700903)
  ·
    refine ⟨46780652678947159613551355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31187101785964773075700903 46780652678947159613551355)
    ·
      refine ⟨70170979018420739420327033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46780652678947159613551355 70170979018420739420327033)
      ·
        refine ⟨52628234263815554565245275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70170979018420739420327033 52628234263815554565245275)
        ·
          refine ⟨78942351395723331847867913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52628234263815554565245275 78942351395723331847867913)
          ·
            refine ⟨59206763546792498885900935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78942351395723331847867913 59206763546792498885900935)
            ·
              refine ⟨88810145320188748328851403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59206763546792498885900935 88810145320188748328851403)
              ·
                refine ⟨133215217980283122493277105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88810145320188748328851403 133215217980283122493277105)
                ·
                  refine ⟨99911413485212341869957829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 133215217980283122493277105 99911413485212341869957829)
                  ·
                    refine ⟨18733390028477314100617093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 99911413485212341869957829 18733390028477314100617093)
                    ·
                      refine ⟨3512510630339496393865705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18733390028477314100617093 3512510630339496393865705)
                      ·
                        rfl

theorem cell23_6840590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_6840590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6840590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6840590 prefixEnd_6840590 := by exact prefixLift 6840590
  have htrace : WordTrace (prefixWord ++ tailWord_6840590) baseStart_6840590 baseEnd_6840590 := by
    simpa [prefixWord, tailWord_6840590, baseEnd_6840590] using wordTrace_append hprefix tailTrace_6840590
  have hstable : (prefixWord ++ tailWord_6840590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6840590).length < 2 ^ (prefixWord ++ tailWord_6840590).sum := by decide
  have hdescent : baseEnd_6840590 < baseStart_6840590 := by decide
  rcases family_descends (prefixWord ++ tailWord_6840590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6840634 : List Nat := [3, 1, 1, 1, 4, 4, 2, 1, 6]
def baseStart_6840634 : Nat := 118140960795 + 6840634 * 2 ^ 59
def prefixEnd_6840634 : Nat := 4983230072969 + 3 ^ 40 * 6840634 * 2
def baseEnd_6840634 : Nat := 390281469276477135746167

theorem tailTrace_6840634 : CollatzResearch.WordTrace tailWord_6840634 prefixEnd_6840634 390281469276477135746167 := by
  unfold tailWord_6840634
  simp only [CollatzResearch.WordTrace]
  refine ⟨62374604774889695030052239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166332279399705853413472637 62374604774889695030052239)
  ·
    refine ⟨93561907162334542545078359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62374604774889695030052239 93561907162334542545078359)
    ·
      refine ⟨140342860743501813817617539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93561907162334542545078359 140342860743501813817617539)
      ·
        refine ⟨210514291115252720726426309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140342860743501813817617539 210514291115252720726426309)
        ·
          refine ⟨39471429584109885136204933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 210514291115252720726426309 39471429584109885136204933)
          ·
            refine ⟨7400893047020603463038425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39471429584109885136204933 7400893047020603463038425)
            ·
              refine ⟨5550669785265452597278819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7400893047020603463038425 5550669785265452597278819)
              ·
                refine ⟨8326004677898178895918229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5550669785265452597278819 8326004677898178895918229)
                ·
                  refine ⟨390281469276477135746167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8326004677898178895918229 390281469276477135746167)
                  ·
                    rfl

theorem cell23_6840634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 2, 1, 6].length) (baseStart_6840634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6840634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6840634 prefixEnd_6840634 := by exact prefixLift 6840634
  have htrace : WordTrace (prefixWord ++ tailWord_6840634) baseStart_6840634 baseEnd_6840634 := by
    simpa [prefixWord, tailWord_6840634, baseEnd_6840634] using wordTrace_append hprefix tailTrace_6840634
  have hstable : (prefixWord ++ tailWord_6840634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6840634).length < 2 ^ (prefixWord ++ tailWord_6840634).sum := by decide
  have hdescent : baseEnd_6840634 < baseStart_6840634 := by decide
  rcases family_descends (prefixWord ++ tailWord_6840634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6840701 : List Nat := [1, 4, 1, 1, 2, 4, 1, 2, 3, 2, 2]
def baseStart_6840701 : Nat := 118140960795 + 6840701 * 2 ^ 59
def prefixEnd_6840701 : Nat := 4983230072969 + 3 ^ 40 * 6840701 * 2
def baseEnd_6840701 : Nat := 3512567626692145459577695

theorem tailTrace_6840701 : CollatzResearch.WordTrace tailWord_6840701 prefixEnd_6840701 3512567626692145459577695 := by
  unfold tailWord_6840701
  simp only [CollatzResearch.WordTrace]
  refine ⟨249500862790316050562897957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166333908526877367041931971 249500862790316050562897957)
  ·
    refine ⟨46781411773184259480543367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 249500862790316050562897957 46781411773184259480543367)
    ·
      refine ⟨70172117659776389220815051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46781411773184259480543367 70172117659776389220815051)
      ·
        refine ⟨105258176489664583831222577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70172117659776389220815051 105258176489664583831222577)
        ·
          refine ⟨78943632367248437873416933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105258176489664583831222577 78943632367248437873416933)
          ·
            refine ⟨14801931068859082101265675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78943632367248437873416933 14801931068859082101265675)
            ·
              refine ⟨22202896603288623151898513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14801931068859082101265675 22202896603288623151898513)
              ·
                refine ⟨16652172452466467363923885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22202896603288623151898513 16652172452466467363923885)
                ·
                  refine ⟨6244564669674925261471457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16652172452466467363923885 6244564669674925261471457)
                  ·
                    refine ⟨4683423502256193946103593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6244564669674925261471457 4683423502256193946103593)
                    ·
                      refine ⟨3512567626692145459577695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4683423502256193946103593 3512567626692145459577695)
                      ·
                        rfl

theorem cell23_6840701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 2, 3, 2, 2].length) (baseStart_6840701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6840701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6840701 prefixEnd_6840701 := by exact prefixLift 6840701
  have htrace : WordTrace (prefixWord ++ tailWord_6840701) baseStart_6840701 baseEnd_6840701 := by
    simpa [prefixWord, tailWord_6840701, baseEnd_6840701] using wordTrace_append hprefix tailTrace_6840701
  have hstable : (prefixWord ++ tailWord_6840701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6840701).length < 2 ^ (prefixWord ++ tailWord_6840701).sum := by decide
  have hdescent : baseEnd_6840701 < baseStart_6840701 := by decide
  rcases family_descends (prefixWord ++ tailWord_6840701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6840718 : List Nat := [4, 1, 1, 4, 1, 3, 2, 1, 1, 1, 4]
def baseStart_6840718 : Nat := 118140960795 + 6840718 * 2 ^ 59
def prefixEnd_6840718 : Nat := 4983230072969 + 3 ^ 40 * 6840718 * 2
def baseEnd_6840718 : Nat := 3512576355863271893065117

theorem tailTrace_6840718 : CollatzResearch.WordTrace tailWord_6840718 prefixEnd_6840718 3512576355863271893065117 := by
  unfold tailWord_6840718
  simp only [CollatzResearch.WordTrace]
  refine ⟨31187685353906807808283351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166334321887502974977511205 31187685353906807808283351)
  ·
    refine ⟨46781528030860211712425027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31187685353906807808283351 46781528030860211712425027)
    ·
      refine ⟨70172292046290317568637541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46781528030860211712425027 70172292046290317568637541)
      ·
        refine ⟨13157304758679434544119539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70172292046290317568637541 13157304758679434544119539)
        ·
          refine ⟨19735957138019151816179309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13157304758679434544119539 19735957138019151816179309)
          ·
            refine ⟨7400983926757181931067241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19735957138019151816179309 7400983926757181931067241)
            ·
              refine ⟨5550737945067886448300431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7400983926757181931067241 5550737945067886448300431)
              ·
                refine ⟨8326106917601829672450647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5550737945067886448300431 8326106917601829672450647)
                ·
                  refine ⟨12489160376402744508675971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8326106917601829672450647 12489160376402744508675971)
                  ·
                    refine ⟨18733740564604116763013957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12489160376402744508675971 18733740564604116763013957)
                    ·
                      refine ⟨3512576355863271893065117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18733740564604116763013957 3512576355863271893065117)
                      ·
                        rfl

theorem cell23_6840718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_6840718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6840718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6840718 prefixEnd_6840718 := by exact prefixLift 6840718
  have htrace : WordTrace (prefixWord ++ tailWord_6840718) baseStart_6840718 baseEnd_6840718 := by
    simpa [prefixWord, tailWord_6840718, baseEnd_6840718] using wordTrace_append hprefix tailTrace_6840718
  have hstable : (prefixWord ++ tailWord_6840718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6840718).length < 2 ^ (prefixWord ++ tailWord_6840718).sum := by decide
  have hdescent : baseEnd_6840718 < baseStart_6840718 := by decide
  rcases family_descends (prefixWord ++ tailWord_6840718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6840761 : List Nat := [1, 2, 1, 4, 3, 1, 1, 4, 1, 3, 2]
def baseStart_6840761 : Nat := 118140960795 + 6840761 * 2 ^ 59
def prefixEnd_6840761 : Nat := 4983230072969 + 3 ^ 40 * 6840761 * 2
def baseEnd_6840761 : Nat := 3512598435531415224827419

theorem tailTrace_6840761 : CollatzResearch.WordTrace tailWord_6840761 prefixEnd_6840761 3512598435531415224827419 := by
  unfold tailWord_6840761
  simp only [CollatzResearch.WordTrace]
  refine ⟨249503051170098680810082137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166335367446732453873388091 249503051170098680810082137)
  ·
    refine ⟨187127288377574010607561603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249503051170098680810082137 187127288377574010607561603)
    ·
      refine ⟨280690932566361015911342405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187127288377574010607561603 280690932566361015911342405)
      ·
        refine ⟨52629549856192690483376701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 280690932566361015911342405 52629549856192690483376701)
        ·
          refine ⟨19736081196072258931266263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52629549856192690483376701 19736081196072258931266263)
          ·
            refine ⟨29604121794108388396899395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19736081196072258931266263 29604121794108388396899395)
            ·
              refine ⟨44406182691162582595349093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29604121794108388396899395 44406182691162582595349093)
              ·
                refine ⟨8326159254592984236627955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44406182691162582595349093 8326159254592984236627955)
                ·
                  refine ⟨12489238881889476354941933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8326159254592984236627955 12489238881889476354941933)
                  ·
                    refine ⟨4683464580708553633103225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12489238881889476354941933 4683464580708553633103225)
                    ·
                      refine ⟨3512598435531415224827419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4683464580708553633103225 3512598435531415224827419)
                      ·
                        rfl

theorem cell23_6840761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 4, 1, 3, 2].length) (baseStart_6840761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6840761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6840761 prefixEnd_6840761 := by exact prefixLift 6840761
  have htrace : WordTrace (prefixWord ++ tailWord_6840761) baseStart_6840761 baseEnd_6840761 := by
    simpa [prefixWord, tailWord_6840761, baseEnd_6840761] using wordTrace_append hprefix tailTrace_6840761
  have hstable : (prefixWord ++ tailWord_6840761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6840761).length < 2 ^ (prefixWord ++ tailWord_6840761).sum := by decide
  have hdescent : baseEnd_6840761 < baseStart_6840761 := by decide
  rcases family_descends (prefixWord ++ tailWord_6840761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6840808 : List Nat := [2, 1, 4, 1, 1, 4, 1, 3, 2, 2, 2]
def baseStart_6840808 : Nat := 118140960795 + 6840808 * 2 ^ 59
def prefixEnd_6840808 : Nat := 4983230072969 + 3 ^ 40 * 6840808 * 2
def baseEnd_6840808 : Nat := 3512622569122176540939703

theorem tailTrace_6840808 : CollatzResearch.WordTrace tailWord_6840808 prefixEnd_6840808 3512622569122176540939703 := by
  unfold tailWord_6840808
  simp only [CollatzResearch.WordTrace]
  refine ⟨124752382700464203918521539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166336510267285605224695385 124752382700464203918521539)
  ·
    refine ⟨187128574050696305877782309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124752382700464203918521539 187128574050696305877782309)
    ·
      refine ⟨35086607634505557352084183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 187128574050696305877782309 35086607634505557352084183)
      ·
        refine ⟨52629911451758336028126275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35086607634505557352084183 52629911451758336028126275)
        ·
          refine ⟨78944867177637504042189413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52629911451758336028126275 78944867177637504042189413)
          ·
            refine ⟨14802162595807032007910515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78944867177637504042189413 14802162595807032007910515)
            ·
              refine ⟨22203243893710548011865773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14802162595807032007910515 22203243893710548011865773)
              ·
                refine ⟨8326216460141455504449665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22203243893710548011865773 8326216460141455504449665)
                ·
                  refine ⟨6244662345106091628337249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8326216460141455504449665 6244662345106091628337249)
                  ·
                    refine ⟨4683496758829568721252937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6244662345106091628337249 4683496758829568721252937)
                    ·
                      refine ⟨3512622569122176540939703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4683496758829568721252937 3512622569122176540939703)
                      ·
                        rfl

theorem cell23_6840808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 3, 2, 2, 2].length) (baseStart_6840808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6840808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6840808 prefixEnd_6840808 := by exact prefixLift 6840808
  have htrace : WordTrace (prefixWord ++ tailWord_6840808) baseStart_6840808 baseEnd_6840808 := by
    simpa [prefixWord, tailWord_6840808, baseEnd_6840808] using wordTrace_append hprefix tailTrace_6840808
  have hstable : (prefixWord ++ tailWord_6840808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6840808).length < 2 ^ (prefixWord ++ tailWord_6840808).sum := by decide
  have hdescent : baseEnd_6840808 < baseStart_6840808 := by decide
  rcases family_descends (prefixWord ++ tailWord_6840808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6840837 : List Nat := [1, 3, 1, 1, 2, 2, 3, 2, 1, 2, 5]
def baseStart_6840837 : Nat := 118140960795 + 6840837 * 2 ^ 59
def prefixEnd_6840837 : Nat := 4983230072969 + 3 ^ 40 * 6840837 * 2
def baseEnd_6840837 : Nat := 3512637460061156927477069

theorem tailTrace_6840837 : CollatzResearch.WordTrace tailWord_6840837 prefixEnd_6840837 3512637460061156927477069 := by
  unfold tailWord_6840837
  simp only [CollatzResearch.WordTrace]
  refine ⟨249505823117823345789848765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166337215411882230526565843 249505823117823345789848765)
  ·
    refine ⟨93564683669183754671193287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249505823117823345789848765 93564683669183754671193287)
    ·
      refine ⟨140347025503775632006789931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93564683669183754671193287 140347025503775632006789931)
      ·
        refine ⟨210520538255663448010184897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140347025503775632006789931 210520538255663448010184897)
        ·
          refine ⟨157890403691747586007638673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210520538255663448010184897 157890403691747586007638673)
          ·
            refine ⟨118417802768810689505729005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157890403691747586007638673 118417802768810689505729005)
            ·
              refine ⟨44406676038304008564648377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118417802768810689505729005 44406676038304008564648377)
              ·
                refine ⟨33305007028728006423486283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44406676038304008564648377 33305007028728006423486283)
                ·
                  refine ⟨49957510543092009635229425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33305007028728006423486283 49957510543092009635229425)
                  ·
                    refine ⟨37468132907319007226422069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49957510543092009635229425 37468132907319007226422069)
                    ·
                      refine ⟨3512637460061156927477069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37468132907319007226422069 3512637460061156927477069)
                      ·
                        rfl

theorem cell23_6840837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 2, 1, 2, 5].length) (baseStart_6840837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6840837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6840837 prefixEnd_6840837 := by exact prefixLift 6840837
  have htrace : WordTrace (prefixWord ++ tailWord_6840837) baseStart_6840837 baseEnd_6840837 := by
    simpa [prefixWord, tailWord_6840837, baseEnd_6840837] using wordTrace_append hprefix tailTrace_6840837
  have hstable : (prefixWord ++ tailWord_6840837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6840837).length < 2 ^ (prefixWord ++ tailWord_6840837).sum := by decide
  have hdescent : baseEnd_6840837 < baseStart_6840837 := by decide
  rcases family_descends (prefixWord ++ tailWord_6840837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6840844 : List Nat := [2, 2, 1, 2, 4, 1, 2, 2, 2, 5]
def baseStart_6840844 : Nat := 118140960795 + 6840844 * 2 ^ 59
def prefixEnd_6840844 : Nat := 4983230072969 + 3 ^ 40 * 6840844 * 2
def baseEnd_6840844 : Nat := 1170880351475246133363179

theorem tailTrace_6840844 : CollatzResearch.WordTrace tailWord_6840844 prefixEnd_6840844 1170880351475246133363179 := by
  unfold tailWord_6840844
  simp only [CollatzResearch.WordTrace]
  refine ⟨124753039214398992992676793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166337385619198657323569057 124753039214398992992676793)
  ·
    refine ⟨93564779410799244744507595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124753039214398992992676793 93564779410799244744507595)
    ·
      refine ⟨140347169116198867116761393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93564779410799244744507595 140347169116198867116761393)
      ·
        refine ⟨105260376837149150337571045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140347169116198867116761393 105260376837149150337571045)
        ·
          refine ⟨19736320656965465688294571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105260376837149150337571045 19736320656965465688294571)
          ·
            refine ⟨29604480985448198532441857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19736320656965465688294571 29604480985448198532441857)
            ·
              refine ⟨22203360739086148899331393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29604480985448198532441857 22203360739086148899331393)
              ·
                refine ⟨16652520554314611674498545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22203360739086148899331393 16652520554314611674498545)
                ·
                  refine ⟨12489390415735958755873909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16652520554314611674498545 12489390415735958755873909)
                  ·
                    refine ⟨1170880351475246133363179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12489390415735958755873909 1170880351475246133363179)
                    ·
                      rfl

theorem cell23_6840844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 2, 2, 5].length) (baseStart_6840844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6840844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6840844 prefixEnd_6840844 := by exact prefixLift 6840844
  have htrace : WordTrace (prefixWord ++ tailWord_6840844) baseStart_6840844 baseEnd_6840844 := by
    simpa [prefixWord, tailWord_6840844, baseEnd_6840844] using wordTrace_append hprefix tailTrace_6840844
  have hstable : (prefixWord ++ tailWord_6840844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6840844).length < 2 ^ (prefixWord ++ tailWord_6840844).sum := by decide
  have hdescent : baseEnd_6840844 < baseStart_6840844 := by decide
  rcases family_descends (prefixWord ++ tailWord_6840844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6840878 : List Nat := [4, 1, 3, 1, 3, 2, 1, 1, 2, 5]
def baseStart_6840878 : Nat := 118140960795 + 6840878 * 2 ^ 59
def prefixEnd_6840878 : Nat := 4983230072969 + 3 ^ 40 * 6840878 * 2
def baseEnd_6840878 : Nat := 1170886170922663755688127

theorem tailTrace_6840878 : CollatzResearch.WordTrace tailWord_6840878 prefixEnd_6840878 1170886170922663755688127 := by
  unfold tailWord_6840878
  simp only [CollatzResearch.WordTrace]
  refine ⟨31188414813834351224011411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166338212340449873194727525 31188414813834351224011411)
  ·
    refine ⟨46782622220751526836017117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31188414813834351224011411 46782622220751526836017117)
    ·
      refine ⟨17543483332781822563506419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46782622220751526836017117 17543483332781822563506419)
      ·
        refine ⟨26315224999172733845259629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17543483332781822563506419 26315224999172733845259629)
        ·
          refine ⟨9868209374689775191972361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26315224999172733845259629 9868209374689775191972361)
          ·
            refine ⟨7401157031017331393979271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9868209374689775191972361 7401157031017331393979271)
            ·
              refine ⟨11101735546525997090968907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7401157031017331393979271 11101735546525997090968907)
              ·
                refine ⟨16652603319788995636453361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11101735546525997090968907 16652603319788995636453361)
                ·
                  refine ⟨12489452489841746727340021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16652603319788995636453361 12489452489841746727340021)
                  ·
                    refine ⟨1170886170922663755688127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12489452489841746727340021 1170886170922663755688127)
                    ·
                      rfl

theorem cell23_6840878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_6840878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6840878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6840878 prefixEnd_6840878 := by exact prefixLift 6840878
  have htrace : WordTrace (prefixWord ++ tailWord_6840878) baseStart_6840878 baseEnd_6840878 := by
    simpa [prefixWord, tailWord_6840878, baseEnd_6840878] using wordTrace_append hprefix tailTrace_6840878
  have hstable : (prefixWord ++ tailWord_6840878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6840878).length < 2 ^ (prefixWord ++ tailWord_6840878).sum := by decide
  have hdescent : baseEnd_6840878 < baseStart_6840878 := by decide
  rcases family_descends (prefixWord ++ tailWord_6840878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6840887 : List Nat := [1, 1, 3, 1, 2, 3, 2, 2, 8]
def baseStart_6840887 : Nat := 118140960795 + 6840887 * 2 ^ 59
def prefixEnd_6840887 : Nat := 4983230072969 + 3 ^ 40 * 6840887 * 2
def baseEnd_6840887 : Nat := 390295903788209081316871

theorem tailTrace_6840887 : CollatzResearch.WordTrace tailWord_6840887 prefixEnd_6840887 390295903788209081316871 := by
  unfold tailWord_6840887
  simp only [CollatzResearch.WordTrace]
  refine ⟨249507646767642204329168915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166338431178428136219445943 249507646767642204329168915)
  ·
    refine ⟨374261470151463306493753373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249507646767642204329168915 374261470151463306493753373)
    ·
      refine ⟨140348051306798739935157515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 374261470151463306493753373 140348051306798739935157515)
      ·
        refine ⟨210522076960198109902736273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140348051306798739935157515 210522076960198109902736273)
        ·
          refine ⟨157891557720148582427052205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210522076960198109902736273 157891557720148582427052205)
          ·
            refine ⟨59209334145055718410144577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157891557720148582427052205 59209334145055718410144577)
            ·
              refine ⟨44407000608791788807608433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59209334145055718410144577 44407000608791788807608433)
              ·
                refine ⟨33305250456593841605706325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44407000608791788807608433 33305250456593841605706325)
                ·
                  refine ⟨390295903788209081316871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33305250456593841605706325 390295903788209081316871)
                  ·
                    rfl

theorem cell23_6840887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 2, 8].length) (baseStart_6840887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6840887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6840887 prefixEnd_6840887 := by exact prefixLift 6840887
  have htrace : WordTrace (prefixWord ++ tailWord_6840887) baseStart_6840887 baseEnd_6840887 := by
    simpa [prefixWord, tailWord_6840887, baseEnd_6840887] using wordTrace_append hprefix tailTrace_6840887
  have hstable : (prefixWord ++ tailWord_6840887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6840887).length < 2 ^ (prefixWord ++ tailWord_6840887).sum := by decide
  have hdescent : baseEnd_6840887 < baseStart_6840887 := by decide
  rcases family_descends (prefixWord ++ tailWord_6840887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6840907 : List Nat := [1, 1, 1, 1, 3, 1, 5, 1, 1, 2, 6]
def baseStart_6840907 : Nat := 118140960795 + 6840907 * 2 ^ 59
def prefixEnd_6840907 : Nat := 4983230072969 + 3 ^ 40 * 6840907 * 2
def baseEnd_6840907 : Nat := 3512673403706971653601747

theorem tailTrace_6840907 : CollatzResearch.WordTrace tailWord_6840907 prefixEnd_6840907 3512673403706971653601747 := by
  unfold tailWord_6840907
  simp only [CollatzResearch.WordTrace]
  refine ⟨249508376227569747744896975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166338917485046498496597983 249508376227569747744896975)
  ·
    refine ⟨374262564341354621617345463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249508376227569747744896975 374262564341354621617345463)
    ·
      refine ⟨561393846512031932426018195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374262564341354621617345463 561393846512031932426018195)
      ·
        refine ⟨842090769768047898639027293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 561393846512031932426018195 842090769768047898639027293)
        ·
          refine ⟨315784038663017961989635235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 842090769768047898639027293 315784038663017961989635235)
          ·
            refine ⟨473676057994526942984452853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315784038663017961989635235 473676057994526942984452853)
            ·
              refine ⟨44407130436986900904792455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 473676057994526942984452853 44407130436986900904792455)
              ·
                refine ⟨66610695655480351357188683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44407130436986900904792455 66610695655480351357188683)
                ·
                  refine ⟨99916043483220527035783025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66610695655480351357188683 99916043483220527035783025)
                  ·
                    refine ⟨74937032612415395276837269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 99916043483220527035783025 74937032612415395276837269)
                    ·
                      refine ⟨3512673403706971653601747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74937032612415395276837269 3512673403706971653601747)
                      ·
                        rfl

theorem cell23_6840907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 2, 6].length) (baseStart_6840907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6840907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6840907 prefixEnd_6840907 := by exact prefixLift 6840907
  have htrace : WordTrace (prefixWord ++ tailWord_6840907) baseStart_6840907 baseEnd_6840907 := by
    simpa [prefixWord, tailWord_6840907, baseEnd_6840907] using wordTrace_append hprefix tailTrace_6840907
  have hstable : (prefixWord ++ tailWord_6840907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6840907).length < 2 ^ (prefixWord ++ tailWord_6840907).sum := by decide
  have hdescent : baseEnd_6840907 < baseStart_6840907 := by decide
  rcases family_descends (prefixWord ++ tailWord_6840907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6840927 : List Nat := [1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 7]
def baseStart_6840927 : Nat := 118140960795 + 6840927 * 2 ^ 59
def prefixEnd_6840927 : Nat := 4983230072969 + 3 ^ 40 * 6840927 * 2
def baseEnd_6840927 : Nat := 3512683673320061575351655

theorem tailTrace_6840927 : CollatzResearch.WordTrace tailWord_6840927 prefixEnd_6840927 3512683673320061575351655 := by
  unfold tailWord_6840927
  simp only [CollatzResearch.WordTrace]
  refine ⟨249509105687497291160625035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166339403791664860773750023 249509105687497291160625035)
  ·
    refine ⟨374263658531245936740937553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249509105687497291160625035 374263658531245936740937553)
    ·
      refine ⟨280697743898434452555703165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 374263658531245936740937553 280697743898434452555703165)
      ·
        refine ⟨105261653961912919708388687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 280697743898434452555703165 105261653961912919708388687)
        ·
          refine ⟨157892480942869379562583031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105261653961912919708388687 157892480942869379562583031)
          ·
            refine ⟨236838721414304069343874547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157892480942869379562583031 236838721414304069343874547)
            ·
              refine ⟨355258082121456104015811821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 236838721414304069343874547 355258082121456104015811821)
              ·
                refine ⟨133221780795546039005929433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 355258082121456104015811821 133221780795546039005929433)
                ·
                  refine ⟨99916335596659529254447075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 133221780795546039005929433 99916335596659529254447075)
                  ·
                    refine ⟨149874503394989293881670613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 99916335596659529254447075 149874503394989293881670613)
                    ·
                      refine ⟨3512683673320061575351655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 149874503394989293881670613 3512683673320061575351655)
                      ·
                        rfl

theorem cell23_6840927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 7].length) (baseStart_6840927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6840927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6840927 prefixEnd_6840927 := by exact prefixLift 6840927
  have htrace : WordTrace (prefixWord ++ tailWord_6840927) baseStart_6840927 baseEnd_6840927 := by
    simpa [prefixWord, tailWord_6840927, baseEnd_6840927] using wordTrace_append hprefix tailTrace_6840927
  have hstable : (prefixWord ++ tailWord_6840927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6840927).length < 2 ^ (prefixWord ++ tailWord_6840927).sum := by decide
  have hdescent : baseEnd_6840927 < baseStart_6840927 := by decide
  rcases family_descends (prefixWord ++ tailWord_6840927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6840931 : List Nat := [1, 1, 1, 5, 1, 2, 1, 4, 3, 1, 3]
def baseStart_6840931 : Nat := 118140960795 + 6840931 * 2 ^ 59
def prefixEnd_6840931 : Nat := 4983230072969 + 3 ^ 40 * 6840931 * 2
def baseEnd_6840931 : Nat := 3512685727242679559701637

theorem tailTrace_6840931 : CollatzResearch.WordTrace tailWord_6840931 prefixEnd_6840931 3512685727242679559701637 := by
  unfold tailWord_6840931
  simp only [CollatzResearch.WordTrace]
  refine ⟨249509251579482799843770647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166339501052988533229180431 249509251579482799843770647)
  ·
    refine ⟨374263877369224199765655971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249509251579482799843770647 374263877369224199765655971)
    ·
      refine ⟨561395816053836299648483957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374263877369224199765655971 561395816053836299648483957)
      ·
        refine ⟨52630857755047153092045371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 561395816053836299648483957 52630857755047153092045371)
        ·
          refine ⟨78946286632570729638068057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52630857755047153092045371 78946286632570729638068057)
          ·
            refine ⟨59209714974428047228551043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78946286632570729638068057 59209714974428047228551043)
            ·
              refine ⟨88814572461642070842826565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59209714974428047228551043 88814572461642070842826565)
              ·
                refine ⟨16652732336557888283029981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88814572461642070842826565 16652732336557888283029981)
                ·
                  refine ⟨6244774626209208106136243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16652732336557888283029981 6244774626209208106136243)
                  ·
                    refine ⟨9367161939313812159204365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6244774626209208106136243 9367161939313812159204365)
                    ·
                      refine ⟨3512685727242679559701637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9367161939313812159204365 3512685727242679559701637)
                      ·
                        rfl

theorem cell23_6840931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 4, 3, 1, 3].length) (baseStart_6840931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6840931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6840931 prefixEnd_6840931 := by exact prefixLift 6840931
  have htrace : WordTrace (prefixWord ++ tailWord_6840931) baseStart_6840931 baseEnd_6840931 := by
    simpa [prefixWord, tailWord_6840931, baseEnd_6840931] using wordTrace_append hprefix tailTrace_6840931
  have hstable : (prefixWord ++ tailWord_6840931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6840931).length < 2 ^ (prefixWord ++ tailWord_6840931).sum := by decide
  have hdescent : baseEnd_6840931 < baseStart_6840931 := by decide
  rcases family_descends (prefixWord ++ tailWord_6840931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6840984 : List Nat := [2, 1, 2, 4, 1, 1, 1, 3, 1, 1, 6]
def baseStart_6840984 : Nat := 118140960795 + 6840984 * 2 ^ 59
def prefixEnd_6840984 : Nat := 4983230072969 + 3 ^ 40 * 6840984 * 2
def baseEnd_6840984 : Nat := 3512712941717367852338893

theorem tailTrace_6840984 : CollatzResearch.WordTrace tailWord_6840984 prefixEnd_6840984 3512712941717367852338893 := by
  unfold tailWord_6840984
  simp only [CollatzResearch.WordTrace]
  refine ⟨124755592324145394947725003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166340789765527193263633337 124755592324145394947725003)
  ·
    refine ⟨187133388486218092421587505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124755592324145394947725003 187133388486218092421587505)
    ·
      refine ⟨140350041364663569316190629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187133388486218092421587505 140350041364663569316190629)
      ·
        refine ⟨26315632755874419246785743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140350041364663569316190629 26315632755874419246785743)
        ·
          refine ⟨39473449133811628870178615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26315632755874419246785743 39473449133811628870178615)
          ·
            refine ⟨59210173700717443305267923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39473449133811628870178615 59210173700717443305267923)
            ·
              refine ⟨88815260551076164957901885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59210173700717443305267923 88815260551076164957901885)
              ·
                refine ⟨33305722706653561859213207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88815260551076164957901885 33305722706653561859213207)
                ·
                  refine ⟨49958584059980342788819811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33305722706653561859213207 49958584059980342788819811)
                  ·
                    refine ⟨74937876089970514183229717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49958584059980342788819811 74937876089970514183229717)
                    ·
                      refine ⟨3512712941717367852338893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74937876089970514183229717 3512712941717367852338893)
                      ·
                        rfl

theorem cell23_6840984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_6840984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6840984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6840984 prefixEnd_6840984 := by exact prefixLift 6840984
  have htrace : WordTrace (prefixWord ++ tailWord_6840984) baseStart_6840984 baseEnd_6840984 := by
    simpa [prefixWord, tailWord_6840984, baseEnd_6840984] using wordTrace_append hprefix tailTrace_6840984
  have hstable : (prefixWord ++ tailWord_6840984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6840984).length < 2 ^ (prefixWord ++ tailWord_6840984).sum := by decide
  have hdescent : baseEnd_6840984 < baseStart_6840984 := by decide
  rcases family_descends (prefixWord ++ tailWord_6840984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6840988 : List Nat := [2, 2, 3, 2, 2, 1, 3, 2, 1, 1, 4]
def baseStart_6840988 : Nat := 118140960795 + 6840988 * 2 ^ 59
def prefixEnd_6840988 : Nat := 4983230072969 + 3 ^ 40 * 6840988 * 2
def baseEnd_6840988 : Nat := 3512714995639985836688875

theorem tailTrace_6840988 : CollatzResearch.WordTrace tailWord_6840988 prefixEnd_6840988 3512714995639985836688875 := by
  unfold tailWord_6840988
  simp only [CollatzResearch.WordTrace]
  refine ⟨124755665270138149289297809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166340887026850865719063745 124755665270138149289297809)
  ·
    refine ⟨93566748952603611966973357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124755665270138149289297809 93566748952603611966973357)
    ·
      refine ⟨35087530857226354487615009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93566748952603611966973357 35087530857226354487615009)
      ·
        refine ⟨26315648142919765865711257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35087530857226354487615009 26315648142919765865711257)
        ·
          refine ⟨19736736107189824399283443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26315648142919765865711257 19736736107189824399283443)
          ·
            refine ⟨29605104160784736598925165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19736736107189824399283443 29605104160784736598925165)
            ·
              refine ⟨11101914060294276224596937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29605104160784736598925165 11101914060294276224596937)
              ·
                refine ⟨8326435545220707168447703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11101914060294276224596937 8326435545220707168447703)
                ·
                  refine ⟨12489653317831060752671555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8326435545220707168447703 12489653317831060752671555)
                  ·
                    refine ⟨18734479976746591129007333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12489653317831060752671555 18734479976746591129007333)
                    ·
                      refine ⟨3512714995639985836688875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18734479976746591129007333 3512714995639985836688875)
                      ·
                        rfl

theorem cell23_6840988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_6840988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6840988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6840988 prefixEnd_6840988 := by exact prefixLift 6840988
  have htrace : WordTrace (prefixWord ++ tailWord_6840988) baseStart_6840988 baseEnd_6840988 := by
    simpa [prefixWord, tailWord_6840988, baseEnd_6840988] using wordTrace_append hprefix tailTrace_6840988
  have hstable : (prefixWord ++ tailWord_6840988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6840988).length < 2 ^ (prefixWord ++ tailWord_6840988).sum := by decide
  have hdescent : baseEnd_6840988 < baseStart_6840988 := by decide
  rcases family_descends (prefixWord ++ tailWord_6840988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6841002 : List Nat := [3, 1, 5, 2, 1, 1, 3, 1, 1, 5]
def baseStart_6841002 : Nat := 118140960795 + 6841002 * 2 ^ 59
def prefixEnd_6841002 : Nat := 4983230072969 + 3 ^ 40 * 6841002 * 2
def baseEnd_6841002 : Nat := 1170907394789716260637937

theorem tailTrace_6841002 : CollatzResearch.WordTrace tailWord_6841002 prefixEnd_6841002 1170907394789716260637937 := by
  unfold tailWord_6841002
  simp only [CollatzResearch.WordTrace]
  refine ⟨62377960290556394742401315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166341227441483719313070173 62377960290556394742401315)
  ·
    refine ⟨93566940435834592113601973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62377960290556394742401315 93566940435834592113601973)
    ·
      refine ⟨8771900665859493010650185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 93566940435834592113601973 8771900665859493010650185)
      ·
        refine ⟨6578925499394619757987639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8771900665859493010650185 6578925499394619757987639)
        ·
          refine ⟨9868388249091929636981459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6578925499394619757987639 9868388249091929636981459)
          ·
            refine ⟨14802582373637894455472189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9868388249091929636981459 14802582373637894455472189)
            ·
              refine ⟨5550968390114210420802071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14802582373637894455472189 5550968390114210420802071)
              ·
                refine ⟨8326452585171315631203107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5550968390114210420802071 8326452585171315631203107)
                ·
                  refine ⟨12489678877756973446804661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8326452585171315631203107 12489678877756973446804661)
                  ·
                    refine ⟨1170907394789716260637937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12489678877756973446804661 1170907394789716260637937)
                    ·
                      rfl

theorem cell23_6841002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_6841002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6841002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6841002 prefixEnd_6841002 := by exact prefixLift 6841002
  have htrace : WordTrace (prefixWord ++ tailWord_6841002) baseStart_6841002 baseEnd_6841002 := by
    simpa [prefixWord, tailWord_6841002, baseEnd_6841002] using wordTrace_append hprefix tailTrace_6841002
  have hstable : (prefixWord ++ tailWord_6841002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6841002).length < 2 ^ (prefixWord ++ tailWord_6841002).sum := by decide
  have hdescent : baseEnd_6841002 < baseStart_6841002 := by decide
  rcases family_descends (prefixWord ++ tailWord_6841002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6841005 : List Nat := [1, 5, 2, 1, 1, 3, 3, 1, 1, 1, 4]
def baseStart_6841005 : Nat := 118140960795 + 6841005 * 2 ^ 59
def prefixEnd_6841005 : Nat := 4983230072969 + 3 ^ 40 * 6841005 * 2
def baseEnd_6841005 : Nat := 3512723724811112270176297

theorem tailTrace_6841005 : CollatzResearch.WordTrace tailWord_6841005 prefixEnd_6841005 3512723724811112270176297 := by
  unfold tailWord_6841005
  simp only [CollatzResearch.WordTrace]
  refine ⟨249511950581214710481964469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166341300387476473654642979 249511950581214710481964469)
  ·
    refine ⟨23391745366988879107684169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 249511950581214710481964469 23391745366988879107684169)
    ·
      refine ⟨17543809025241659330763127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23391745366988879107684169 17543809025241659330763127)
      ·
        refine ⟨26315713537862488996144691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17543809025241659330763127 26315713537862488996144691)
        ·
          refine ⟨39473570306793733494217037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26315713537862488996144691 39473570306793733494217037)
          ·
            refine ⟨14802588865047650060331389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39473570306793733494217037 14802588865047650060331389)
            ·
              refine ⟨5550970824392868772624271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14802588865047650060331389 5550970824392868772624271)
              ·
                refine ⟨8326456236589303158936407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5550970824392868772624271 8326456236589303158936407)
                ·
                  refine ⟨12489684354883954738404611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8326456236589303158936407 12489684354883954738404611)
                  ·
                    refine ⟨18734526532325932107606917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12489684354883954738404611 18734526532325932107606917)
                    ·
                      refine ⟨3512723724811112270176297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18734526532325932107606917 3512723724811112270176297)
                      ·
                        rfl

theorem cell23_6841005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 3, 1, 1, 1, 4].length) (baseStart_6841005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6841005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6841005 prefixEnd_6841005 := by exact prefixLift 6841005
  have htrace : WordTrace (prefixWord ++ tailWord_6841005) baseStart_6841005 baseEnd_6841005 := by
    simpa [prefixWord, tailWord_6841005, baseEnd_6841005] using wordTrace_append hprefix tailTrace_6841005
  have hstable : (prefixWord ++ tailWord_6841005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6841005).length < 2 ^ (prefixWord ++ tailWord_6841005).sum := by decide
  have hdescent : baseEnd_6841005 < baseStart_6841005 := by decide
  rcases family_descends (prefixWord ++ tailWord_6841005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6841022 : List Nat := [4, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2]
def baseStart_6841022 : Nat := 118140960795 + 6841022 * 2 ^ 59
def prefixEnd_6841022 : Nat := 4983230072969 + 3 ^ 40 * 6841022 * 2
def baseEnd_6841022 : Nat := 3512732453982238703663719

theorem tailTrace_6841022 : CollatzResearch.WordTrace tailWord_6841022 prefixEnd_6841022 3512732453982238703663719 := by
  unfold tailWord_6841022
  simp only [CollatzResearch.WordTrace]
  refine ⟨31189071327769140298166665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166341713748102081590222213 31189071327769140298166665)
  ·
    refine ⟨23391803495826855223624999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31189071327769140298166665 23391803495826855223624999)
    ·
      refine ⟨35087705243740282835437499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23391803495826855223624999 35087705243740282835437499)
      ·
        refine ⟨52631557865610424253156249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35087705243740282835437499 52631557865610424253156249)
        ·
          refine ⟨39473668399207818189867187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52631557865610424253156249 39473668399207818189867187)
          ·
            refine ⟨59210502598811727284800781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39473668399207818189867187 59210502598811727284800781)
            ·
              refine ⟨22203938474554397731800293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59210502598811727284800781 22203938474554397731800293)
              ·
                refine ⟨4163238463978949574712555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22203938474554397731800293 4163238463978949574712555)
                ·
                  refine ⟨6244857695968424362068833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4163238463978949574712555 6244857695968424362068833)
                  ·
                    refine ⟨4683643271976318271551625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6244857695968424362068833 4683643271976318271551625)
                    ·
                      refine ⟨3512732453982238703663719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4683643271976318271551625 3512732453982238703663719)
                      ·
                        rfl

theorem cell23_6841022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2].length) (baseStart_6841022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6841022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6841022 prefixEnd_6841022 := by exact prefixLift 6841022
  have htrace : WordTrace (prefixWord ++ tailWord_6841022) baseStart_6841022 baseEnd_6841022 := by
    simpa [prefixWord, tailWord_6841022, baseEnd_6841022] using wordTrace_append hprefix tailTrace_6841022
  have hstable : (prefixWord ++ tailWord_6841022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6841022).length < 2 ^ (prefixWord ++ tailWord_6841022).sum := by decide
  have hdescent : baseEnd_6841022 < baseStart_6841022 := by decide
  rcases family_descends (prefixWord ++ tailWord_6841022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6841024 : List Nat := [2, 1, 1, 2, 4, 2, 1, 1, 2, 7]
def baseStart_6841024 : Nat := 118140960795 + 6841024 * 2 ^ 59
def prefixEnd_6841024 : Nat := 4983230072969 + 3 ^ 40 * 6841024 * 2
def baseEnd_6841024 : Nat := 1170911160314515898612903

theorem tailTrace_6841024 : CollatzResearch.WordTrace tailWord_6841024 prefixEnd_6841024 1170911160314515898612903 := by
  unfold tailWord_6841024
  simp only [CollatzResearch.WordTrace]
  refine ⟨124756321784072938363453063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166341762378763917817937417 124756321784072938363453063)
  ·
    refine ⟨187134482676109407545179595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124756321784072938363453063 187134482676109407545179595)
    ·
      refine ⟨280701724014164111317769393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187134482676109407545179595 280701724014164111317769393)
      ·
        refine ⟨210526293010623083488327045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280701724014164111317769393 210526293010623083488327045)
        ·
          refine ⟨39473679939491828154061321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 210526293010623083488327045 39473679939491828154061321)
          ·
            refine ⟨29605259954618871115545991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39473679939491828154061321 29605259954618871115545991)
            ·
              refine ⟨44407889931928306673318987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29605259954618871115545991 44407889931928306673318987)
              ·
                refine ⟨66611834897892460009978481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44407889931928306673318987 66611834897892460009978481)
                ·
                  refine ⟨49958876173419345007483861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66611834897892460009978481 49958876173419345007483861)
                  ·
                    refine ⟨1170911160314515898612903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49958876173419345007483861 1170911160314515898612903)
                    ·
                      rfl

theorem cell23_6841024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 2, 7].length) (baseStart_6841024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6841024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6841024 prefixEnd_6841024 := by exact prefixLift 6841024
  have htrace : WordTrace (prefixWord ++ tailWord_6841024) baseStart_6841024 baseEnd_6841024 := by
    simpa [prefixWord, tailWord_6841024, baseEnd_6841024] using wordTrace_append hprefix tailTrace_6841024
  have hstable : (prefixWord ++ tailWord_6841024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6841024).length < 2 ^ (prefixWord ++ tailWord_6841024).sum := by decide
  have hdescent : baseEnd_6841024 < baseStart_6841024 := by decide
  rcases family_descends (prefixWord ++ tailWord_6841024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6841038 : List Nat := [4, 1, 1, 1, 3, 3, 2, 1, 1, 3, 3]
def baseStart_6841038 : Nat := 118140960795 + 6841038 * 2 ^ 59
def prefixEnd_6841038 : Nat := 4983230072969 + 3 ^ 40 * 6841038 * 2
def baseEnd_6841038 : Nat := 3512740669672710641063645

theorem tailTrace_6841038 : CollatzResearch.WordTrace tailWord_6841038 prefixEnd_6841038 3512740669672710641063645 := by
  unfold tailWord_6841038
  simp only [CollatzResearch.WordTrace]
  refine ⟨31189144273761894639739471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166342102793396771411943845 31189144273761894639739471)
  ·
    refine ⟨46783716410642841959609207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31189144273761894639739471 46783716410642841959609207)
    ·
      refine ⟨70175574615964262939413811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46783716410642841959609207 70175574615964262939413811)
      ·
        refine ⟨105263361923946394409120717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70175574615964262939413811 105263361923946394409120717)
        ·
          refine ⟨39473760721479897903420269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105263361923946394409120717 39473760721479897903420269)
          ·
            refine ⟨14802660270554961713782601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39473760721479897903420269 14802660270554961713782601)
            ·
              refine ⟨11101995202916221285336951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14802660270554961713782601 11101995202916221285336951)
              ·
                refine ⟨16652992804374331928005427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11101995202916221285336951 16652992804374331928005427)
                ·
                  refine ⟨24979489206561497892008141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16652992804374331928005427 24979489206561497892008141)
                  ·
                    refine ⟨9367308452460561709503053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24979489206561497892008141 9367308452460561709503053)
                    ·
                      refine ⟨3512740669672710641063645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9367308452460561709503053 3512740669672710641063645)
                      ·
                        rfl

theorem cell23_6841038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 1, 1, 3, 3].length) (baseStart_6841038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6841038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6841038 prefixEnd_6841038 := by exact prefixLift 6841038
  have htrace : WordTrace (prefixWord ++ tailWord_6841038) baseStart_6841038 baseEnd_6841038 := by
    simpa [prefixWord, tailWord_6841038, baseEnd_6841038] using wordTrace_append hprefix tailTrace_6841038
  have hstable : (prefixWord ++ tailWord_6841038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6841038).length < 2 ^ (prefixWord ++ tailWord_6841038).sum := by decide
  have hdescent : baseEnd_6841038 < baseStart_6841038 := by decide
  rcases family_descends (prefixWord ++ tailWord_6841038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6841048 : List Nat := [2, 1, 2, 2, 3, 2, 2, 1, 3, 3, 2]
def baseStart_6841048 : Nat := 118140960795 + 6841048 * 2 ^ 59
def prefixEnd_6841048 : Nat := 4983230072969 + 3 ^ 40 * 6841048 * 2
def baseEnd_6841048 : Nat := 3512745804479255601938599

theorem tailTrace_6841048 : CollatzResearch.WordTrace tailWord_6841048 prefixEnd_6841048 3512745804479255601938599 := by
  unfold tailWord_6841048
  simp only [CollatzResearch.WordTrace]
  refine ⟨124756759460029464412889899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166342345946705952550519865 124756759460029464412889899)
  ·
    refine ⟨187135139190044196619334849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124756759460029464412889899 187135139190044196619334849)
    ·
      refine ⟨140351354392533147464501137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187135139190044196619334849 140351354392533147464501137)
      ·
        refine ⟨105263515794399860598375853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140351354392533147464501137 105263515794399860598375853)
        ·
          refine ⟨39473818422899947724390945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105263515794399860598375853 39473818422899947724390945)
          ·
            refine ⟨29605363817174960793293209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39473818422899947724390945 29605363817174960793293209)
            ·
              refine ⟨22204022862881220594969907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29605363817174960793293209 22204022862881220594969907)
              ·
                refine ⟨33306034294321830892454861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22204022862881220594969907 33306034294321830892454861)
                ·
                  refine ⟨12489762860370686584670573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33306034294321830892454861 12489762860370686584670573)
                  ·
                    refine ⟨4683661072639007469251465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12489762860370686584670573 4683661072639007469251465)
                    ·
                      refine ⟨3512745804479255601938599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4683661072639007469251465 3512745804479255601938599)
                      ·
                        rfl

theorem cell23_6841048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 1, 3, 3, 2].length) (baseStart_6841048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6841048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6841048 prefixEnd_6841048 := by exact prefixLift 6841048
  have htrace : WordTrace (prefixWord ++ tailWord_6841048) baseStart_6841048 baseEnd_6841048 := by
    simpa [prefixWord, tailWord_6841048, baseEnd_6841048] using wordTrace_append hprefix tailTrace_6841048
  have hstable : (prefixWord ++ tailWord_6841048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6841048).length < 2 ^ (prefixWord ++ tailWord_6841048).sum := by decide
  have hdescent : baseEnd_6841048 < baseStart_6841048 := by decide
  rcases family_descends (prefixWord ++ tailWord_6841048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6841065 : List Nat := [1, 2, 1, 1, 1, 2, 8, 1, 1, 3, 2]
def baseStart_6841065 : Nat := 118140960795 + 6841065 * 2 ^ 59
def prefixEnd_6841065 : Nat := 4983230072969 + 3 ^ 40 * 6841065 * 2
def baseEnd_6841065 : Nat := 3512754533650382035426021

theorem tailTrace_6841065 : CollatzResearch.WordTrace tailWord_6841065 prefixEnd_6841065 3512754533650382035426021 := by
  unfold tailWord_6841065
  simp only [CollatzResearch.WordTrace]
  refine ⟨249514138960997340729148649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166342759307331560486099099 249514138960997340729148649)
  ·
    refine ⟨187135604220748005546861487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249514138960997340729148649 187135604220748005546861487)
    ·
      refine ⟨280703406331122008320292231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187135604220748005546861487 280703406331122008320292231)
      ·
        refine ⟨421055109496683012480438347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280703406331122008320292231 421055109496683012480438347)
        ·
          refine ⟨631582664245024518720657521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 421055109496683012480438347 631582664245024518720657521)
          ·
            refine ⟨473686998183768389040493141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 631582664245024518720657521 473686998183768389040493141)
            ·
              refine ⟨5551019509966035809068279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 473686998183768389040493141 5551019509966035809068279)
              ·
                refine ⟨8326529264949053713602419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5551019509966035809068279 8326529264949053713602419)
                ·
                  refine ⟨12489793897423580570403629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8326529264949053713602419 12489793897423580570403629)
                  ·
                    refine ⟨4683672711533842713901361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12489793897423580570403629 4683672711533842713901361)
                    ·
                      refine ⟨3512754533650382035426021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4683672711533842713901361 3512754533650382035426021)
                      ·
                        rfl

theorem cell23_6841065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 8, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 8, 1, 1, 3, 2].length) (baseStart_6841065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6841065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6841065 prefixEnd_6841065 := by exact prefixLift 6841065
  have htrace : WordTrace (prefixWord ++ tailWord_6841065) baseStart_6841065 baseEnd_6841065 := by
    simpa [prefixWord, tailWord_6841065, baseEnd_6841065] using wordTrace_append hprefix tailTrace_6841065
  have hstable : (prefixWord ++ tailWord_6841065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6841065).length < 2 ^ (prefixWord ++ tailWord_6841065).sum := by decide
  have hdescent : baseEnd_6841065 < baseStart_6841065 := by decide
  rcases family_descends (prefixWord ++ tailWord_6841065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6841095 : List Nat := [1, 1, 4, 4, 1, 1, 3, 1, 1, 4, 2]
def baseStart_6841095 : Nat := 118140960795 + 6841095 * 2 ^ 59
def prefixEnd_6841095 : Nat := 4983230072969 + 3 ^ 40 * 6841095 * 2
def baseEnd_6841095 : Nat := 3512769938070016918050883

theorem tailTrace_6841095 : CollatzResearch.WordTrace tailWord_6841095 prefixEnd_6841095 3512769938070016918050883 := by
  unfold tailWord_6841095
  simp only [CollatzResearch.WordTrace]
  refine ⟨249515233150888655852740739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166343488767259103901827159 249515233150888655852740739)
  ·
    refine ⟨374272849726332983779111109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249515233150888655852740739 374272849726332983779111109)
    ·
      refine ⟨70176159323687434458583333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 374272849726332983779111109 70176159323687434458583333)
      ·
        refine ⟨13158029873191393960984375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70176159323687434458583333 13158029873191393960984375)
        ·
          refine ⟨19737044809787090941476563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13158029873191393960984375 19737044809787090941476563)
          ·
            refine ⟨29605567214680636412214845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19737044809787090941476563 29605567214680636412214845)
            ·
              refine ⟨11102087705505238654580567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29605567214680636412214845 11102087705505238654580567)
              ·
                refine ⟨16653131558257857981870851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11102087705505238654580567 16653131558257857981870851)
                ·
                  refine ⟨24979697337386786972806277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16653131558257857981870851 24979697337386786972806277)
                  ·
                    refine ⟨4683693250760022557401177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24979697337386786972806277 4683693250760022557401177)
                    ·
                      refine ⟨3512769938070016918050883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4683693250760022557401177 3512769938070016918050883)
                      ·
                        rfl

theorem cell23_6841095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_6841095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6841095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6841095 prefixEnd_6841095 := by exact prefixLift 6841095
  have htrace : WordTrace (prefixWord ++ tailWord_6841095) baseStart_6841095 baseEnd_6841095 := by
    simpa [prefixWord, tailWord_6841095, baseEnd_6841095] using wordTrace_append hprefix tailTrace_6841095
  have hstable : (prefixWord ++ tailWord_6841095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6841095).length < 2 ^ (prefixWord ++ tailWord_6841095).sum := by decide
  have hdescent : baseEnd_6841095 < baseStart_6841095 := by decide
  rcases family_descends (prefixWord ++ tailWord_6841095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6841138 : List Nat := [3, 2, 1, 1, 3, 1, 2, 1, 2, 5, 2]
def baseStart_6841138 : Nat := 118140960795 + 6841138 * 2 ^ 59
def prefixEnd_6841138 : Nat := 4983230072969 + 3 ^ 40 * 6841138 * 2
def baseEnd_6841138 : Nat := 3512792017738160249813185

theorem tailTrace_6841138 : CollatzResearch.WordTrace tailWord_6841138 prefixEnd_6841138 3512792017738160249813185 := by
  unfold tailWord_6841138
  simp only [CollatzResearch.WordTrace]
  refine ⟨62379200372433218549139017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166344534326488582797704045 62379200372433218549139017)
  ·
    refine ⟨46784400279324913911854263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62379200372433218549139017 46784400279324913911854263)
    ·
      refine ⟨70176600418987370867781395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46784400279324913911854263 70176600418987370867781395)
      ·
        refine ⟨105264900628481056301672093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70176600418987370867781395 105264900628481056301672093)
        ·
          refine ⟨39474337735680396113127035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105264900628481056301672093 39474337735680396113127035)
          ·
            refine ⟨59211506603520594169690553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39474337735680396113127035 59211506603520594169690553)
            ·
              refine ⟨44408629952640445627267915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59211506603520594169690553 44408629952640445627267915)
              ·
                refine ⟨66612944928960668440901873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44408629952640445627267915 66612944928960668440901873)
                ·
                  refine ⟨49959708696720501330676405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66612944928960668440901873 49959708696720501330676405)
                  ·
                    refine ⟨4683722690317546999750913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49959708696720501330676405 4683722690317546999750913)
                    ·
                      refine ⟨3512792017738160249813185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4683722690317546999750913 3512792017738160249813185)
                      ·
                        rfl

theorem cell23_6841138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 2, 5, 2].length) (baseStart_6841138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6841138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6841138 prefixEnd_6841138 := by exact prefixLift 6841138
  have htrace : WordTrace (prefixWord ++ tailWord_6841138) baseStart_6841138 baseEnd_6841138 := by
    simpa [prefixWord, tailWord_6841138, baseEnd_6841138] using wordTrace_append hprefix tailTrace_6841138
  have hstable : (prefixWord ++ tailWord_6841138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6841138).length < 2 ^ (prefixWord ++ tailWord_6841138).sum := by decide
  have hdescent : baseEnd_6841138 < baseStart_6841138 := by decide
  rcases family_descends (prefixWord ++ tailWord_6841138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6841141 : List Nat := [1, 3, 3, 1, 3, 1, 1, 1, 1, 1, 7]
def baseStart_6841141 : Nat := 118140960795 + 6841141 * 2 ^ 59
def prefixEnd_6841141 : Nat := 4983230072969 + 3 ^ 40 * 6841141 * 2
def baseEnd_6841141 : Nat := 3512793558180123738075671

theorem tailTrace_6841141 : CollatzResearch.WordTrace tailWord_6841141 prefixEnd_6841141 3512793558180123738075671 := by
  unfold tailWord_6841141
  simp only [CollatzResearch.WordTrace]
  refine ⟨249516910908722005708915277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166344607272481337139276851 249516910908722005708915277)
  ·
    refine ⟨93568841590770752140843229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249516910908722005708915277 93568841590770752140843229)
    ·
      refine ⟨35088315596539032052816211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93568841590770752140843229 35088315596539032052816211)
      ·
        refine ⟨52632473394808548079224317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35088315596539032052816211 52632473394808548079224317)
        ·
          refine ⟨19737177523053205529709119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52632473394808548079224317 19737177523053205529709119)
          ·
            refine ⟨29605766284579808294563679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19737177523053205529709119 29605766284579808294563679)
            ·
              refine ⟨44408649426869712441845519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29605766284579808294563679 44408649426869712441845519)
              ·
                refine ⟨66612974140304568662768279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44408649426869712441845519 66612974140304568662768279)
                ·
                  refine ⟨99919461210456852994152419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66612974140304568662768279 99919461210456852994152419)
                  ·
                    refine ⟨149879191815685279491228629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 99919461210456852994152419 149879191815685279491228629)
                    ·
                      refine ⟨3512793558180123738075671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 149879191815685279491228629 3512793558180123738075671)
                      ·
                        rfl

theorem cell23_6841141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_6841141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6841141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6841141 prefixEnd_6841141 := by exact prefixLift 6841141
  have htrace : WordTrace (prefixWord ++ tailWord_6841141) baseStart_6841141 baseEnd_6841141 := by
    simpa [prefixWord, tailWord_6841141, baseEnd_6841141] using wordTrace_append hprefix tailTrace_6841141
  have hstable : (prefixWord ++ tailWord_6841141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6841141).length < 2 ^ (prefixWord ++ tailWord_6841141).sum := by decide
  have hdescent : baseEnd_6841141 < baseStart_6841141 := by decide
  rcases family_descends (prefixWord ++ tailWord_6841141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6841146 : List Nat := [3, 1, 1, 1, 7, 1, 2, 1, 2, 2, 2]
def baseStart_6841146 : Nat := 118140960795 + 6841146 * 2 ^ 59
def prefixEnd_6841146 : Nat := 4983230072969 + 3 ^ 40 * 6841146 * 2
def baseEnd_6841146 : Nat := 3512796125583396218513149

theorem tailTrace_6841146 : CollatzResearch.WordTrace tailWord_6841146 prefixEnd_6841146 3512796125583396218513149 := by
  unfold tailWord_6841146
  simp only [CollatzResearch.WordTrace]
  refine ⟨62379273318425972890711823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166344728849135927708564861 62379273318425972890711823)
  ·
    refine ⟨93568909977638959336067735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62379273318425972890711823 93568909977638959336067735)
    ·
      refine ⟨140353364966458439004101603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93568909977638959336067735 140353364966458439004101603)
      ·
        refine ⟨210530047449687658506152405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140353364966458439004101603 210530047449687658506152405)
        ·
          refine ⟨4934297987102054496237947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 210530047449687658506152405 4934297987102054496237947)
          ·
            refine ⟨7401446980653081744356921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4934297987102054496237947 7401446980653081744356921)
            ·
              refine ⟨5551085235489811308267691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7401446980653081744356921 5551085235489811308267691)
              ·
                refine ⟨8326627853234716962401537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5551085235489811308267691 8326627853234716962401537)
                ·
                  refine ⟨6244970889926037721801153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8326627853234716962401537 6244970889926037721801153)
                  ·
                    refine ⟨4683728167444528291350865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6244970889926037721801153 4683728167444528291350865)
                    ·
                      refine ⟨3512796125583396218513149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4683728167444528291350865 3512796125583396218513149)
                      ·
                        rfl

theorem cell23_6841146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 2, 1, 2, 2, 2].length) (baseStart_6841146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6841146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6841146 prefixEnd_6841146 := by exact prefixLift 6841146
  have htrace : WordTrace (prefixWord ++ tailWord_6841146) baseStart_6841146 baseEnd_6841146 := by
    simpa [prefixWord, tailWord_6841146, baseEnd_6841146] using wordTrace_append hprefix tailTrace_6841146
  have hstable : (prefixWord ++ tailWord_6841146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6841146).length < 2 ^ (prefixWord ++ tailWord_6841146).sum := by decide
  have hdescent : baseEnd_6841146 < baseStart_6841146 := by decide
  rcases family_descends (prefixWord ++ tailWord_6841146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6841171 : List Nat := [1, 1, 1, 2, 1, 1, 3, 5, 1, 4, 3]
def baseStart_6841171 : Nat := 118140960795 + 6841171 * 2 ^ 59
def prefixEnd_6841171 : Nat := 4983230072969 + 3 ^ 40 * 6841171 * 2
def baseEnd_6841171 : Nat := 3512808962599758620700533

theorem tailTrace_6841171 : CollatzResearch.WordTrace tailWord_6841171 prefixEnd_6841171 3512808962599758620700533 := by
  unfold tailWord_6841171
  simp only [CollatzResearch.WordTrace]
  refine ⟨249518005098613320832507367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166345336732408880555004911 249518005098613320832507367)
  ·
    refine ⟨374277007647919981248761051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249518005098613320832507367 374277007647919981248761051)
    ·
      refine ⟨561415511471879971873141577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374277007647919981248761051 561415511471879971873141577)
      ·
        refine ⟨421061633603909978904856183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 561415511471879971873141577 421061633603909978904856183)
        ·
          refine ⟨631592450405864968357284275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 421061633603909978904856183 631592450405864968357284275)
          ·
            refine ⟨947388675608797452535926413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 631592450405864968357284275 947388675608797452535926413)
            ·
              refine ⟨355270753353299044700972405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 947388675608797452535926413 355270753353299044700972405)
              ·
                refine ⟨33306633126871785440716163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 355270753353299044700972405 33306633126871785440716163)
                ·
                  refine ⟨49959949690307678161074245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33306633126871785440716163 49959949690307678161074245)
                  ·
                    refine ⟨9367490566932689655201421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49959949690307678161074245 9367490566932689655201421)
                    ·
                      refine ⟨3512808962599758620700533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9367490566932689655201421 3512808962599758620700533)
                      ·
                        rfl

theorem cell23_6841171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 5, 1, 4, 3].length) (baseStart_6841171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6841171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6841171 prefixEnd_6841171 := by exact prefixLift 6841171
  have htrace : WordTrace (prefixWord ++ tailWord_6841171) baseStart_6841171 baseEnd_6841171 := by
    simpa [prefixWord, tailWord_6841171, baseEnd_6841171] using wordTrace_append hprefix tailTrace_6841171
  have hstable : (prefixWord ++ tailWord_6841171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6841171).length < 2 ^ (prefixWord ++ tailWord_6841171).sum := by decide
  have hdescent : baseEnd_6841171 < baseStart_6841171 := by decide
  rcases family_descends (prefixWord ++ tailWord_6841171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6841242 : List Nat := [3, 1, 1, 4, 4, 1, 1, 2, 6]
def baseStart_6841242 : Nat := 118140960795 + 6841242 * 2 ^ 59
def prefixEnd_6841242 : Nat := 4983230072969 + 3 ^ 40 * 6841242 * 2
def baseEnd_6841242 : Nat := 390316157747358649212523

theorem tailTrace_6841242 : CollatzResearch.WordTrace tailWord_6841242 prefixEnd_6841242 390316157747358649212523 := by
  unfold tailWord_6841242
  simp only [CollatzResearch.WordTrace]
  refine ⟨62380148670339024989585495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166347063120904066638894653 62380148670339024989585495)
  ·
    refine ⟨93570223005508537484378243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62380148670339024989585495 93570223005508537484378243)
    ·
      refine ⟨140355334508262806226567365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93570223005508537484378243 140355334508262806226567365)
      ·
        refine ⟨26316625220299276167481381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140355334508262806226567365 26316625220299276167481381)
        ·
          refine ⟨4934367228806114281402759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26316625220299276167481381 4934367228806114281402759)
          ·
            refine ⟨7401550843209171422104139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4934367228806114281402759 7401550843209171422104139)
            ·
              refine ⟨11102326264813757133156209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7401550843209171422104139 11102326264813757133156209)
              ·
                refine ⟨8326744698610317849867157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11102326264813757133156209 8326744698610317849867157)
                ·
                  refine ⟨390316157747358649212523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8326744698610317849867157 390316157747358649212523)
                  ·
                    rfl

theorem cell23_6841242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 2, 6].length) (baseStart_6841242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6841242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6841242 prefixEnd_6841242 := by exact prefixLift 6841242
  have htrace : WordTrace (prefixWord ++ tailWord_6841242) baseStart_6841242 baseEnd_6841242 := by
    simpa [prefixWord, tailWord_6841242, baseEnd_6841242] using wordTrace_append hprefix tailTrace_6841242
  have hstable : (prefixWord ++ tailWord_6841242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6841242).length < 2 ^ (prefixWord ++ tailWord_6841242).sum := by decide
  have hdescent : baseEnd_6841242 < baseStart_6841242 := by decide
  rcases family_descends (prefixWord ++ tailWord_6841242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6841245 : List Nat := [1, 4, 2, 1, 2, 1, 2, 1, 4, 3, 2]
def baseStart_6841245 : Nat := 118140960795 + 6841245 * 2 ^ 59
def prefixEnd_6841245 : Nat := 4983230072969 + 3 ^ 40 * 6841245 * 2
def baseEnd_6841245 : Nat := 3512846960168191331175193

theorem tailTrace_6841245 : CollatzResearch.WordTrace tailWord_6841245 prefixEnd_6841245 3512846960168191331175193 := by
  unfold tailWord_6841245
  simp only [CollatzResearch.WordTrace]
  refine ⟨249520704100345231470701189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166347136066896820980467459 249520704100345231470701189)
  ·
    refine ⟨46785132018814730900756473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 249520704100345231470701189 46785132018814730900756473)
    ·
      refine ⟨35088849014111048175567355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46785132018814730900756473 35088849014111048175567355)
      ·
        refine ⟨52633273521166572263351033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35088849014111048175567355 52633273521166572263351033)
        ·
          refine ⟨39474955140874929197513275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52633273521166572263351033 39474955140874929197513275)
          ·
            refine ⟨59212432711312393796269913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39474955140874929197513275 59212432711312393796269913)
            ·
              refine ⟨44409324533484295347202435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59212432711312393796269913 44409324533484295347202435)
              ·
                refine ⟨66613986800226443020803653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44409324533484295347202435 66613986800226443020803653)
                ·
                  refine ⟨12490122525042458066400685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66613986800226443020803653 12490122525042458066400685)
                  ·
                    refine ⟨4683795946890921774900257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12490122525042458066400685 4683795946890921774900257)
                    ·
                      refine ⟨3512846960168191331175193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4683795946890921774900257 3512846960168191331175193)
                      ·
                        rfl

theorem cell23_6841245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 4, 3, 2].length) (baseStart_6841245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6841245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6841245 prefixEnd_6841245 := by exact prefixLift 6841245
  have htrace : WordTrace (prefixWord ++ tailWord_6841245) baseStart_6841245 baseEnd_6841245 := by
    simpa [prefixWord, tailWord_6841245, baseEnd_6841245] using wordTrace_append hprefix tailTrace_6841245
  have hstable : (prefixWord ++ tailWord_6841245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6841245).length < 2 ^ (prefixWord ++ tailWord_6841245).sum := by decide
  have hdescent : baseEnd_6841245 < baseStart_6841245 := by decide
  rcases family_descends (prefixWord ++ tailWord_6841245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6841251 : List Nat := [1, 1, 1, 4, 1, 2, 2, 2, 3, 6]
def baseStart_6841251 : Nat := 118140960795 + 6841251 * 2 ^ 59
def prefixEnd_6841251 : Nat := 4983230072969 + 3 ^ 40 * 6841251 * 2
def baseEnd_6841251 : Nat := 1170950013684039435900055

theorem tailTrace_6841251 : CollatzResearch.WordTrace tailWord_6841251 prefixEnd_6841251 1170950013684039435900055 := by
  unfold tailWord_6841251
  simp only [CollatzResearch.WordTrace]
  refine ⟨249520922938323494495419607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166347281958882329663613071 249520922938323494495419607)
  ·
    refine ⟨374281384407485241743129411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249520922938323494495419607 374281384407485241743129411)
    ·
      refine ⟨561422076611227862614694117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374281384407485241743129411 561422076611227862614694117)
      ·
        refine ⟨105266639364605224240255147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 561422076611227862614694117 105266639364605224240255147)
        ·
          refine ⟨157899959046907836360382721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105266639364605224240255147 157899959046907836360382721)
          ·
            refine ⟨118424969285180877270287041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157899959046907836360382721 118424969285180877270287041)
            ·
              refine ⟨88818726963885657952715281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118424969285180877270287041 88818726963885657952715281)
              ·
                refine ⟨66614045222914243464536461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88818726963885657952715281 66614045222914243464536461)
                ·
                  refine ⟨24980266958592841299201173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66614045222914243464536461 24980266958592841299201173)
                  ·
                    refine ⟨1170950013684039435900055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24980266958592841299201173 1170950013684039435900055)
                    ·
                      rfl

theorem cell23_6841251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 3, 6].length) (baseStart_6841251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6841251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6841251 prefixEnd_6841251 := by exact prefixLift 6841251
  have htrace : WordTrace (prefixWord ++ tailWord_6841251) baseStart_6841251 baseEnd_6841251 := by
    simpa [prefixWord, tailWord_6841251, baseEnd_6841251] using wordTrace_append hprefix tailTrace_6841251
  have hstable : (prefixWord ++ tailWord_6841251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6841251).length < 2 ^ (prefixWord ++ tailWord_6841251).sum := by decide
  have hdescent : baseEnd_6841251 < baseStart_6841251 := by decide
  rcases family_descends (prefixWord ++ tailWord_6841251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6841252 : List Nat := [2, 3, 1, 2, 1, 2, 1, 6, 1, 1, 3]
def baseStart_6841252 : Nat := 118140960795 + 6841252 * 2 ^ 59
def prefixEnd_6841252 : Nat := 4983230072969 + 3 ^ 40 * 6841252 * 2
def baseEnd_6841252 : Nat := 3512850554532772803787661

theorem tailTrace_6841252 : CollatzResearch.WordTrace tailWord_6841252 prefixEnd_6841252 3512850554532772803787661 := by
  unfold tailWord_6841252
  simp only [CollatzResearch.WordTrace]
  refine ⟨124760479705659935833103005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166347306274213247777470673 124760479705659935833103005)
  ·
    refine ⟨46785179889622475937413627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124760479705659935833103005 46785179889622475937413627)
    ·
      refine ⟨70177769834433713906120441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46785179889622475937413627 70177769834433713906120441)
      ·
        refine ⟨52633327375825285429590331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70177769834433713906120441 52633327375825285429590331)
        ·
          refine ⟨78949991063737928144385497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52633327375825285429590331 78949991063737928144385497)
          ·
            refine ⟨59212493297803446108289123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78949991063737928144385497 59212493297803446108289123)
            ·
              refine ⟨88818739946705169162433685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59212493297803446108289123 88818739946705169162433685)
              ·
                refine ⟨4163378435001804804489079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 88818739946705169162433685 4163378435001804804489079)
                ·
                  refine ⟨6245067652502707206733619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4163378435001804804489079 6245067652502707206733619)
                  ·
                    refine ⟨9367601478754060810100429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6245067652502707206733619 9367601478754060810100429)
                    ·
                      refine ⟨3512850554532772803787661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9367601478754060810100429 3512850554532772803787661)
                      ·
                        rfl

theorem cell23_6841252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 6, 1, 1, 3].length) (baseStart_6841252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6841252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6841252 prefixEnd_6841252 := by exact prefixLift 6841252
  have htrace : WordTrace (prefixWord ++ tailWord_6841252) baseStart_6841252 baseEnd_6841252 := by
    simpa [prefixWord, tailWord_6841252, baseEnd_6841252] using wordTrace_append hprefix tailTrace_6841252
  have hstable : (prefixWord ++ tailWord_6841252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6841252).length < 2 ^ (prefixWord ++ tailWord_6841252).sum := by decide
  have hdescent : baseEnd_6841252 < baseStart_6841252 := by decide
  rcases family_descends (prefixWord ++ tailWord_6841252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6841278 : List Nat := [4, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5]
def baseStart_6841278 : Nat := 118140960795 + 6841278 * 2 ^ 59
def prefixEnd_6841278 : Nat := 4983230072969 + 3 ^ 40 * 6841278 * 2
def baseEnd_6841278 : Nat := 3512863905029789702062541

theorem tailTrace_6841278 : CollatzResearch.WordTrace tailWord_6841278 prefixEnd_6841278 3512863905029789702062541 := by
  unfold tailWord_6841278
  simp only [CollatzResearch.WordTrace]
  refine ⟨31190238463653209763331561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166347938472817118737768325 31190238463653209763331561)
  ·
    refine ⟨23392678847739907322498671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31190238463653209763331561 23392678847739907322498671)
    ·
      refine ⟨35089018271609860983748007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23392678847739907322498671 35089018271609860983748007)
      ·
        refine ⟨52633527407414791475622011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35089018271609860983748007 52633527407414791475622011)
        ·
          refine ⟨78950291111122187213433017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52633527407414791475622011 78950291111122187213433017)
          ·
            refine ⟨59212718333341640410074763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78950291111122187213433017 59212718333341640410074763)
            ·
              refine ⟨88819077500012460615112145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59212718333341640410074763 88819077500012460615112145)
              ·
                refine ⟨66614308125009345461334109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88819077500012460615112145 66614308125009345461334109)
                ·
                  refine ⟨24980365546878504548000291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66614308125009345461334109 24980365546878504548000291)
                  ·
                    refine ⟨37470548320317756822000437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24980365546878504548000291 37470548320317756822000437)
                    ·
                      refine ⟨3512863905029789702062541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37470548320317756822000437 3512863905029789702062541)
                      ·
                        rfl

theorem cell23_6841278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_6841278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6841278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6841278 prefixEnd_6841278 := by exact prefixLift 6841278
  have htrace : WordTrace (prefixWord ++ tailWord_6841278) baseStart_6841278 baseEnd_6841278 := by
    simpa [prefixWord, tailWord_6841278, baseEnd_6841278] using wordTrace_append hprefix tailTrace_6841278
  have hstable : (prefixWord ++ tailWord_6841278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6841278).length < 2 ^ (prefixWord ++ tailWord_6841278).sum := by decide
  have hdescent : baseEnd_6841278 < baseStart_6841278 := by decide
  rcases family_descends (prefixWord ++ tailWord_6841278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6841295 : List Nat := [1, 1, 2, 1, 1, 6, 2, 3, 1, 2, 3]
def baseStart_6841295 : Nat := 118140960795 + 6841295 * 2 ^ 59
def prefixEnd_6841295 : Nat := 4983230072969 + 3 ^ 40 * 6841295 * 2
def baseEnd_6841295 : Nat := 3512872634200916135549963

theorem tailTrace_6841295 : CollatzResearch.WordTrace tailWord_6841295 prefixEnd_6841295 3512872634200916135549963 := by
  unfold tailWord_6841295
  simp only [CollatzResearch.WordTrace]
  refine ⟨249522527750164090010021339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166348351833442726673347559 249522527750164090010021339)
  ·
    refine ⟨374283791625246135015032009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249522527750164090010021339 374283791625246135015032009)
    ·
      refine ⟨280712843718934601261274007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 374283791625246135015032009 280712843718934601261274007)
      ·
        refine ⟨421069265578401901891911011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280712843718934601261274007 421069265578401901891911011)
        ·
          refine ⟨631603898367602852837866517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 421069265578401901891911011 631603898367602852837866517)
          ·
            refine ⟨29606432735981383726774993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 631603898367602852837866517 29606432735981383726774993)
            ·
              refine ⟨22204824551986037795081245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29606432735981383726774993 22204824551986037795081245)
              ·
                refine ⟨8326809206994764173155467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22204824551986037795081245 8326809206994764173155467)
                ·
                  refine ⟨12490213810492146259733201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8326809206994764173155467 12490213810492146259733201)
                  ·
                    refine ⟨9367660357869109694799901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12490213810492146259733201 9367660357869109694799901)
                    ·
                      refine ⟨3512872634200916135549963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9367660357869109694799901 3512872634200916135549963)
                      ·
                        rfl

theorem cell23_6841295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 3, 1, 2, 3].length) (baseStart_6841295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6841295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6841295 prefixEnd_6841295 := by exact prefixLift 6841295
  have htrace : WordTrace (prefixWord ++ tailWord_6841295) baseStart_6841295 baseEnd_6841295 := by
    simpa [prefixWord, tailWord_6841295, baseEnd_6841295] using wordTrace_append hprefix tailTrace_6841295
  have hstable : (prefixWord ++ tailWord_6841295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6841295).length < 2 ^ (prefixWord ++ tailWord_6841295).sum := by decide
  have hdescent : baseEnd_6841295 < baseStart_6841295 := by decide
  rcases family_descends (prefixWord ++ tailWord_6841295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6841298 : List Nat := [3, 2, 2, 3, 1, 1, 11]
def baseStart_6841298 : Nat := 118140960795 + 6841298 * 2 ^ 59
def prefixEnd_6841298 : Nat := 4983230072969 + 3 ^ 40 * 6841298 * 2
def baseEnd_6841298 : Nat := 43368816970899748442129

theorem tailTrace_6841298 : CollatzResearch.WordTrace tailWord_6841298 prefixEnd_6841298 43368816970899748442129 := by
  unfold tailWord_6841298
  simp only [CollatzResearch.WordTrace]
  refine ⟨62380659292288305380595137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166348424779435481014920365 62380659292288305380595137)
  ·
    refine ⟨46785494469216229035446353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62380659292288305380595137 46785494469216229035446353)
    ·
      refine ⟨35089120851912171776584765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46785494469216229035446353 35089120851912171776584765)
      ·
        refine ⟨13158420319467064416219287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35089120851912171776584765 13158420319467064416219287)
        ·
          refine ⟨19737630479200596624328931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13158420319467064416219287 19737630479200596624328931)
          ·
            refine ⟨29606445718800894936493397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19737630479200596624328931 29606445718800894936493397)
            ·
              refine ⟨43368816970899748442129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 29606445718800894936493397 43368816970899748442129)
              ·
                rfl

theorem cell23_6841298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 11].length) (baseStart_6841298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6841298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6841298 prefixEnd_6841298 := by exact prefixLift 6841298
  have htrace : WordTrace (prefixWord ++ tailWord_6841298) baseStart_6841298 baseEnd_6841298 := by
    simpa [prefixWord, tailWord_6841298, baseEnd_6841298] using wordTrace_append hprefix tailTrace_6841298
  have hstable : (prefixWord ++ tailWord_6841298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6841298).length < 2 ^ (prefixWord ++ tailWord_6841298).sum := by decide
  have hdescent : baseEnd_6841298 < baseStart_6841298 := by decide
  rcases family_descends (prefixWord ++ tailWord_6841298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6841302 : List Nat := [5, 2, 1, 1, 2, 1, 2, 1, 4, 4]
def baseStart_6841302 : Nat := 118140960795 + 6841302 * 2 ^ 59
def prefixEnd_6841302 : Nat := 4983230072969 + 3 ^ 40 * 6841302 * 2
def baseEnd_6841302 : Nat := 1170958742855165869387477

theorem tailTrace_6841302 : CollatzResearch.WordTrace tailWord_6841302 prefixEnd_6841302 1170958742855165869387477 := by
  unfold tailWord_6841302
  simp only [CollatzResearch.WordTrace]
  refine ⟨15595173941321170637845385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 166348522040759153470350773 15595173941321170637845385)
  ·
    refine ⟨11696380455990877978384039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15595173941321170637845385 11696380455990877978384039)
    ·
      refine ⟨17544570683986316967576059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11696380455990877978384039 17544570683986316967576059)
      ·
        refine ⟨26316856025979475451364089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17544570683986316967576059 26316856025979475451364089)
        ·
          refine ⟨19737642019484606588523067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26316856025979475451364089 19737642019484606588523067)
          ·
            refine ⟨29606463029226909882784601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19737642019484606588523067 29606463029226909882784601)
            ·
              refine ⟨22204847271920182412088451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29606463029226909882784601 22204847271920182412088451)
              ·
                refine ⟨33307270907880273618132677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22204847271920182412088451 33307270907880273618132677)
                ·
                  refine ⟨6245113295227551303399877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33307270907880273618132677 6245113295227551303399877)
                  ·
                    refine ⟨1170958742855165869387477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6245113295227551303399877 1170958742855165869387477)
                    ·
                      rfl

theorem cell23_6841302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_6841302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6841302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6841302 prefixEnd_6841302 := by exact prefixLift 6841302
  have htrace : WordTrace (prefixWord ++ tailWord_6841302) baseStart_6841302 baseEnd_6841302 := by
    simpa [prefixWord, tailWord_6841302, baseEnd_6841302] using wordTrace_append hprefix tailTrace_6841302
  have hstable : (prefixWord ++ tailWord_6841302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6841302).length < 2 ^ (prefixWord ++ tailWord_6841302).sum := by decide
  have hdescent : baseEnd_6841302 < baseStart_6841302 := by decide
  rcases family_descends (prefixWord ++ tailWord_6841302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6841309 : List Nat := [1, 4, 3, 1, 2, 1, 3, 1, 3, 2, 2]
def baseStart_6841309 : Nat := 118140960795 + 6841309 * 2 ^ 59
def prefixEnd_6841309 : Nat := 4983230072969 + 3 ^ 40 * 6841309 * 2
def baseEnd_6841309 : Nat := 3512879822930079080774899

theorem tailTrace_6841309 : CollatzResearch.WordTrace tailWord_6841309 prefixEnd_6841309 3512879822930079080774899 := by
  unfold tailWord_6841309
  simp only [CollatzResearch.WordTrace]
  refine ⟨249523038372113370401030981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166348692248075580267353987 249523038372113370401030981)
  ·
    refine ⟨46785569694771256950193309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 249523038372113370401030981 46785569694771256950193309)
    ·
      refine ⟨17544588635539221356322491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46785569694771256950193309 17544588635539221356322491)
      ·
        refine ⟨26316882953308832034483737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17544588635539221356322491 26316882953308832034483737)
        ·
          refine ⟨19737662214981624025862803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26316882953308832034483737 19737662214981624025862803)
          ·
            refine ⟨29606493322472436038794205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19737662214981624025862803 29606493322472436038794205)
            ·
              refine ⟨11102434995927163514547827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29606493322472436038794205 11102434995927163514547827)
              ·
                refine ⟨16653652493890745271821741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11102434995927163514547827 16653652493890745271821741)
                ·
                  refine ⟨6245119685209029476933153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16653652493890745271821741 6245119685209029476933153)
                  ·
                    refine ⟨4683839763906772107699865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6245119685209029476933153 4683839763906772107699865)
                    ·
                      refine ⟨3512879822930079080774899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4683839763906772107699865 3512879822930079080774899)
                      ·
                        rfl

theorem cell23_6841309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 1, 3, 2, 2].length) (baseStart_6841309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6841309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6841309 prefixEnd_6841309 := by exact prefixLift 6841309
  have htrace : WordTrace (prefixWord ++ tailWord_6841309) baseStart_6841309 baseEnd_6841309 := by
    simpa [prefixWord, tailWord_6841309, baseEnd_6841309] using wordTrace_append hprefix tailTrace_6841309
  have hstable : (prefixWord ++ tailWord_6841309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6841309).length < 2 ^ (prefixWord ++ tailWord_6841309).sum := by decide
  have hdescent : baseEnd_6841309 < baseStart_6841309 := by decide
  rcases family_descends (prefixWord ++ tailWord_6841309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6841319 : List Nat := [1, 1, 5, 2, 2, 3, 2, 1, 2, 4]
def baseStart_6841319 : Nat := 118140960795 + 6841319 * 2 ^ 59
def prefixEnd_6841319 : Nat := 4983230072969 + 3 ^ 40 * 6841319 * 2
def baseEnd_6841319 : Nat := 1170961652578874680549951

theorem tailTrace_6841319 : CollatzResearch.WordTrace tailWord_6841319 prefixEnd_6841319 1170961652578874680549951 := by
  unfold tailWord_6841319
  simp only [CollatzResearch.WordTrace]
  refine ⟨249523403102077142108895011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166348935401384761405930007 249523403102077142108895011)
  ·
    refine ⟨374285104653115713163342517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249523403102077142108895011 374285104653115713163342517)
    ·
      refine ⟨35089228561229598109063361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 374285104653115713163342517 35089228561229598109063361)
      ·
        refine ⟨26316921420922198581797521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35089228561229598109063361 26316921420922198581797521)
        ·
          refine ⟨19737691065691648936348141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26316921420922198581797521 19737691065691648936348141)
          ·
            refine ⟨7401634149634368351130553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19737691065691648936348141 7401634149634368351130553)
            ·
              refine ⟨5551225612225776263347915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7401634149634368351130553 5551225612225776263347915)
              ·
                refine ⟨8326838418338664395021873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5551225612225776263347915 8326838418338664395021873)
                ·
                  refine ⟨6245128813753998296266405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8326838418338664395021873 6245128813753998296266405)
                  ·
                    refine ⟨1170961652578874680549951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6245128813753998296266405 1170961652578874680549951)
                    ·
                      rfl

theorem cell23_6841319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 2, 1, 2, 4].length) (baseStart_6841319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6841319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6841319 prefixEnd_6841319 := by exact prefixLift 6841319
  have htrace : WordTrace (prefixWord ++ tailWord_6841319) baseStart_6841319 baseEnd_6841319 := by
    simpa [prefixWord, tailWord_6841319, baseEnd_6841319] using wordTrace_append hprefix tailTrace_6841319
  have hstable : (prefixWord ++ tailWord_6841319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6841319).length < 2 ^ (prefixWord ++ tailWord_6841319).sum := by decide
  have hdescent : baseEnd_6841319 < baseStart_6841319 := by decide
  rcases family_descends (prefixWord ++ tailWord_6841319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6841331 : List Nat := [1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 10]
def baseStart_6841331 : Nat := 118140960795 + 6841331 * 2 ^ 59
def prefixEnd_6841331 : Nat := 4983230072969 + 3 ^ 40 * 6841331 * 2
def baseEnd_6841331 : Nat := 3512891119504477994699797

theorem tailTrace_6841331 : CollatzResearch.WordTrace tailWord_6841331 prefixEnd_6841331 3512891119504477994699797 := by
  unfold tailWord_6841331
  simp only [CollatzResearch.WordTrace]
  refine ⟨249523840778033668158331847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166349227185355778772221231 249523840778033668158331847)
  ·
    refine ⟨374285761167050502237497771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249523840778033668158331847 374285761167050502237497771)
    ·
      refine ⟨561428641750575753356246657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374285761167050502237497771 561428641750575753356246657)
      ·
        refine ⟨421071481312931815017184993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 561428641750575753356246657 421071481312931815017184993)
        ·
          refine ⟨315803610984698861262888745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 421071481312931815017184993 315803610984698861262888745)
          ·
            refine ⟨236852708238524145947166559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 315803610984698861262888745 236852708238524145947166559)
            ·
              refine ⟨355279062357786218920749839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 236852708238524145947166559 355279062357786218920749839)
              ·
                refine ⟨532918593536679328381124759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 355279062357786218920749839 532918593536679328381124759)
                ·
                  refine ⟨799377890305018992571687139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 532918593536679328381124759 799377890305018992571687139)
                  ·
                    refine ⟨1199066835457528488857530709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 799377890305018992571687139 1199066835457528488857530709)
                    ·
                      refine ⟨3512891119504477994699797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 1199066835457528488857530709 3512891119504477994699797)
                      ·
                        rfl

theorem cell23_6841331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 10].length) (baseStart_6841331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6841331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6841331 prefixEnd_6841331 := by exact prefixLift 6841331
  have htrace : WordTrace (prefixWord ++ tailWord_6841331) baseStart_6841331 baseEnd_6841331 := by
    simpa [prefixWord, tailWord_6841331, baseEnd_6841331] using wordTrace_append hprefix tailTrace_6841331
  have hstable : (prefixWord ++ tailWord_6841331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6841331).length < 2 ^ (prefixWord ++ tailWord_6841331).sum := by decide
  have hdescent : baseEnd_6841331 < baseStart_6841331 := by decide
  rcases family_descends (prefixWord ++ tailWord_6841331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6841346 : List Nat := [3, 4, 1, 3, 2, 1, 1, 1, 1, 1, 5]
def baseStart_6841346 : Nat := 118140960795 + 6841346 * 2 ^ 59
def prefixEnd_6841346 : Nat := 4983230072969 + 3 ^ 40 * 6841346 * 2
def baseEnd_6841346 : Nat := 3512898821714295436012229

theorem tailTrace_6841346 : CollatzResearch.WordTrace tailWord_6841346 prefixEnd_6841346 3512898821714295436012229 := by
  unfold tailWord_6841346
  simp only [CollatzResearch.WordTrace]
  refine ⟨62381096968244831430031973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166349591915319550480085261 62381096968244831430031973)
  ·
    refine ⟨11696455681545905893130995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62381096968244831430031973 11696455681545905893130995)
    ·
      refine ⟨17544683522318858839696493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11696455681545905893130995 17544683522318858839696493)
      ·
        refine ⟨6579256320869572064886185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17544683522318858839696493 6579256320869572064886185)
        ·
          refine ⟨4934442240652179048664639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6579256320869572064886185 4934442240652179048664639)
          ·
            refine ⟨7401663360978268572996959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4934442240652179048664639 7401663360978268572996959)
            ·
              refine ⟨11102495041467402859495439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7401663360978268572996959 11102495041467402859495439)
              ·
                refine ⟨16653742562201104289243159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11102495041467402859495439 16653742562201104289243159)
                ·
                  refine ⟨24980613843301656433864739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16653742562201104289243159 24980613843301656433864739)
                  ·
                    refine ⟨37470920764952484650797109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24980613843301656433864739 37470920764952484650797109)
                    ·
                      refine ⟨3512898821714295436012229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37470920764952484650797109 3512898821714295436012229)
                      ·
                        rfl

theorem cell23_6841346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_6841346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6841346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6841346 prefixEnd_6841346 := by exact prefixLift 6841346
  have htrace : WordTrace (prefixWord ++ tailWord_6841346) baseStart_6841346 baseEnd_6841346 := by
    simpa [prefixWord, tailWord_6841346, baseEnd_6841346] using wordTrace_append hprefix tailTrace_6841346
  have hstable : (prefixWord ++ tailWord_6841346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6841346).length < 2 ^ (prefixWord ++ tailWord_6841346).sum := by decide
  have hdescent : baseEnd_6841346 < baseStart_6841346 := by decide
  rcases family_descends (prefixWord ++ tailWord_6841346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6841388 : List Nat := [2, 2, 1, 1, 1, 2, 5, 2, 7]
def baseStart_6841388 : Nat := 118140960795 + 6841388 * 2 ^ 59
def prefixEnd_6841388 : Nat := 4983230072969 + 3 ^ 40 * 6841388 * 2
def baseEnd_6841388 : Nat := 390324487544642696854115

theorem tailTrace_6841388 : CollatzResearch.WordTrace tailWord_6841388 prefixEnd_6841388 390324487544642696854115 := by
  unfold tailWord_6841388
  simp only [CollatzResearch.WordTrace]
  refine ⟨124762959869413583446578409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166350613159218111262104545 124762959869413583446578409)
  ·
    refine ⟨93572219902060187584933807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124762959869413583446578409 93572219902060187584933807)
    ·
      refine ⟨140358329853090281377400711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93572219902060187584933807 140358329853090281377400711)
      ·
        refine ⟨210537494779635422066101067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140358329853090281377400711 210537494779635422066101067)
        ·
          refine ⟨315806242169453133099151601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210537494779635422066101067 315806242169453133099151601)
          ·
            refine ⟨236854681627089849824363701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 315806242169453133099151601 236854681627089849824363701)
            ·
              refine ⟨22205126402539673421034097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 236854681627089849824363701 22205126402539673421034097)
              ·
                refine ⟨16653844801904755065775573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22205126402539673421034097 16653844801904755065775573)
                ·
                  refine ⟨390324487544642696854115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16653844801904755065775573 390324487544642696854115)
                  ·
                    rfl

theorem cell23_6841388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 7].length) (baseStart_6841388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6841388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6841388 prefixEnd_6841388 := by exact prefixLift 6841388
  have htrace : WordTrace (prefixWord ++ tailWord_6841388) baseStart_6841388 baseEnd_6841388 := by
    simpa [prefixWord, tailWord_6841388, baseEnd_6841388] using wordTrace_append hprefix tailTrace_6841388
  have hstable : (prefixWord ++ tailWord_6841388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6841388).length < 2 ^ (prefixWord ++ tailWord_6841388).sum := by decide
  have hdescent : baseEnd_6841388 < baseStart_6841388 := by decide
  rcases family_descends (prefixWord ++ tailWord_6841388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6841415 : List Nat := [1, 1, 4, 1, 3, 2, 1, 2, 2, 3, 3]
def baseStart_6841415 : Nat := 118140960795 + 6841415 * 2 ^ 59
def prefixEnd_6841415 : Nat := 4983230072969 + 3 ^ 40 * 6841415 * 2
def baseEnd_6841415 : Nat := 3512934251879455666049411

theorem tailTrace_6841415 : CollatzResearch.WordTrace tailWord_6841415 prefixEnd_6841415 3512934251879455666049411 := by
  unfold tailWord_6841415
  simp only [CollatzResearch.WordTrace]
  refine ⟨249526904509729350504389699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166351269673152900336259799 249526904509729350504389699)
  ·
    refine ⟨374290356764594025756584549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249526904509729350504389699 374290356764594025756584549)
    ·
      refine ⟨70179441893361379829359603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 374290356764594025756584549 70179441893361379829359603)
      ·
        refine ⟨105269162840042069744039405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70179441893361379829359603 105269162840042069744039405)
        ·
          refine ⟨39475936065015776154014777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105269162840042069744039405 39475936065015776154014777)
          ·
            refine ⟨29606952048761832115511083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39475936065015776154014777 29606952048761832115511083)
            ·
              refine ⟨44410428073142748173266625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29606952048761832115511083 44410428073142748173266625)
              ·
                refine ⟨33307821054857061129949969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44410428073142748173266625 33307821054857061129949969)
                ·
                  refine ⟨24980865791142795847462477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33307821054857061129949969 24980865791142795847462477)
                  ·
                    refine ⟨9367824671678548442798429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24980865791142795847462477 9367824671678548442798429)
                    ·
                      refine ⟨3512934251879455666049411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9367824671678548442798429 3512934251879455666049411)
                      ·
                        rfl

theorem cell23_6841415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 2, 2, 3, 3].length) (baseStart_6841415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6841415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6841415 prefixEnd_6841415 := by exact prefixLift 6841415
  have htrace : WordTrace (prefixWord ++ tailWord_6841415) baseStart_6841415 baseEnd_6841415 := by
    simpa [prefixWord, tailWord_6841415, baseEnd_6841415] using wordTrace_append hprefix tailTrace_6841415
  have hstable : (prefixWord ++ tailWord_6841415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6841415).length < 2 ^ (prefixWord ++ tailWord_6841415).sum := by decide
  have hdescent : baseEnd_6841415 < baseStart_6841415 := by decide
  rcases family_descends (prefixWord ++ tailWord_6841415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6841425 : List Nat := [1, 2, 2, 1, 3, 1, 2, 1, 1, 7, 2]
def baseStart_6841425 : Nat := 118140960795 + 6841425 * 2 ^ 59
def prefixEnd_6841425 : Nat := 4983230072969 + 3 ^ 40 * 6841425 * 2
def baseEnd_6841425 : Nat := 3512939386686000626924365

theorem tailTrace_6841425 : CollatzResearch.WordTrace tailWord_6841425 prefixEnd_6841425 3512939386686000626924365 := by
  unfold tailWord_6841425
  simp only [CollatzResearch.WordTrace]
  refine ⟨249527269239693122212253729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166351512826462081474835819 249527269239693122212253729)
  ·
    refine ⟨187145451929769841659190297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249527269239693122212253729 187145451929769841659190297)
    ·
      refine ⟨140359088947327381244392723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187145451929769841659190297 140359088947327381244392723)
      ·
        refine ⟨210538633420991071866589085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140359088947327381244392723 210538633420991071866589085)
        ·
          refine ⟨78951987532871651949970907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 210538633420991071866589085 78951987532871651949970907)
          ·
            refine ⟨118427981299307477924956361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78951987532871651949970907 118427981299307477924956361)
            ·
              refine ⟨88820985974480608443717271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118427981299307477924956361 88820985974480608443717271)
              ·
                refine ⟨133231478961720912665575907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88820985974480608443717271 133231478961720912665575907)
                ·
                  refine ⟨199847218442581368998363861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133231478961720912665575907 199847218442581368998363861)
                  ·
                    refine ⟨4683919182248000835899153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 199847218442581368998363861 4683919182248000835899153)
                    ·
                      refine ⟨3512939386686000626924365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4683919182248000835899153 3512939386686000626924365)
                      ·
                        rfl

theorem cell23_6841425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 7, 2].length) (baseStart_6841425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6841425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6841425 prefixEnd_6841425 := by exact prefixLift 6841425
  have htrace : WordTrace (prefixWord ++ tailWord_6841425) baseStart_6841425 baseEnd_6841425 := by
    simpa [prefixWord, tailWord_6841425, baseEnd_6841425] using wordTrace_append hprefix tailTrace_6841425
  have hstable : (prefixWord ++ tailWord_6841425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6841425).length < 2 ^ (prefixWord ++ tailWord_6841425).sum := by decide
  have hdescent : baseEnd_6841425 < baseStart_6841425 := by decide
  rcases family_descends (prefixWord ++ tailWord_6841425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6841455 : List Nat := [1, 1, 2, 1, 3, 3, 2, 3, 2, 1, 4]
def baseStart_6841455 : Nat := 118140960795 + 6841455 * 2 ^ 59
def prefixEnd_6841455 : Nat := 4983230072969 + 3 ^ 40 * 6841455 * 2
def baseEnd_6841455 : Nat := 3512954791105635509549227

theorem tailTrace_6841455 : CollatzResearch.WordTrace tailWord_6841455 prefixEnd_6841455 3512954791105635509549227 := by
  unfold tailWord_6841455
  simp only [CollatzResearch.WordTrace]
  refine ⟨249528363429584437335845819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166352242286389624890563879 249528363429584437335845819)
  ·
    refine ⟨374292545144376656003768729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249528363429584437335845819 374292545144376656003768729)
    ·
      refine ⟨280719408858282492002826547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 374292545144376656003768729 280719408858282492002826547)
      ·
        refine ⟨421079113287423738004239821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280719408858282492002826547 421079113287423738004239821)
        ·
          refine ⟨157904667482783901751589933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 421079113287423738004239821 157904667482783901751589933)
          ·
            refine ⟨59214250306043963156846225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157904667482783901751589933 59214250306043963156846225)
            ·
              refine ⟨44410687729532972367634669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59214250306043963156846225 44410687729532972367634669)
              ·
                refine ⟨16654007898574864637863001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44410687729532972367634669 16654007898574864637863001)
                ·
                  refine ⟨12490505923931148478397251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16654007898574864637863001 12490505923931148478397251)
                  ·
                    refine ⟨18735758885896722717595877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12490505923931148478397251 18735758885896722717595877)
                    ·
                      refine ⟨3512954791105635509549227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18735758885896722717595877 3512954791105635509549227)
                      ·
                        rfl

theorem cell23_6841455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 3, 2, 1, 4].length) (baseStart_6841455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6841455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6841455 prefixEnd_6841455 := by exact prefixLift 6841455
  have htrace : WordTrace (prefixWord ++ tailWord_6841455) baseStart_6841455 baseEnd_6841455 := by
    simpa [prefixWord, tailWord_6841455, baseEnd_6841455] using wordTrace_append hprefix tailTrace_6841455
  have hstable : (prefixWord ++ tailWord_6841455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6841455).length < 2 ^ (prefixWord ++ tailWord_6841455).sum := by decide
  have hdescent : baseEnd_6841455 < baseStart_6841455 := by decide
  rcases family_descends (prefixWord ++ tailWord_6841455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6841562 : List Nat := [3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 4]
def baseStart_6841562 : Nat := 118140960795 + 6841562 * 2 ^ 59
def prefixEnd_6841562 : Nat := 4983230072969 + 3 ^ 40 * 6841562 * 2
def baseEnd_6841562 : Nat := 3513009733535666590911235

theorem tailTrace_6841562 : CollatzResearch.WordTrace tailWord_6841562 prefixEnd_6841562 3513009733535666590911235 := by
  unfold tailWord_6841562
  simp only [CollatzResearch.WordTrace]
  refine ⟨62383066510049198652497735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166354844026797863073327293 62383066510049198652497735)
  ·
    refine ⟨93574599765073797978746603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62383066510049198652497735 93574599765073797978746603)
    ·
      refine ⟨140361899647610696968119905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93574599765073797978746603 140361899647610696968119905)
      ·
        refine ⟨105271424735708022726089929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140361899647610696968119905 105271424735708022726089929)
        ·
          refine ⟨78953568551781017044567447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105271424735708022726089929 78953568551781017044567447)
          ·
            refine ⟨118430352827671525566851171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78953568551781017044567447 118430352827671525566851171)
            ·
              refine ⟨177645529241507288350276757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118430352827671525566851171 177645529241507288350276757)
              ·
                refine ⟨8327134183195654141419223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 177645529241507288350276757 8327134183195654141419223)
                ·
                  refine ⟨12490701274793481212128835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8327134183195654141419223 12490701274793481212128835)
                  ·
                    refine ⟨18736051912190221818193253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12490701274793481212128835 18736051912190221818193253)
                    ·
                      refine ⟨3513009733535666590911235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18736051912190221818193253 3513009733535666590911235)
                      ·
                        rfl

theorem cell23_6841562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 4].length) (baseStart_6841562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6841562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6841562 prefixEnd_6841562 := by exact prefixLift 6841562
  have htrace : WordTrace (prefixWord ++ tailWord_6841562) baseStart_6841562 baseEnd_6841562 := by
    simpa [prefixWord, tailWord_6841562, baseEnd_6841562] using wordTrace_append hprefix tailTrace_6841562
  have hstable : (prefixWord ++ tailWord_6841562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6841562).length < 2 ^ (prefixWord ++ tailWord_6841562).sum := by decide
  have hdescent : baseEnd_6841562 < baseStart_6841562 := by decide
  rcases family_descends (prefixWord ++ tailWord_6841562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
