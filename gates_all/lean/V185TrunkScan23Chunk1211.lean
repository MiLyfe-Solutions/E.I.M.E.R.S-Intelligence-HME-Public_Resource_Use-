import V185TrunkScan23Chunk1210

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7175044 : List Nat := [2, 3, 2, 1, 1, 1, 1, 3, 1, 3, 5]
def baseStart_7175044 : Nat := 118140960795 + 7175044 * 2 ^ 59
def prefixEnd_7175044 : Nat := 4983230072969 + 3 ^ 40 * 7175044 * 2
def baseEnd_7175044 : Nat := 3684246289158330841052579

theorem tailTrace_7175044 : CollatzResearch.WordTrace tailWord_7175044 prefixEnd_7175044 3684246289158330841052579 := by
  unfold tailWord_7175044
  simp only [CollatzResearch.WordTrace]
  refine ⟨130847676909024231400618093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174463569212032308534157457 130847676909024231400618093)
  ·
    refine ⟨49067878840884086775231785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130847676909024231400618093 49067878840884086775231785)
    ·
      refine ⟨36800909130663065081423839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49067878840884086775231785 36800909130663065081423839)
      ·
        refine ⟨55201363695994597622135759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36800909130663065081423839 55201363695994597622135759)
        ·
          refine ⟨82802045543991896433203639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55201363695994597622135759 82802045543991896433203639)
          ·
            refine ⟨124203068315987844649805459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82802045543991896433203639 124203068315987844649805459)
            ·
              refine ⟨186304602473981766974708189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124203068315987844649805459 186304602473981766974708189)
              ·
                refine ⟨69864225927743162615515571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 186304602473981766974708189 69864225927743162615515571)
                ·
                  refine ⟨104796338891614743923273357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69864225927743162615515571 104796338891614743923273357)
                  ·
                    refine ⟨39298627084355528971227509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 104796338891614743923273357 39298627084355528971227509)
                    ·
                      refine ⟨3684246289158330841052579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39298627084355528971227509 3684246289158330841052579)
                      ·
                        rfl

theorem cell23_7175044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_7175044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7175044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7175044 prefixEnd_7175044 := by exact prefixLift 7175044
  have htrace : WordTrace (prefixWord ++ tailWord_7175044) baseStart_7175044 baseEnd_7175044 := by
    simpa [prefixWord, tailWord_7175044, baseEnd_7175044] using wordTrace_append hprefix tailTrace_7175044
  have hstable : (prefixWord ++ tailWord_7175044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7175044).length < 2 ^ (prefixWord ++ tailWord_7175044).sum := by decide
  have hdescent : baseEnd_7175044 < baseStart_7175044 := by decide
  rcases family_descends (prefixWord ++ tailWord_7175044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7175045 : List Nat := [1, 3, 1, 1, 3, 3, 4, 1, 1, 3, 2]
def baseStart_7175045 : Nat := 118140960795 + 7175045 * 2 ^ 59
def prefixEnd_7175045 : Nat := 4983230072969 + 3 ^ 40 * 7175045 * 2
def baseEnd_7175045 : Nat := 3684246802638985337140075

theorem tailTrace_7175045 : CollatzResearch.WordTrace tailWord_7175045 prefixEnd_7175045 3684246802638985337140075 := by
  unfold tailWord_7175045
  simp only [CollatzResearch.WordTrace]
  refine ⟨261695390291044839972022589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174463593527363226648015059 261695390291044839972022589)
  ·
    refine ⟨98135771359141814989508471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261695390291044839972022589 98135771359141814989508471)
    ·
      refine ⟨147203657038712722484262707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98135771359141814989508471 147203657038712722484262707)
      ·
        refine ⟨220805485558069083726394061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147203657038712722484262707 220805485558069083726394061)
        ·
          refine ⟨82802057084275906397397773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 220805485558069083726394061 82802057084275906397397773)
          ·
            refine ⟨31050771406603464899024165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82802057084275906397397773 31050771406603464899024165)
            ·
              refine ⟨5822019638738149668567031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31050771406603464899024165 5822019638738149668567031)
              ·
                refine ⟨8733029458107224502850547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5822019638738149668567031 8733029458107224502850547)
                ·
                  refine ⟨13099544187160836754275821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8733029458107224502850547 13099544187160836754275821)
                  ·
                    refine ⟨4912329070185313782853433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13099544187160836754275821 4912329070185313782853433)
                    ·
                      refine ⟨3684246802638985337140075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4912329070185313782853433 3684246802638985337140075)
                      ·
                        rfl

theorem cell23_7175045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 4, 1, 1, 3, 2].length) (baseStart_7175045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7175045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7175045 prefixEnd_7175045 := by exact prefixLift 7175045
  have htrace : WordTrace (prefixWord ++ tailWord_7175045) baseStart_7175045 baseEnd_7175045 := by
    simpa [prefixWord, tailWord_7175045, baseEnd_7175045] using wordTrace_append hprefix tailTrace_7175045
  have hstable : (prefixWord ++ tailWord_7175045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7175045).length < 2 ^ (prefixWord ++ tailWord_7175045).sum := by decide
  have hdescent : baseEnd_7175045 < baseStart_7175045 := by decide
  rcases family_descends (prefixWord ++ tailWord_7175045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7175071 : List Nat := [1, 1, 2, 5, 2, 1, 2, 1, 2, 2, 4]
def baseStart_7175071 : Nat := 118140960795 + 7175071 * 2 ^ 59
def prefixEnd_7175071 : Nat := 4983230072969 + 3 ^ 40 * 7175071 * 2
def baseEnd_7175071 : Nat := 3684260153136002235414955

theorem tailTrace_7175071 : CollatzResearch.WordTrace tailWord_7175071 prefixEnd_7175071 3684260153136002235414955 := by
  unfold tailWord_7175071
  simp only [CollatzResearch.WordTrace]
  refine ⟨261696338588950646412469067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174464225725967097608312711 261696338588950646412469067)
  ·
    refine ⟨392544507883425969618703601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261696338588950646412469067 392544507883425969618703601)
    ·
      refine ⟨294408380912569477214027701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 392544507883425969618703601 294408380912569477214027701)
      ·
        refine ⟨27600785710553388488815097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 294408380912569477214027701 27600785710553388488815097)
        ·
          refine ⟨20700589282915041366611323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27600785710553388488815097 20700589282915041366611323)
          ·
            refine ⟨31050883924372562049916985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20700589282915041366611323 31050883924372562049916985)
            ·
              refine ⟨23288162943279421537437739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31050883924372562049916985 23288162943279421537437739)
              ·
                refine ⟨34932244414919132306156609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23288162943279421537437739 34932244414919132306156609)
                ·
                  refine ⟨26199183311189349229617457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34932244414919132306156609 26199183311189349229617457)
                  ·
                    refine ⟨19649387483392011922213093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26199183311189349229617457 19649387483392011922213093)
                    ·
                      refine ⟨3684260153136002235414955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19649387483392011922213093 3684260153136002235414955)
                      ·
                        rfl

theorem cell23_7175071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_7175071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7175071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7175071 prefixEnd_7175071 := by exact prefixLift 7175071
  have htrace : WordTrace (prefixWord ++ tailWord_7175071) baseStart_7175071 baseEnd_7175071 := by
    simpa [prefixWord, tailWord_7175071, baseEnd_7175071] using wordTrace_append hprefix tailTrace_7175071
  have hstable : (prefixWord ++ tailWord_7175071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7175071).length < 2 ^ (prefixWord ++ tailWord_7175071).sum := by decide
  have hdescent : baseEnd_7175071 < baseStart_7175071 := by decide
  rcases family_descends (prefixWord ++ tailWord_7175071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7175092 : List Nat := [2, 5, 2, 1, 1, 1, 1, 2, 4, 2, 2]
def baseStart_7175092 : Nat := 118140960795 + 7175092 * 2 ^ 59
def prefixEnd_7175092 : Nat := 4983230072969 + 3 ^ 40 * 7175092 * 2
def baseEnd_7175092 : Nat := 3684270936229746653252359

theorem tailTrace_7175092 : CollatzResearch.WordTrace tailWord_7175092 prefixEnd_7175092 3684270936229746653252359 := by
  unfold tailWord_7175092
  simp only [CollatzResearch.WordTrace]
  refine ⟨130848552260937283499491765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174464736347916377999322353 130848552260937283499491765)
  ·
    refine ⟨12267051774462870328077353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 130848552260937283499491765 12267051774462870328077353)
    ·
      refine ⟨9200288830847152746058015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12267051774462870328077353 9200288830847152746058015)
      ·
        refine ⟨13800433246270729119087023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9200288830847152746058015 13800433246270729119087023)
        ·
          refine ⟨20700649869406093678630535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13800433246270729119087023 20700649869406093678630535)
          ·
            refine ⟨31050974804109140517945803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20700649869406093678630535 31050974804109140517945803)
            ·
              refine ⟨46576462206163710776918705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31050974804109140517945803 46576462206163710776918705)
              ·
                refine ⟨34932346654622783082689029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46576462206163710776918705 34932346654622783082689029)
                ·
                  refine ⟨6549814997741771828004193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34932346654622783082689029 6549814997741771828004193)
                  ·
                    refine ⟨4912361248306328871003145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6549814997741771828004193 4912361248306328871003145)
                    ·
                      refine ⟨3684270936229746653252359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4912361248306328871003145 3684270936229746653252359)
                      ·
                        rfl

theorem cell23_7175092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_7175092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7175092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7175092 prefixEnd_7175092 := by exact prefixLift 7175092
  have htrace : WordTrace (prefixWord ++ tailWord_7175092) baseStart_7175092 baseEnd_7175092 := by
    simpa [prefixWord, tailWord_7175092, baseEnd_7175092] using wordTrace_append hprefix tailTrace_7175092
  have hstable : (prefixWord ++ tailWord_7175092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7175092).length < 2 ^ (prefixWord ++ tailWord_7175092).sum := by decide
  have hdescent : baseEnd_7175092 < baseStart_7175092 := by decide
  rcases family_descends (prefixWord ++ tailWord_7175092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7175126 : List Nat := [5, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2]
def baseStart_7175126 : Nat := 118140960795 + 7175126 * 2 ^ 59
def prefixEnd_7175126 : Nat := 4983230072969 + 3 ^ 40 * 7175126 * 2
def baseEnd_7175126 : Nat := 3684288394571999520227203

theorem tailTrace_7175126 : CollatzResearch.WordTrace tailWord_7175126 prefixEnd_7175126 3684288394571999520227203 := by
  unfold tailWord_7175126
  simp only [CollatzResearch.WordTrace]
  refine ⟨16356146537734461925357577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 174465563069167593870480821 16356146537734461925357577)
  ·
    refine ⟨12267109903300846444018183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16356146537734461925357577 12267109903300846444018183)
    ·
      refine ⟨18400664854951269666027275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12267109903300846444018183 18400664854951269666027275)
      ·
        refine ⟨27600997282426904499040913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18400664854951269666027275 27600997282426904499040913)
        ·
          refine ⟨20700747961820178374280685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27600997282426904499040913 20700747961820178374280685)
          ·
            refine ⟨7762780485682566890355257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20700747961820178374280685 7762780485682566890355257)
            ·
              refine ⟨5822085364261925167766443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7762780485682566890355257 5822085364261925167766443)
              ·
                refine ⟨8733128046392887751649665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5822085364261925167766443 8733128046392887751649665)
                ·
                  refine ⟨6549846034794665813737249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8733128046392887751649665 6549846034794665813737249)
                  ·
                    refine ⟨4912384526095999360302937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6549846034794665813737249 4912384526095999360302937)
                    ·
                      refine ⟨3684288394571999520227203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4912384526095999360302937 3684288394571999520227203)
                      ·
                        rfl

theorem cell23_7175126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2].length) (baseStart_7175126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7175126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7175126 prefixEnd_7175126 := by exact prefixLift 7175126
  have htrace : WordTrace (prefixWord ++ tailWord_7175126) baseStart_7175126 baseEnd_7175126 := by
    simpa [prefixWord, tailWord_7175126, baseEnd_7175126] using wordTrace_append hprefix tailTrace_7175126
  have hstable : (prefixWord ++ tailWord_7175126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7175126).length < 2 ^ (prefixWord ++ tailWord_7175126).sum := by decide
  have hdescent : baseEnd_7175126 < baseStart_7175126 := by decide
  rcases family_descends (prefixWord ++ tailWord_7175126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7175175 : List Nat := [1, 1, 4, 3, 1, 1, 3, 4, 1, 4]
def baseStart_7175175 : Nat := 118140960795 + 7175175 * 2 ^ 59
def prefixEnd_7175175 : Nat := 4983230072969 + 3 ^ 40 * 7175175 * 2
def baseEnd_7175175 : Nat := 1228104518374689942838159

theorem tailTrace_7175175 : CollatzResearch.WordTrace tailWord_7175175 prefixEnd_7175175 1228104518374689942838159 := by
  unfold tailWord_7175175
  simp only [CollatzResearch.WordTrace]
  refine ⟨261700131780573872174254979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174466754520382581449503319 261700131780573872174254979)
  ·
    refine ⟨392550197670860808261382469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261700131780573872174254979 392550197670860808261382469)
    ·
      refine ⟨73603162063286401549009213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 392550197670860808261382469 73603162063286401549009213)
      ·
        refine ⟨27601185773732400580878455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73603162063286401549009213 27601185773732400580878455)
        ·
          refine ⟨41401778660598600871317683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27601185773732400580878455 41401778660598600871317683)
          ·
            refine ⟨62102667990897901306976525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41401778660598600871317683 62102667990897901306976525)
            ·
              refine ⟨23288500496586712990116197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62102667990897901306976525 23288500496586712990116197)
              ·
                refine ⟨4366593843110008685646787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23288500496586712990116197 4366593843110008685646787)
                ·
                  refine ⟨6549890764665013028470181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4366593843110008685646787 6549890764665013028470181)
                  ·
                    refine ⟨1228104518374689942838159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6549890764665013028470181 1228104518374689942838159)
                    ·
                      rfl

theorem cell23_7175175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 4, 1, 4].length) (baseStart_7175175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7175175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7175175 prefixEnd_7175175 := by exact prefixLift 7175175
  have htrace : WordTrace (prefixWord ++ tailWord_7175175) baseStart_7175175 baseEnd_7175175 := by
    simpa [prefixWord, tailWord_7175175, baseEnd_7175175] using wordTrace_append hprefix tailTrace_7175175
  have hstable : (prefixWord ++ tailWord_7175175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7175175).length < 2 ^ (prefixWord ++ tailWord_7175175).sum := by decide
  have hdescent : baseEnd_7175175 < baseStart_7175175 := by decide
  rcases family_descends (prefixWord ++ tailWord_7175175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7175184 : List Nat := [2, 1, 1, 1, 1, 1, 1, 3, 1, 11]
def baseStart_7175184 : Nat := 118140960795 + 7175184 * 2 ^ 59
def prefixEnd_7175184 : Nat := 4983230072969 + 3 ^ 40 * 7175184 * 2
def baseEnd_7175184 : Nat := 1228106058816653431100645

theorem tailTrace_7175184 : CollatzResearch.WordTrace tailWord_7175184 prefixEnd_7175184 1228106058816653431100645 := by
  unfold tailWord_7175184
  simp only [CollatzResearch.WordTrace]
  refine ⟨130850230018770633355666303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174466973358360844474221737 130850230018770633355666303)
  ·
    refine ⟨196275345028155950033499455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130850230018770633355666303 196275345028155950033499455)
    ·
      refine ⟨294413017542233925050249183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196275345028155950033499455 294413017542233925050249183)
      ·
        refine ⟨441619526313350887575373775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294413017542233925050249183 441619526313350887575373775)
        ·
          refine ⟨662429289470026331363060663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 441619526313350887575373775 662429289470026331363060663)
          ·
            refine ⟨993643934205039497044590995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 662429289470026331363060663 993643934205039497044590995)
            ·
              refine ⟨1490465901307559245566886493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 993643934205039497044590995 1490465901307559245566886493)
              ·
                refine ⟨558924712990334717087582435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1490465901307559245566886493 558924712990334717087582435)
                ·
                  refine ⟨838387069485502075631373653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 558924712990334717087582435 838387069485502075631373653)
                  ·
                    refine ⟨1228106058816653431100645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 838387069485502075631373653 1228106058816653431100645)
                    ·
                      rfl

theorem cell23_7175184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 1, 11].length) (baseStart_7175184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7175184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7175184 prefixEnd_7175184 := by exact prefixLift 7175184
  have htrace : WordTrace (prefixWord ++ tailWord_7175184) baseStart_7175184 baseEnd_7175184 := by
    simpa [prefixWord, tailWord_7175184, baseEnd_7175184] using wordTrace_append hprefix tailTrace_7175184
  have hstable : (prefixWord ++ tailWord_7175184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7175184).length < 2 ^ (prefixWord ++ tailWord_7175184).sum := by decide
  have hdescent : baseEnd_7175184 < baseStart_7175184 := by decide
  rcases family_descends (prefixWord ++ tailWord_7175184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7175218 : List Nat := [3, 2, 1, 1, 2, 2, 3, 3, 1, 5]
def baseStart_7175218 : Nat := 118140960795 + 7175218 * 2 ^ 59
def prefixEnd_7175218 : Nat := 4983230072969 + 3 ^ 40 * 7175218 * 2
def baseEnd_7175218 : Nat := 1228111878264071053425593

theorem tailTrace_7175218 : CollatzResearch.WordTrace tailWord_7175218 prefixEnd_7175218 1228111878264071053425593 := by
  unfold tailWord_7175218
  simp only [CollatzResearch.WordTrace]
  refine ⟨65425425029854522629517577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174467800079612060345380205 65425425029854522629517577)
  ·
    refine ⟨49069068772390891972138183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65425425029854522629517577 49069068772390891972138183)
    ·
      refine ⟨73603603158586337958207275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49069068772390891972138183 73603603158586337958207275)
      ·
        refine ⟨110405404737879506937310913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73603603158586337958207275 110405404737879506937310913)
        ·
          refine ⟨82804053553409630202983185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110405404737879506937310913 82804053553409630202983185)
          ·
            refine ⟨62103040165057222652237389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82804053553409630202983185 62103040165057222652237389)
            ·
              refine ⟨23288640061896458494589021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62103040165057222652237389 23288640061896458494589021)
              ·
                refine ⟨8733240023211171935470883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23288640061896458494589021 8733240023211171935470883)
                ·
                  refine ⟨13099860034816757903206325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8733240023211171935470883 13099860034816757903206325)
                  ·
                    refine ⟨1228111878264071053425593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13099860034816757903206325 1228111878264071053425593)
                    ·
                      rfl

theorem cell23_7175218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 3, 1, 5].length) (baseStart_7175218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7175218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7175218 prefixEnd_7175218 := by exact prefixLift 7175218
  have htrace : WordTrace (prefixWord ++ tailWord_7175218) baseStart_7175218 baseEnd_7175218 := by
    simpa [prefixWord, tailWord_7175218, baseEnd_7175218] using wordTrace_append hprefix tailTrace_7175218
  have hstable : (prefixWord ++ tailWord_7175218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7175218).length < 2 ^ (prefixWord ++ tailWord_7175218).sum := by decide
  have hdescent : baseEnd_7175218 < baseStart_7175218 := by decide
  rcases family_descends (prefixWord ++ tailWord_7175218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7175241 : List Nat := [1, 2, 1, 1, 2, 2, 2, 1, 2, 6, 3]
def baseStart_7175241 : Nat := 118140960795 + 7175241 * 2 ^ 59
def prefixEnd_7175241 : Nat := 4983230072969 + 3 ^ 40 * 7175241 * 2
def baseEnd_7175241 : Nat := 3684347444847266570289173

theorem tailTrace_7175241 : CollatzResearch.WordTrace tailWord_7175241 prefixEnd_7175241 3684347444847266570289173 := by
  unfold tailWord_7175241
  simp only [CollatzResearch.WordTrace]
  refine ⟨261702538998334765446157577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174468359332223176964105051 261702538998334765446157577)
  ·
    refine ⟨196276904248751074084618183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261702538998334765446157577 196276904248751074084618183)
    ·
      refine ⟨294415356373126611126927275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196276904248751074084618183 294415356373126611126927275)
      ·
        refine ⟨441623034559689916690390913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294415356373126611126927275 441623034559689916690390913)
        ·
          refine ⟨331217275919767437517793185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 441623034559689916690390913 331217275919767437517793185)
          ·
            refine ⟨248412956939825578138344889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 331217275919767437517793185 248412956939825578138344889)
            ·
              refine ⟨186309717704869183603758667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 248412956939825578138344889 186309717704869183603758667)
              ·
                refine ⟨279464576557303775405638001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 186309717704869183603758667 279464576557303775405638001)
                ·
                  refine ⟨209598432417977831554228501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 279464576557303775405638001 209598432417977831554228501)
                  ·
                    refine ⟨9824926519592710854104461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 209598432417977831554228501 9824926519592710854104461)
                    ·
                      refine ⟨3684347444847266570289173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9824926519592710854104461 3684347444847266570289173)
                      ·
                        rfl

theorem cell23_7175241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 6, 3].length) (baseStart_7175241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7175241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7175241 prefixEnd_7175241 := by exact prefixLift 7175241
  have htrace : WordTrace (prefixWord ++ tailWord_7175241) baseStart_7175241 baseEnd_7175241 := by
    simpa [prefixWord, tailWord_7175241, baseEnd_7175241] using wordTrace_append hprefix tailTrace_7175241
  have hstable : (prefixWord ++ tailWord_7175241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7175241).length < 2 ^ (prefixWord ++ tailWord_7175241).sum := by decide
  have hdescent : baseEnd_7175241 < baseStart_7175241 := by decide
  rcases family_descends (prefixWord ++ tailWord_7175241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7175248 : List Nat := [2, 1, 1, 1, 1, 3, 1, 7, 2, 4]
def baseStart_7175248 : Nat := 118140960795 + 7175248 * 2 ^ 59
def prefixEnd_7175248 : Nat := 4983230072969 + 3 ^ 40 * 7175248 * 2
def baseEnd_7175248 : Nat := 1228117013070616014300547

theorem tailTrace_7175248 : CollatzResearch.WordTrace tailWord_7175248 prefixEnd_7175248 1228117013070616014300547 := by
  unfold tailWord_7175248
  simp only [CollatzResearch.WordTrace]
  refine ⟨130851397154654702820831199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174468529539539603761108265 130851397154654702820831199)
  ·
    refine ⟨196277095731982054231246799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130851397154654702820831199 196277095731982054231246799)
    ·
      refine ⟨294415643597973081346870199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196277095731982054231246799 294415643597973081346870199)
      ·
        refine ⟨441623465396959622020305299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294415643597973081346870199 441623465396959622020305299)
        ·
          refine ⟨662435198095439433030457949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 441623465396959622020305299 662435198095439433030457949)
          ·
            refine ⟨248413199285789787386421731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 662435198095439433030457949 248413199285789787386421731)
            ·
              refine ⟨372619798928684681079632597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248413199285789787386421731 372619798928684681079632597)
              ·
                refine ⟨8733276537391047212803889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 372619798928684681079632597 8733276537391047212803889)
                ·
                  refine ⟨6549957403043285409602917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8733276537391047212803889 6549957403043285409602917)
                  ·
                    refine ⟨1228117013070616014300547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6549957403043285409602917 1228117013070616014300547)
                    ·
                      rfl

theorem cell23_7175248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 7, 2, 4].length) (baseStart_7175248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7175248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7175248 prefixEnd_7175248 := by exact prefixLift 7175248
  have htrace : WordTrace (prefixWord ++ tailWord_7175248) baseStart_7175248 baseEnd_7175248 := by
    simpa [prefixWord, tailWord_7175248, baseEnd_7175248] using wordTrace_append hprefix tailTrace_7175248
  have hstable : (prefixWord ++ tailWord_7175248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7175248).length < 2 ^ (prefixWord ++ tailWord_7175248).sum := by decide
  have hdescent : baseEnd_7175248 < baseStart_7175248 := by decide
  rcases family_descends (prefixWord ++ tailWord_7175248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7175266 : List Nat := [3, 3, 2, 2, 1, 3, 1, 3, 1, 1, 3]
def baseStart_7175266 : Nat := 118140960795 + 7175266 * 2 ^ 59
def prefixEnd_7175266 : Nat := 4983230072969 + 3 ^ 40 * 7175266 * 2
def baseEnd_7175266 : Nat := 3684360281863628972476559

theorem tailTrace_7175266 : CollatzResearch.WordTrace tailWord_7175266 prefixEnd_7175266 3684360281863628972476559 := by
  unfold tailWord_7175266
  simp only [CollatzResearch.WordTrace]
  refine ⟨65425862705811048678954413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174468967215496129810545101 65425862705811048678954413)
  ·
    refine ⟨24534698514679143254607905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65425862705811048678954413 24534698514679143254607905)
    ·
      refine ⟨18401023886009357440955929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24534698514679143254607905 18401023886009357440955929)
      ·
        refine ⟨13800767914507018080716947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18401023886009357440955929 13800767914507018080716947)
        ·
          refine ⟨20701151871760527121075421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13800767914507018080716947 20701151871760527121075421)
          ·
            refine ⟨7762931951910197670403283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20701151871760527121075421 7762931951910197670403283)
            ·
              refine ⟨11644397927865296505604925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7762931951910197670403283 11644397927865296505604925)
              ·
                refine ⟨4366649222949486189601847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11644397927865296505604925 4366649222949486189601847)
                ·
                  refine ⟨6549973834424229284402771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4366649222949486189601847 6549973834424229284402771)
                  ·
                    refine ⟨9824960751636343926604157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6549973834424229284402771 9824960751636343926604157)
                    ·
                      refine ⟨3684360281863628972476559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9824960751636343926604157 3684360281863628972476559)
                      ·
                        rfl

theorem cell23_7175266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_7175266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7175266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7175266 prefixEnd_7175266 := by exact prefixLift 7175266
  have htrace : WordTrace (prefixWord ++ tailWord_7175266) baseStart_7175266 baseEnd_7175266 := by
    simpa [prefixWord, tailWord_7175266, baseEnd_7175266] using wordTrace_append hprefix tailTrace_7175266
  have hstable : (prefixWord ++ tailWord_7175266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7175266).length < 2 ^ (prefixWord ++ tailWord_7175266).sum := by decide
  have hdescent : baseEnd_7175266 < baseStart_7175266 := by decide
  rcases family_descends (prefixWord ++ tailWord_7175266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7175278 : List Nat := [4, 1, 2, 2, 1, 4, 9]
def baseStart_7175278 : Nat := 118140960795 + 7175278 * 2 ^ 59
def prefixEnd_7175278 : Nat := 4983230072969 + 3 ^ 40 * 7175278 * 2
def baseEnd_7175278 : Nat := 45486005476931887969463

theorem tailTrace_7175278 : CollatzResearch.WordTrace tailWord_7175278 prefixEnd_7175278 45486005476931887969463 := by
  unfold tailWord_7175278
  simp only [CollatzResearch.WordTrace]
  refine ⟨32712986062400090095656811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174469258999467147176836325 32712986062400090095656811)
  ·
    refine ⟨49069479093600135143485217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32712986062400090095656811 49069479093600135143485217)
    ·
      refine ⟨36802109320200101357613913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49069479093600135143485217 36802109320200101357613913)
      ·
        refine ⟨27601581990150076018210435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36802109320200101357613913 27601581990150076018210435)
        ·
          refine ⟨41402372985225114027315653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27601581990150076018210435 41402372985225114027315653)
          ·
            refine ⟨7762944934729708880121685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41402372985225114027315653 7762944934729708880121685)
            ·
              refine ⟨45486005476931887969463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7762944934729708880121685 45486005476931887969463)
              ·
                rfl

theorem cell23_7175278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 9].length) (baseStart_7175278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7175278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7175278 prefixEnd_7175278 := by exact prefixLift 7175278
  have htrace : WordTrace (prefixWord ++ tailWord_7175278) baseStart_7175278 baseEnd_7175278 := by
    simpa [prefixWord, tailWord_7175278, baseEnd_7175278] using wordTrace_append hprefix tailTrace_7175278
  have hstable : (prefixWord ++ tailWord_7175278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7175278).length < 2 ^ (prefixWord ++ tailWord_7175278).sum := by decide
  have hdescent : baseEnd_7175278 < baseStart_7175278 := by decide
  rcases family_descends (prefixWord ++ tailWord_7175278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7175289 : List Nat := [1, 2, 1, 3, 5, 2, 1, 1, 3, 2, 2]
def baseStart_7175289 : Nat := 118140960795 + 7175289 * 2 ^ 59
def prefixEnd_7175289 : Nat := 4983230072969 + 3 ^ 40 * 7175289 * 2
def baseEnd_7175289 : Nat := 3684372091918682382488953

theorem tailTrace_7175289 : CollatzResearch.WordTrace tailWord_7175289 prefixEnd_7175289 3684372091918682382488953 := by
  unfold tailWord_7175289
  simp only [CollatzResearch.WordTrace]
  refine ⟨261704289702160869643904921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174469526468107246429269947 261704289702160869643904921)
  ·
    refine ⟨196278217276620652232928691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261704289702160869643904921 196278217276620652232928691)
    ·
      refine ⟨294417325914930978349393037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196278217276620652232928691 294417325914930978349393037)
      ·
        refine ⟨110406497218099116881022389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 294417325914930978349393037 110406497218099116881022389)
        ·
          refine ⟨10350609114196792207595849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 110406497218099116881022389 10350609114196792207595849)
          ·
            refine ⟨7762956835647594155696887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10350609114196792207595849 7762956835647594155696887)
            ·
              refine ⟨11644435253471391233545331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7762956835647594155696887 11644435253471391233545331)
              ·
                refine ⟨17466652880207086850317997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11644435253471391233545331 17466652880207086850317997)
                ·
                  refine ⟨6549994830077657568869249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17466652880207086850317997 6549994830077657568869249)
                  ·
                    refine ⟨4912496122558243176651937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6549994830077657568869249 4912496122558243176651937)
                    ·
                      refine ⟨3684372091918682382488953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4912496122558243176651937 3684372091918682382488953)
                      ·
                        rfl

theorem cell23_7175289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 1, 3, 2, 2].length) (baseStart_7175289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7175289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7175289 prefixEnd_7175289 := by exact prefixLift 7175289
  have htrace : WordTrace (prefixWord ++ tailWord_7175289) baseStart_7175289 baseEnd_7175289 := by
    simpa [prefixWord, tailWord_7175289, baseEnd_7175289] using wordTrace_append hprefix tailTrace_7175289
  have hstable : (prefixWord ++ tailWord_7175289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7175289).length < 2 ^ (prefixWord ++ tailWord_7175289).sum := by decide
  have hdescent : baseEnd_7175289 < baseStart_7175289 := by decide
  rcases family_descends (prefixWord ++ tailWord_7175289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7175321 : List Nat := [1, 2, 1, 2, 1, 2, 1, 1, 6, 6]
def baseStart_7175321 : Nat := 118140960795 + 7175321 * 2 ^ 59
def prefixEnd_7175321 : Nat := 4983230072969 + 3 ^ 40 * 7175321 * 2
def baseEnd_7175321 : Nat := 1228129507766542085762935

theorem tailTrace_7175321 : CollatzResearch.WordTrace tailWord_7175321 prefixEnd_7175321 1228129507766542085762935 := by
  unfold tailWord_7175321
  simp only [CollatzResearch.WordTrace]
  refine ⟨261705456838044939109069817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174470304558696626072713211 261705456838044939109069817)
  ·
    refine ⟨196279092628533704331802363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261705456838044939109069817 196279092628533704331802363)
    ·
      refine ⟨294418638942800556497703545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196279092628533704331802363 294418638942800556497703545)
      ·
        refine ⟨220813979207100417373277659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 294418638942800556497703545 220813979207100417373277659)
        ·
          refine ⟨331220968810650626059916489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220813979207100417373277659 331220968810650626059916489)
          ·
            refine ⟨248415726607987969544937367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 331220968810650626059916489 248415726607987969544937367)
            ·
              refine ⟨372623589911981954317406051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248415726607987969544937367 372623589911981954317406051)
              ·
                refine ⟨558935384867972931476109077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 372623589911981954317406051 558935384867972931476109077)
                ·
                  refine ⟨26200096165686231162942613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 558935384867972931476109077 26200096165686231162942613)
                  ·
                    refine ⟨1228129507766542085762935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26200096165686231162942613 1228129507766542085762935)
                    ·
                      rfl

theorem cell23_7175321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 6, 6].length) (baseStart_7175321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7175321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7175321 prefixEnd_7175321 := by exact prefixLift 7175321
  have htrace : WordTrace (prefixWord ++ tailWord_7175321) baseStart_7175321 baseEnd_7175321 := by
    simpa [prefixWord, tailWord_7175321, baseEnd_7175321] using wordTrace_append hprefix tailTrace_7175321
  have hstable : (prefixWord ++ tailWord_7175321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7175321).length < 2 ^ (prefixWord ++ tailWord_7175321).sum := by decide
  have hdescent : baseEnd_7175321 < baseStart_7175321 := by decide
  rcases family_descends (prefixWord ++ tailWord_7175321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7175418 : List Nat := [3, 1, 1, 1, 1, 4, 1, 1, 3, 3, 4]
def baseStart_7175418 : Nat := 118140960795 + 7175418 * 2 ^ 59
def prefixEnd_7175418 : Nat := 4983230072969 + 3 ^ 40 * 7175418 * 2
def baseEnd_7175418 : Nat := 3684438330923112377775859

theorem tailTrace_7175418 : CollatzResearch.WordTrace tailWord_7175418 prefixEnd_7175418 3684438330923112377775859 := by
  unfold tailWord_7175418
  simp only [CollatzResearch.WordTrace]
  refine ⟨65427248679673381168837727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174472663145795683116900605 65427248679673381168837727)
  ·
    refine ⟨98140873019510071753256591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65427248679673381168837727 98140873019510071753256591)
    ·
      refine ⟨147211309529265107629884887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98140873019510071753256591 147211309529265107629884887)
      ·
        refine ⟨220816964293897661444827331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147211309529265107629884887 220816964293897661444827331)
        ·
          refine ⟨331225446440846492167240997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220816964293897661444827331 331225446440846492167240997)
          ·
            refine ⟨62104771207658717281357687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 331225446440846492167240997 62104771207658717281357687)
            ·
              refine ⟨93157156811488075922036531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62104771207658717281357687 93157156811488075922036531)
              ·
                refine ⟨139735735217232113883054797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93157156811488075922036531 139735735217232113883054797)
                ·
                  refine ⟨52400900706462042706145549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 139735735217232113883054797 52400900706462042706145549)
                  ·
                    refine ⟨19650337764923266014804581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52400900706462042706145549 19650337764923266014804581)
                    ·
                      refine ⟨3684438330923112377775859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19650337764923266014804581 3684438330923112377775859)
                      ·
                        rfl

theorem cell23_7175418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 3, 3, 4].length) (baseStart_7175418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7175418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7175418 prefixEnd_7175418 := by exact prefixLift 7175418
  have htrace : WordTrace (prefixWord ++ tailWord_7175418) baseStart_7175418 baseEnd_7175418 := by
    simpa [prefixWord, tailWord_7175418, baseEnd_7175418] using wordTrace_append hprefix tailTrace_7175418
  have hstable : (prefixWord ++ tailWord_7175418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7175418).length < 2 ^ (prefixWord ++ tailWord_7175418).sum := by decide
  have hdescent : baseEnd_7175418 < baseStart_7175418 := by decide
  rcases family_descends (prefixWord ++ tailWord_7175418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7175475 : List Nat := [1, 1, 1, 2, 5, 3, 1, 3, 6]
def baseStart_7175475 : Nat := 118140960795 + 7175475 * 2 ^ 59
def prefixEnd_7175475 : Nat := 4983230072969 + 3 ^ 40 * 7175475 * 2
def baseEnd_7175475 : Nat := 409385288813379850529233

theorem tailTrace_7175475 : CollatzResearch.WordTrace tailWord_7175475 prefixEnd_7175475 409385288813379850529233 := by
  unfold tailWord_7175475
  simp only [CollatzResearch.WordTrace]
  refine ⟨261711073679487023410175879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174474049119658015606783919 261711073679487023410175879)
  ·
    refine ⟨392566610519230535115263819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261711073679487023410175879 392566610519230535115263819)
    ·
      refine ⟨588849915778845802672895729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392566610519230535115263819 588849915778845802672895729)
      ·
        refine ⟨441637436834134352004671797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 588849915778845802672895729 441637436834134352004671797)
        ·
          refine ⟨41403509703200095500437981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 441637436834134352004671797 41403509703200095500437981)
          ·
            refine ⟨15526316138700035812664243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41403509703200095500437981 15526316138700035812664243)
            ·
              refine ⟨23289474208050053718996365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15526316138700035812664243 23289474208050053718996365)
              ·
                refine ⟨8733552828018770144623637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23289474208050053718996365 8733552828018770144623637)
                ·
                  refine ⟨409385288813379850529233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8733552828018770144623637 409385288813379850529233)
                  ·
                    rfl

theorem cell23_7175475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 3, 6].length) (baseStart_7175475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7175475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7175475 prefixEnd_7175475 := by exact prefixLift 7175475
  have htrace : WordTrace (prefixWord ++ tailWord_7175475) baseStart_7175475 baseEnd_7175475 := by
    simpa [prefixWord, tailWord_7175475, baseEnd_7175475] using wordTrace_append hprefix tailTrace_7175475
  have hstable : (prefixWord ++ tailWord_7175475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7175475).length < 2 ^ (prefixWord ++ tailWord_7175475).sum := by decide
  have hdescent : baseEnd_7175475 < baseStart_7175475 := by decide
  rcases family_descends (prefixWord ++ tailWord_7175475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7175489 : List Nat := [1, 2, 5, 2, 1, 2, 2, 1, 2, 2, 3]
def baseStart_7175489 : Nat := 118140960795 + 7175489 * 2 ^ 59
def prefixEnd_7175489 : Nat := 4983230072969 + 3 ^ 40 * 7175489 * 2
def baseEnd_7175489 : Nat := 3684474788049581599988033

theorem tailTrace_7175489 : CollatzResearch.WordTrace tailWord_7175489 prefixEnd_7175489 3684474788049581599988033 := by
  unfold tailWord_7175489
  simp only [CollatzResearch.WordTrace]
  refine ⟨261711584301436303801185521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174474389534290869200790347 261711584301436303801185521)
  ·
    refine ⟨196283688226077227850889141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261711584301436303801185521 196283688226077227850889141)
    ·
      refine ⟨18401595771194740111020857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 196283688226077227850889141 18401595771194740111020857)
      ·
        refine ⟨13801196828396055083265643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18401595771194740111020857 13801196828396055083265643)
        ·
          refine ⟨20701795242594082624898465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13801196828396055083265643 20701795242594082624898465)
          ·
            refine ⟨15526346431945561968673849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20701795242594082624898465 15526346431945561968673849)
            ·
              refine ⟨11644759823959171476505387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15526346431945561968673849 11644759823959171476505387)
              ·
                refine ⟨17467139735938757214758081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11644759823959171476505387 17467139735938757214758081)
                ·
                  refine ⟨13100354801954067911068561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17467139735938757214758081 13100354801954067911068561)
                  ·
                    refine ⟨9825266101465550933301421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13100354801954067911068561 9825266101465550933301421)
                    ·
                      refine ⟨3684474788049581599988033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9825266101465550933301421 3684474788049581599988033)
                      ·
                        rfl

theorem cell23_7175489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_7175489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7175489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7175489 prefixEnd_7175489 := by exact prefixLift 7175489
  have htrace : WordTrace (prefixWord ++ tailWord_7175489) baseStart_7175489 baseEnd_7175489 := by
    simpa [prefixWord, tailWord_7175489, baseEnd_7175489] using wordTrace_append hprefix tailTrace_7175489
  have hstable : (prefixWord ++ tailWord_7175489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7175489).length < 2 ^ (prefixWord ++ tailWord_7175489).sum := by decide
  have hdescent : baseEnd_7175489 < baseStart_7175489 := by decide
  rcases family_descends (prefixWord ++ tailWord_7175489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7175498 : List Nat := [3, 1, 2, 1, 1, 1, 1, 2, 1, 3, 7]
def baseStart_7175498 : Nat := 118140960795 + 7175498 * 2 ^ 59
def prefixEnd_7175498 : Nat := 4983230072969 + 3 ^ 40 * 7175498 * 2
def baseEnd_7175498 : Nat := 3684479409375472064775491

theorem tailTrace_7175498 : CollatzResearch.WordTrace tailWord_7175498 prefixEnd_7175498 3684479409375472064775491 := by
  unfold tailWord_7175498
  simp only [CollatzResearch.WordTrace]
  refine ⟨65427978139600924584565787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174474608372269132225508765 65427978139600924584565787)
  ·
    refine ⟨98141967209401386876848681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65427978139600924584565787 98141967209401386876848681)
    ·
      refine ⟨73606475407051040157636511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98141967209401386876848681 73606475407051040157636511)
      ·
        refine ⟨110409713110576560236454767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73606475407051040157636511 110409713110576560236454767)
        ·
          refine ⟨165614569665864840354682151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110409713110576560236454767 165614569665864840354682151)
          ·
            refine ⟨248421854498797260532023227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165614569665864840354682151 248421854498797260532023227)
            ·
              refine ⟨372632781748195890798034841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248421854498797260532023227 372632781748195890798034841)
              ·
                refine ⟨279474586311146918098526131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 372632781748195890798034841 279474586311146918098526131)
                ·
                  refine ⟨419211879466720377147789197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 279474586311146918098526131 419211879466720377147789197)
                  ·
                    refine ⟨157204454800020141430420949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 419211879466720377147789197 157204454800020141430420949)
                    ·
                      refine ⟨3684479409375472064775491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 157204454800020141430420949 3684479409375472064775491)
                      ·
                        rfl

theorem cell23_7175498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 1, 3, 7].length) (baseStart_7175498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7175498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7175498 prefixEnd_7175498 := by exact prefixLift 7175498
  have htrace : WordTrace (prefixWord ++ tailWord_7175498) baseStart_7175498 baseEnd_7175498 := by
    simpa [prefixWord, tailWord_7175498, baseEnd_7175498] using wordTrace_append hprefix tailTrace_7175498
  have hstable : (prefixWord ++ tailWord_7175498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7175498).length < 2 ^ (prefixWord ++ tailWord_7175498).sum := by decide
  have hdescent : baseEnd_7175498 < baseStart_7175498 := by decide
  rcases family_descends (prefixWord ++ tailWord_7175498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7175512 : List Nat := [2, 1, 2, 2, 1, 1, 3, 4, 2, 3, 2]
def baseStart_7175512 : Nat := 118140960795 + 7175512 * 2 ^ 59
def prefixEnd_7175512 : Nat := 4983230072969 + 3 ^ 40 * 7175512 * 2
def baseEnd_7175512 : Nat := 3684486598104635010000427

theorem tailTrace_7175512 : CollatzResearch.WordTrace tailWord_7175512 prefixEnd_7175512 3684486598104635010000427 := by
  unfold tailWord_7175512
  simp only [CollatzResearch.WordTrace]
  refine ⟨130856211590176489364636395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174474948786901985819515193 130856211590176489364636395)
  ·
    refine ⟨196284317385264734046954593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130856211590176489364636395 196284317385264734046954593)
    ·
      refine ⟨147213238038948550535215945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196284317385264734046954593 147213238038948550535215945)
      ·
        refine ⟨110409928529211412901411959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147213238038948550535215945 110409928529211412901411959)
        ·
          refine ⟨165614892793817119352117939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110409928529211412901411959 165614892793817119352117939)
          ·
            refine ⟨248422339190725679028176909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165614892793817119352117939 248422339190725679028176909)
            ·
              refine ⟨93158377196522129635566341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 248422339190725679028176909 93158377196522129635566341)
              ·
                refine ⟨17467195724347899306668689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93158377196522129635566341 17467195724347899306668689)
                ·
                  refine ⟨13100396793260924480001517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17467195724347899306668689 13100396793260924480001517)
                  ·
                    refine ⟨4912648797472846680000569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13100396793260924480001517 4912648797472846680000569)
                    ·
                      refine ⟨3684486598104635010000427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4912648797472846680000569 3684486598104635010000427)
                      ·
                        rfl

theorem cell23_7175512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 4, 2, 3, 2].length) (baseStart_7175512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7175512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7175512 prefixEnd_7175512 := by exact prefixLift 7175512
  have htrace : WordTrace (prefixWord ++ tailWord_7175512) baseStart_7175512 baseEnd_7175512 := by
    simpa [prefixWord, tailWord_7175512, baseEnd_7175512] using wordTrace_append hprefix tailTrace_7175512
  have hstable : (prefixWord ++ tailWord_7175512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7175512).length < 2 ^ (prefixWord ++ tailWord_7175512).sum := by decide
  have hdescent : baseEnd_7175512 < baseStart_7175512 := by decide
  rcases family_descends (prefixWord ++ tailWord_7175512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7175525 : List Nat := [1, 3, 1, 3, 1, 2, 1, 1, 5, 1, 4]
def baseStart_7175525 : Nat := 118140960795 + 7175525 * 2 ^ 59
def prefixEnd_7175525 : Nat := 4983230072969 + 3 ^ 40 * 7175525 * 2
def baseEnd_7175525 : Nat := 3684493273353143459137867

theorem tailTrace_7175525 : CollatzResearch.WordTrace tailWord_7175525 prefixEnd_7175525 3684493273353143459137867 := by
  unfold tailWord_7175525
  simp only [CollatzResearch.WordTrace]
  refine ⟨261712897329305881949496029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174475264886203921299664019 261712897329305881949496029)
  ·
    refine ⟨98142336498489705731061011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261712897329305881949496029 98142336498489705731061011)
    ·
      refine ⟨147213504747734558596591517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98142336498489705731061011 147213504747734558596591517)
      ·
        refine ⟨55205064280400459473721819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147213504747734558596591517 55205064280400459473721819)
        ·
          refine ⟨82807596420600689210582729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55205064280400459473721819 82807596420600689210582729)
          ·
            refine ⟨62105697315450516907937047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82807596420600689210582729 62105697315450516907937047)
            ·
              refine ⟨93158545973175775361905571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62105697315450516907937047 93158545973175775361905571)
              ·
                refine ⟨139737818959763663042858357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93158545973175775361905571 139737818959763663042858357)
                ·
                  refine ⟨13100420527477843410267971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 139737818959763663042858357 13100420527477843410267971)
                  ·
                    refine ⟨19650630791216765115401957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13100420527477843410267971 19650630791216765115401957)
                    ·
                      refine ⟨3684493273353143459137867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19650630791216765115401957 3684493273353143459137867)
                      ·
                        rfl

theorem cell23_7175525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_7175525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7175525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7175525 prefixEnd_7175525 := by exact prefixLift 7175525
  have htrace : WordTrace (prefixWord ++ tailWord_7175525) baseStart_7175525 baseEnd_7175525 := by
    simpa [prefixWord, tailWord_7175525, baseEnd_7175525] using wordTrace_append hprefix tailTrace_7175525
  have hstable : (prefixWord ++ tailWord_7175525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7175525).length < 2 ^ (prefixWord ++ tailWord_7175525).sum := by decide
  have hdescent : baseEnd_7175525 < baseStart_7175525 := by decide
  rcases family_descends (prefixWord ++ tailWord_7175525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7175535 : List Nat := [1, 1, 2, 1, 3, 1, 6, 1, 1, 6]
def baseStart_7175535 : Nat := 118140960795 + 7175535 * 2 ^ 59
def prefixEnd_7175535 : Nat := 4983230072969 + 3 ^ 40 * 7175535 * 2
def baseEnd_7175535 : Nat := 1228166136053229473337607

theorem tailTrace_7175535 : CollatzResearch.WordTrace tailWord_7175535 prefixEnd_7175535 1228166136053229473337607 := by
  unfold tailWord_7175535
  simp only [CollatzResearch.WordTrace]
  refine ⟨261713262059269653657360059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174475508039513102438240039 261713262059269653657360059)
  ·
    refine ⟨392569893088904480486040089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261713262059269653657360059 392569893088904480486040089)
    ·
      refine ⟨294427419816678360364530067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 392569893088904480486040089 294427419816678360364530067)
      ·
        refine ⟨441641129725017540546795101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294427419816678360364530067 441641129725017540546795101)
        ·
          refine ⟨165615423646881577705048163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 441641129725017540546795101 165615423646881577705048163)
          ·
            refine ⟨248423135470322366557572245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165615423646881577705048163 248423135470322366557572245)
            ·
              refine ⟨11644834475171360932386199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 248423135470322366557572245 11644834475171360932386199)
              ·
                refine ⟨17467251712757041398579299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11644834475171360932386199 17467251712757041398579299)
                ·
                  refine ⟨26200877569135562097868949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17467251712757041398579299 26200877569135562097868949)
                  ·
                    refine ⟨1228166136053229473337607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26200877569135562097868949 1228166136053229473337607)
                    ·
                      rfl

theorem cell23_7175535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 1, 1, 6].length) (baseStart_7175535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7175535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7175535 prefixEnd_7175535 := by exact prefixLift 7175535
  have htrace : WordTrace (prefixWord ++ tailWord_7175535) baseStart_7175535 baseEnd_7175535 := by
    simpa [prefixWord, tailWord_7175535, baseEnd_7175535] using wordTrace_append hprefix tailTrace_7175535
  have hstable : (prefixWord ++ tailWord_7175535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7175535).length < 2 ^ (prefixWord ++ tailWord_7175535).sum := by decide
  have hdescent : baseEnd_7175535 < baseStart_7175535 := by decide
  rcases family_descends (prefixWord ++ tailWord_7175535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7175553 : List Nat := [1, 2, 4, 3, 2, 1, 2, 3, 1, 1, 3]
def baseStart_7175553 : Nat := 118140960795 + 7175553 * 2 ^ 59
def prefixEnd_7175553 : Nat := 4983230072969 + 3 ^ 40 * 7175553 * 2
def baseEnd_7175553 : Nat := 3684507650811469349587739

theorem tailTrace_7175553 : CollatzResearch.WordTrace tailWord_7175553 prefixEnd_7175553 3684507650811469349587739 := by
  unfold tailWord_7175553
  simp only [CollatzResearch.WordTrace]
  refine ⟨261713918573204442731515313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174475945715469628487676875 261713918573204442731515313)
  ·
    refine ⟨196285438929903332048636485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261713918573204442731515313 196285438929903332048636485)
    ·
      refine ⟨36803519799356874759119341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 196285438929903332048636485 36803519799356874759119341)
      ·
        refine ⟨13801319924758828034669753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36803519799356874759119341 13801319924758828034669753)
        ·
          refine ⟨10350989943569121026002315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13801319924758828034669753 10350989943569121026002315)
          ·
            refine ⟨15526484915353681539003473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10350989943569121026002315 15526484915353681539003473)
            ·
              refine ⟨11644863686515261154252605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15526484915353681539003473 11644863686515261154252605)
              ·
                refine ⟨4366823882443222932844727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11644863686515261154252605 4366823882443222932844727)
                ·
                  refine ⟨6550235823664834399267091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4366823882443222932844727 6550235823664834399267091)
                  ·
                    refine ⟨9825353735497251598900637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6550235823664834399267091 9825353735497251598900637)
                    ·
                      refine ⟨3684507650811469349587739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9825353735497251598900637 3684507650811469349587739)
                      ·
                        rfl

theorem cell23_7175553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_7175553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7175553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7175553 prefixEnd_7175553 := by exact prefixLift 7175553
  have htrace : WordTrace (prefixWord ++ tailWord_7175553) baseStart_7175553 baseEnd_7175553 := by
    simpa [prefixWord, tailWord_7175553, baseEnd_7175553] using wordTrace_append hprefix tailTrace_7175553
  have hstable : (prefixWord ++ tailWord_7175553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7175553).length < 2 ^ (prefixWord ++ tailWord_7175553).sum := by decide
  have hdescent : baseEnd_7175553 < baseStart_7175553 := by decide
  rcases family_descends (prefixWord ++ tailWord_7175553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7175559 : List Nat := [1, 1, 4, 2, 2, 2, 4, 1, 1, 1, 4]
def baseStart_7175559 : Nat := 118140960795 + 7175559 * 2 ^ 59
def prefixEnd_7175559 : Nat := 4983230072969 + 3 ^ 40 * 7175559 * 2
def baseEnd_7175559 : Nat := 3684510731695396326112711

theorem tailTrace_7175559 : CollatzResearch.WordTrace tailWord_7175559 prefixEnd_7175559 3684510731695396326112711 := by
  unfold tailWord_7175559
  simp only [CollatzResearch.WordTrace]
  refine ⟨261714137411182705756233731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174476091607455137170822487 261714137411182705756233731)
  ·
    refine ⟨392571206116774058634350597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261714137411182705756233731 392571206116774058634350597)
    ·
      refine ⟨73607101146895135993940737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 392571206116774058634350597 73607101146895135993940737)
      ·
        refine ⟨55205325860171351995455553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73607101146895135993940737 55205325860171351995455553)
        ·
          refine ⟨41403994395128513996591665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55205325860171351995455553 41403994395128513996591665)
          ·
            refine ⟨31052995796346385497443749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41403994395128513996591665 31052995796346385497443749)
            ·
              refine ⟨5822436711814947280770703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31052995796346385497443749 5822436711814947280770703)
              ·
                refine ⟨8733655067722420921156055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5822436711814947280770703 8733655067722420921156055)
                ·
                  refine ⟨13100482601583631381734083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8733655067722420921156055 13100482601583631381734083)
                  ·
                    refine ⟨19650723902375447072601125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13100482601583631381734083 19650723902375447072601125)
                    ·
                      refine ⟨3684510731695396326112711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19650723902375447072601125 3684510731695396326112711)
                      ·
                        rfl

theorem cell23_7175559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 4, 1, 1, 1, 4].length) (baseStart_7175559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7175559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7175559 prefixEnd_7175559 := by exact prefixLift 7175559
  have htrace : WordTrace (prefixWord ++ tailWord_7175559) baseStart_7175559 baseEnd_7175559 := by
    simpa [prefixWord, tailWord_7175559, baseEnd_7175559] using wordTrace_append hprefix tailTrace_7175559
  have hstable : (prefixWord ++ tailWord_7175559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7175559).length < 2 ^ (prefixWord ++ tailWord_7175559).sum := by decide
  have hdescent : baseEnd_7175559 < baseStart_7175559 := by decide
  rcases family_descends (prefixWord ++ tailWord_7175559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7175586 : List Nat := [3, 3, 1, 2, 1, 3, 3, 1, 2, 4]
def baseStart_7175586 : Nat := 118140960795 + 7175586 * 2 ^ 59
def prefixEnd_7175586 : Nat := 4983230072969 + 3 ^ 40 * 7175586 * 2
def baseEnd_7175586 : Nat := 1228174865224355906825029

theorem tailTrace_7175586 : CollatzResearch.WordTrace tailWord_7175586 prefixEnd_7175586 1228174865224355906825029 := by
  unfold tailWord_7175586
  simp only [CollatzResearch.WordTrace]
  refine ⟨65428780545521222341866653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174476748121389926244977741 65428780545521222341866653)
  ·
    refine ⟨24535792704570458378199995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65428780545521222341866653 24535792704570458378199995)
    ·
      refine ⟨36803689056855687567299993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24535792704570458378199995 36803689056855687567299993)
      ·
        refine ⟨27602766792641765675474995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36803689056855687567299993 27602766792641765675474995)
        ·
          refine ⟨41404150188962648513212493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27602766792641765675474995 41404150188962648513212493)
          ·
            refine ⟨15526556320860993192454685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41404150188962648513212493 15526556320860993192454685)
            ·
              refine ⟨5822458620322872447170507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15526556320860993192454685 5822458620322872447170507)
              ·
                refine ⟨8733687930484308670755761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5822458620322872447170507 8733687930484308670755761)
                ·
                  refine ⟨6550265947863231503066821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8733687930484308670755761 6550265947863231503066821)
                  ·
                    refine ⟨1228174865224355906825029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6550265947863231503066821 1228174865224355906825029)
                    ·
                      rfl

theorem cell23_7175586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 3, 1, 2, 4].length) (baseStart_7175586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7175586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7175586 prefixEnd_7175586 := by exact prefixLift 7175586
  have htrace : WordTrace (prefixWord ++ tailWord_7175586) baseStart_7175586 baseEnd_7175586 := by
    simpa [prefixWord, tailWord_7175586, baseEnd_7175586] using wordTrace_append hprefix tailTrace_7175586
  have hstable : (prefixWord ++ tailWord_7175586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7175586).length < 2 ^ (prefixWord ++ tailWord_7175586).sum := by decide
  have hdescent : baseEnd_7175586 < baseStart_7175586 := by decide
  rcases family_descends (prefixWord ++ tailWord_7175586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7175619 : List Nat := [1, 1, 1, 3, 1, 1, 6, 3, 1, 3, 2]
def baseStart_7175619 : Nat := 118140960795 + 7175619 * 2 ^ 59
def prefixEnd_7175619 : Nat := 4983230072969 + 3 ^ 40 * 7175619 * 2
def baseEnd_7175619 : Nat := 3684541540534666091362435

theorem tailTrace_7175619 : CollatzResearch.WordTrace tailWord_7175619 prefixEnd_7175619 3684541540534666091362435 := by
  unfold tailWord_7175619
  simp only [CollatzResearch.WordTrace]
  refine ⟨261716325790965336003417911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174477550527310224002278607 261716325790965336003417911)
  ·
    refine ⟨392574488686448004005126867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261716325790965336003417911 392574488686448004005126867)
    ·
      refine ⟨588861733029672006007690301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392574488686448004005126867 588861733029672006007690301)
      ·
        refine ⟨220823149886127002252883863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 588861733029672006007690301 220823149886127002252883863)
        ·
          refine ⟨331234724829190503379325795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220823149886127002252883863 331234724829190503379325795)
          ·
            refine ⟨496852087243785755068988693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 331234724829190503379325795 496852087243785755068988693)
            ·
              refine ⟨23289941589552457268858845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 496852087243785755068988693 23289941589552457268858845)
              ·
                refine ⟨8733728096082171475822067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23289941589552457268858845 8733728096082171475822067)
                ·
                  refine ⟨13100592144123257213733101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8733728096082171475822067 13100592144123257213733101)
                  ·
                    refine ⟨4912722054046221455149913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13100592144123257213733101 4912722054046221455149913)
                    ·
                      refine ⟨3684541540534666091362435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4912722054046221455149913 3684541540534666091362435)
                      ·
                        rfl

theorem cell23_7175619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 3, 1, 3, 2].length) (baseStart_7175619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7175619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7175619 prefixEnd_7175619 := by exact prefixLift 7175619
  have htrace : WordTrace (prefixWord ++ tailWord_7175619) baseStart_7175619 baseEnd_7175619 := by
    simpa [prefixWord, tailWord_7175619, baseEnd_7175619] using wordTrace_append hprefix tailTrace_7175619
  have hstable : (prefixWord ++ tailWord_7175619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7175619).length < 2 ^ (prefixWord ++ tailWord_7175619).sum := by decide
  have hdescent : baseEnd_7175619 < baseStart_7175619 := by decide
  rcases family_descends (prefixWord ++ tailWord_7175619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7175632 : List Nat := [2, 1, 1, 1, 1, 2, 2, 4, 3, 4, 2]
def baseStart_7175632 : Nat := 118140960795 + 7175632 * 2 ^ 59
def prefixEnd_7175632 : Nat := 4983230072969 + 3 ^ 40 * 7175632 * 2
def baseEnd_7175632 : Nat := 3684548215783174540499875

theorem tailTrace_7175632 : CollatzResearch.WordTrace tailWord_7175632 prefixEnd_7175632 3684548215783174540499875 := by
  unfold tailWord_7175632
  simp only [CollatzResearch.WordTrace]
  refine ⟨130858399969959119611820575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174477866626612159482427433 130858399969959119611820575)
  ·
    refine ⟨196287599954938679417730863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130858399969959119611820575 196287599954938679417730863)
    ·
      refine ⟨294431399932408019126596295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196287599954938679417730863 294431399932408019126596295)
      ·
        refine ⟨441647099898612028689894443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294431399932408019126596295 441647099898612028689894443)
        ·
          refine ⟨662470649847918043034841665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 441647099898612028689894443 662470649847918043034841665)
          ·
            refine ⟨496852987385938532276131249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 662470649847918043034841665 496852987385938532276131249)
            ·
              refine ⟨372639740539453899207098437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 496852987385938532276131249 372639740539453899207098437)
              ·
                refine ⟨69869951351147606101330957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 372639740539453899207098437 69869951351147606101330957)
                ·
                  refine ⟨26201231756680352287999109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69869951351147606101330957 26201231756680352287999109)
                  ·
                    refine ⟨4912730954377566053999833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26201231756680352287999109 4912730954377566053999833)
                    ·
                      refine ⟨3684548215783174540499875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4912730954377566053999833 3684548215783174540499875)
                      ·
                        rfl

theorem cell23_7175632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 3, 4, 2].length) (baseStart_7175632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7175632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7175632 prefixEnd_7175632 := by exact prefixLift 7175632
  have htrace : WordTrace (prefixWord ++ tailWord_7175632) baseStart_7175632 baseEnd_7175632 := by
    simpa [prefixWord, tailWord_7175632, baseEnd_7175632] using wordTrace_append hprefix tailTrace_7175632
  have hstable : (prefixWord ++ tailWord_7175632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7175632).length < 2 ^ (prefixWord ++ tailWord_7175632).sum := by decide
  have hdescent : baseEnd_7175632 < baseStart_7175632 := by decide
  rcases family_descends (prefixWord ++ tailWord_7175632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7175653 : List Nat := [1, 3, 1, 5, 1, 3, 1, 2, 1, 3, 2]
def baseStart_7175653 : Nat := 118140960795 + 7175653 * 2 ^ 59
def prefixEnd_7175653 : Nat := 4983230072969 + 3 ^ 40 * 7175653 * 2
def baseEnd_7175653 : Nat := 3684558998876918958337279

theorem tailTrace_7175653 : CollatzResearch.WordTrace tailWord_7175653 prefixEnd_7175653 3684558998876918958337279 := by
  unfold tailWord_7175653
  simp only [CollatzResearch.WordTrace]
  refine ⟨261717565872842159810155613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174478377248561439873437075 261717565872842159810155613)
  ·
    refine ⟨98144087202315809928808355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261717565872842159810155613 98144087202315809928808355)
    ·
      refine ⟨147216130803473714893212533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98144087202315809928808355 147216130803473714893212533)
      ·
        refine ⟨13801512262825660771238675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 147216130803473714893212533 13801512262825660771238675)
        ·
          refine ⟨20702268394238491156858013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13801512262825660771238675 20702268394238491156858013)
          ·
            refine ⟨7763350647839434183821755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20702268394238491156858013 7763350647839434183821755)
            ·
              refine ⟨11645025971759151275732633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7763350647839434183821755 11645025971759151275732633)
              ·
                refine ⟨8733769478819363456799475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11645025971759151275732633 8733769478819363456799475)
                ·
                  refine ⟨13100654218229045185199213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8733769478819363456799475 13100654218229045185199213)
                  ·
                    refine ⟨4912745331835891944449705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13100654218229045185199213 4912745331835891944449705)
                    ·
                      refine ⟨3684558998876918958337279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4912745331835891944449705 3684558998876918958337279)
                      ·
                        rfl

theorem cell23_7175653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_7175653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7175653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7175653 prefixEnd_7175653 := by exact prefixLift 7175653
  have htrace : WordTrace (prefixWord ++ tailWord_7175653) baseStart_7175653 baseEnd_7175653 := by
    simpa [prefixWord, tailWord_7175653, baseEnd_7175653] using wordTrace_append hprefix tailTrace_7175653
  have hstable : (prefixWord ++ tailWord_7175653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7175653).length < 2 ^ (prefixWord ++ tailWord_7175653).sum := by decide
  have hdescent : baseEnd_7175653 < baseStart_7175653 := by decide
  rcases family_descends (prefixWord ++ tailWord_7175653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7175666 : List Nat := [3, 2, 1, 4, 1, 2, 1, 2, 1, 4, 2]
def baseStart_7175666 : Nat := 118140960795 + 7175666 * 2 ^ 59
def prefixEnd_7175666 : Nat := 4983230072969 + 3 ^ 40 * 7175666 * 2
def baseEnd_7175666 : Nat := 3684565674125427407474719

theorem tailTrace_7175666 : CollatzResearch.WordTrace tailWord_7175666 prefixEnd_7175666 3684565674125427407474719 := by
  unfold tailWord_7175666
  simp only [CollatzResearch.WordTrace]
  refine ⟨65429510005448765757594713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174478693347863375353585901 65429510005448765757594713)
  ·
    refine ⟨49072132504086574318196035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65429510005448765757594713 49072132504086574318196035)
    ·
      refine ⟨73608198756129861477294053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49072132504086574318196035 73608198756129861477294053)
      ·
        refine ⟨13801537266774349026992635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73608198756129861477294053 13801537266774349026992635)
        ·
          refine ⟨20702305900161523540488953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13801537266774349026992635 20702305900161523540488953)
          ·
            refine ⟨15526729425121142655366715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20702305900161523540488953 15526729425121142655366715)
            ·
              refine ⟨23290094137681713983050073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15526729425121142655366715 23290094137681713983050073)
              ·
                refine ⟨17467570603261285487287555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23290094137681713983050073 17467570603261285487287555)
                ·
                  refine ⟨26201355904891928230931333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17467570603261285487287555 26201355904891928230931333)
                  ·
                    refine ⟨4912754232167236543299625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26201355904891928230931333 4912754232167236543299625)
                    ·
                      refine ⟨3684565674125427407474719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4912754232167236543299625 3684565674125427407474719)
                      ·
                        rfl

theorem cell23_7175666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_7175666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7175666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7175666 prefixEnd_7175666 := by exact prefixLift 7175666
  have htrace : WordTrace (prefixWord ++ tailWord_7175666) baseStart_7175666 baseEnd_7175666 := by
    simpa [prefixWord, tailWord_7175666, baseEnd_7175666] using wordTrace_append hprefix tailTrace_7175666
  have hstable : (prefixWord ++ tailWord_7175666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7175666).length < 2 ^ (prefixWord ++ tailWord_7175666).sum := by decide
  have hdescent : baseEnd_7175666 < baseStart_7175666 := by decide
  rcases family_descends (prefixWord ++ tailWord_7175666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7175669 : List Nat := [1, 3, 5, 1, 1, 1, 2, 1, 2, 1, 5]
def baseStart_7175669 : Nat := 118140960795 + 7175669 * 2 ^ 59
def prefixEnd_7175669 : Nat := 4983230072969 + 3 ^ 40 * 7175669 * 2
def baseEnd_7175669 : Nat := 3684567214567390895737205

theorem tailTrace_7175669 : CollatzResearch.WordTrace tailWord_7175669 prefixEnd_7175669 3684567214567390895737205 := by
  unfold tailWord_7175669
  simp only [CollatzResearch.WordTrace]
  refine ⟨261718149440784194542738061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174478766293856129695158707 261718149440784194542738061)
  ·
    refine ⟨98144306040294072953526773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261718149440784194542738061 98144306040294072953526773)
    ·
      refine ⟨9201028691277569339393135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 98144306040294072953526773 9201028691277569339393135)
      ·
        refine ⟨13801543036916354009089703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9201028691277569339393135 13801543036916354009089703)
        ·
          refine ⟨20702314555374531013634555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13801543036916354009089703 20702314555374531013634555)
          ·
            refine ⟨31053471833061796520451833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20702314555374531013634555 31053471833061796520451833)
            ·
              refine ⟨23290103874796347390338875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31053471833061796520451833 23290103874796347390338875)
              ·
                refine ⟨34935155812194521085508313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23290103874796347390338875 34935155812194521085508313)
                ·
                  refine ⟨26201366859145890814131235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34935155812194521085508313 26201366859145890814131235)
                  ·
                    refine ⟨39302050288718836221196853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26201366859145890814131235 39302050288718836221196853)
                    ·
                      refine ⟨3684567214567390895737205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39302050288718836221196853 3684567214567390895737205)
                      ·
                        rfl

theorem cell23_7175669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_7175669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7175669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7175669 prefixEnd_7175669 := by exact prefixLift 7175669
  have htrace : WordTrace (prefixWord ++ tailWord_7175669) baseStart_7175669 baseEnd_7175669 := by
    simpa [prefixWord, tailWord_7175669, baseEnd_7175669] using wordTrace_append hprefix tailTrace_7175669
  have hstable : (prefixWord ++ tailWord_7175669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7175669).length < 2 ^ (prefixWord ++ tailWord_7175669).sum := by decide
  have hdescent : baseEnd_7175669 < baseStart_7175669 := by decide
  rcases family_descends (prefixWord ++ tailWord_7175669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7175685 : List Nat := [1, 3, 1, 1, 2, 2, 1, 2, 3, 7]
def baseStart_7175685 : Nat := 118140960795 + 7175685 * 2 ^ 59
def prefixEnd_7175685 : Nat := 4983230072969 + 3 ^ 40 * 7175685 * 2
def baseEnd_7175685 : Nat := 1228191810085954277712377

theorem tailTrace_7175685 : CollatzResearch.WordTrace tailWord_7175685 prefixEnd_7175685 1228191810085954277712377 := by
  unfold tailWord_7175685
  simp only [CollatzResearch.WordTrace]
  refine ⟨261718733008726229275320509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174479155339150819516880339 261718733008726229275320509)
  ·
    refine ⟨98144524878272335978245191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261718733008726229275320509 98144524878272335978245191)
    ·
      refine ⟨147216787317408503967367787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98144524878272335978245191 147216787317408503967367787)
      ·
        refine ⟨220825180976112755951051681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147216787317408503967367787 220825180976112755951051681)
        ·
          refine ⟨165618885732084566963288761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220825180976112755951051681 165618885732084566963288761)
          ·
            refine ⟨124214164299063425222466571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165618885732084566963288761 124214164299063425222466571)
            ·
              refine ⟨186321246448595137833699857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124214164299063425222466571 186321246448595137833699857)
              ·
                refine ⟨139740934836446353375274893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 186321246448595137833699857 139740934836446353375274893)
                ·
                  refine ⟨52402850563667382515728085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 139740934836446353375274893 52402850563667382515728085)
                  ·
                    refine ⟨1228191810085954277712377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52402850563667382515728085 1228191810085954277712377)
                    ·
                      rfl

theorem cell23_7175685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 3, 7].length) (baseStart_7175685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7175685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7175685 prefixEnd_7175685 := by exact prefixLift 7175685
  have htrace : WordTrace (prefixWord ++ tailWord_7175685) baseStart_7175685 baseEnd_7175685 := by
    simpa [prefixWord, tailWord_7175685, baseEnd_7175685] using wordTrace_append hprefix tailTrace_7175685
  have hstable : (prefixWord ++ tailWord_7175685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7175685).length < 2 ^ (prefixWord ++ tailWord_7175685).sum := by decide
  have hdescent : baseEnd_7175685 < baseStart_7175685 := by decide
  rcases family_descends (prefixWord ++ tailWord_7175685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7175695 : List Nat := [1, 1, 2, 1, 1, 1, 2, 2, 5, 2, 5]
def baseStart_7175695 : Nat := 118140960795 + 7175695 * 2 ^ 59
def prefixEnd_7175695 : Nat := 4983230072969 + 3 ^ 40 * 7175695 * 2
def baseEnd_7175695 : Nat := 3684580565064407794012085

theorem tailTrace_7175695 : CollatzResearch.WordTrace tailWord_7175695 prefixEnd_7175695 3684580565064407794012085 := by
  unfold tailWord_7175695
  simp only [CollatzResearch.WordTrace]
  refine ⟨261719097738690000983184539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174479398492460000655456359 261719097738690000983184539)
  ·
    refine ⟨392578646608035001474776809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261719097738690000983184539 392578646608035001474776809)
    ·
      refine ⟨294433984956026251106082607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 392578646608035001474776809 294433984956026251106082607)
      ·
        refine ⟨441650977434039376659123911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294433984956026251106082607 441650977434039376659123911)
        ·
          refine ⟨662476466151059064988685867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 441650977434039376659123911 662476466151059064988685867)
          ·
            refine ⟨993714699226588597483028801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 662476466151059064988685867 993714699226588597483028801)
            ·
              refine ⟨745286024419941448112271601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 993714699226588597483028801 745286024419941448112271601)
              ·
                refine ⟨558964518314956086084203701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 745286024419941448112271601 558964518314956086084203701)
                ·
                  refine ⟨52402923592027133070394097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 558964518314956086084203701 52402923592027133070394097)
                  ·
                    refine ⟨39302192694020349802795573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52402923592027133070394097 39302192694020349802795573)
                    ·
                      refine ⟨3684580565064407794012085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39302192694020349802795573 3684580565064407794012085)
                      ·
                        rfl

theorem cell23_7175695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 5, 2, 5].length) (baseStart_7175695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7175695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7175695 prefixEnd_7175695 := by exact prefixLift 7175695
  have htrace : WordTrace (prefixWord ++ tailWord_7175695) baseStart_7175695 baseEnd_7175695 := by
    simpa [prefixWord, tailWord_7175695, baseEnd_7175695] using wordTrace_append hprefix tailTrace_7175695
  have hstable : (prefixWord ++ tailWord_7175695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7175695).length < 2 ^ (prefixWord ++ tailWord_7175695).sum := by decide
  have hdescent : baseEnd_7175695 < baseStart_7175695 := by decide
  rcases family_descends (prefixWord ++ tailWord_7175695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7175709 : List Nat := [1, 4, 2, 2, 1, 1, 1, 2, 2, 5, 2]
def baseStart_7175709 : Nat := 118140960795 + 7175709 * 2 ^ 59
def prefixEnd_7175709 : Nat := 4983230072969 + 3 ^ 40 * 7175709 * 2
def baseEnd_7175709 : Nat := 3684587753793570739237021

theorem tailTrace_7175709 : CollatzResearch.WordTrace tailWord_7175709 prefixEnd_7175709 3684587753793570739237021 := by
  unfold tailWord_7175709
  simp only [CollatzResearch.WordTrace]
  refine ⟨261719608360639281374194181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174479738907092854249462787 261719608360639281374194181)
  ·
    refine ⟨49072426567619865257661409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 261719608360639281374194181 49072426567619865257661409)
    ·
      refine ⟨36804319925714898943246057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49072426567619865257661409 36804319925714898943246057)
      ·
        refine ⟨27603239944286174207434543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36804319925714898943246057 27603239944286174207434543)
        ·
          refine ⟨41404859916429261311151815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27603239944286174207434543 41404859916429261311151815)
          ·
            refine ⟨62107289874643891966727723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41404859916429261311151815 62107289874643891966727723)
            ·
              refine ⟨93160934811965837950091585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62107289874643891966727723 93160934811965837950091585)
              ·
                refine ⟨69870701108974378462568689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93160934811965837950091585 69870701108974378462568689)
                ·
                  refine ⟨52403025831730783846926517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69870701108974378462568689 52403025831730783846926517)
                  ·
                    refine ⟨4912783671724760985649361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52403025831730783846926517 4912783671724760985649361)
                    ·
                      refine ⟨3684587753793570739237021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4912783671724760985649361 3684587753793570739237021)
                      ·
                        rfl

theorem cell23_7175709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 2, 5, 2].length) (baseStart_7175709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7175709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7175709 prefixEnd_7175709 := by exact prefixLift 7175709
  have htrace : WordTrace (prefixWord ++ tailWord_7175709) baseStart_7175709 baseEnd_7175709 := by
    simpa [prefixWord, tailWord_7175709, baseEnd_7175709] using wordTrace_append hprefix tailTrace_7175709
  have hstable : (prefixWord ++ tailWord_7175709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7175709).length < 2 ^ (prefixWord ++ tailWord_7175709).sum := by decide
  have hdescent : baseEnd_7175709 < baseStart_7175709 := by decide
  rcases family_descends (prefixWord ++ tailWord_7175709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7175749 : List Nat := [1, 3, 1, 1, 1, 4, 4, 1, 3, 4]
def baseStart_7175749 : Nat := 118140960795 + 7175749 * 2 ^ 59
def prefixEnd_7175749 : Nat := 4983230072969 + 3 ^ 40 * 7175749 * 2
def baseEnd_7175749 : Nat := 1228202764339916860912279

theorem tailTrace_7175749 : CollatzResearch.WordTrace tailWord_7175749 prefixEnd_7175749 1228202764339916860912279 := by
  unfold tailWord_7175749
  simp only [CollatzResearch.WordTrace]
  refine ⟨261721067280494368205650301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174480711520329578803766867 261721067280494368205650301)
  ·
    refine ⟨98145400230185388077118863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261721067280494368205650301 98145400230185388077118863)
    ·
      refine ⟨147218100345278082115678295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98145400230185388077118863 147218100345278082115678295)
      ·
        refine ⟨220827150517917123173517443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147218100345278082115678295 220827150517917123173517443)
        ·
          refine ⟨331240725776875684760276165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220827150517917123173517443 331240725776875684760276165)
          ·
            refine ⟨62107636083164190892551781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 331240725776875684760276165 62107636083164190892551781)
            ·
              refine ⟨11645181765593285792353459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62107636083164190892551781 11645181765593285792353459)
              ·
                refine ⟨17467772648389928688530189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11645181765593285792353459 17467772648389928688530189)
                ·
                  refine ⟨6550414743146223258198821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17467772648389928688530189 6550414743146223258198821)
                  ·
                    refine ⟨1228202764339916860912279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6550414743146223258198821 1228202764339916860912279)
                    ·
                      rfl

theorem cell23_7175749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 1, 3, 4].length) (baseStart_7175749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7175749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7175749 prefixEnd_7175749 := by exact prefixLift 7175749
  have htrace : WordTrace (prefixWord ++ tailWord_7175749) baseStart_7175749 baseEnd_7175749 := by
    simpa [prefixWord, tailWord_7175749, baseEnd_7175749] using wordTrace_append hprefix tailTrace_7175749
  have hstable : (prefixWord ++ tailWord_7175749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7175749).length < 2 ^ (prefixWord ++ tailWord_7175749).sum := by decide
  have hdescent : baseEnd_7175749 < baseStart_7175749 := by decide
  rcases family_descends (prefixWord ++ tailWord_7175749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7175826 : List Nat := [3, 2, 3, 1, 3, 1, 1, 1, 3, 5]
def baseStart_7175826 : Nat := 118140960795 + 7175826 * 2 ^ 59
def prefixEnd_7175826 : Nat := 4983230072969 + 3 ^ 40 * 7175826 * 2
def baseEnd_7175826 : Nat := 1228215943676715593824661

theorem tailTrace_7175826 : CollatzResearch.WordTrace tailWord_7175826 prefixEnd_7175826 1228215943676715593824661 := by
  unfold tailWord_7175826
  simp only [CollatzResearch.WordTrace]
  refine ⟨65430968925303852589050833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174482583800810273570802221 65430968925303852589050833)
  ·
    refine ⟨49073226693977889441788125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65430968925303852589050833 49073226693977889441788125)
    ·
      refine ⟨18402460010241708540670547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49073226693977889441788125 18402460010241708540670547)
      ·
        refine ⟨27603690015362562811005821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18402460010241708540670547 27603690015362562811005821)
        ·
          refine ⟨10351383755760961054127183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27603690015362562811005821 10351383755760961054127183)
          ·
            refine ⟨15527075633641441581190775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10351383755760961054127183 15527075633641441581190775)
            ·
              refine ⟨23290613450462162371786163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15527075633641441581190775 23290613450462162371786163)
              ·
                refine ⟨34935920175693243557679245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23290613450462162371786163 34935920175693243557679245)
                ·
                  refine ⟨13100970065884966334129717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34935920175693243557679245 13100970065884966334129717)
                  ·
                    refine ⟨1228215943676715593824661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13100970065884966334129717 1228215943676715593824661)
                    ·
                      rfl

theorem cell23_7175826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_7175826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7175826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7175826 prefixEnd_7175826 := by exact prefixLift 7175826
  have htrace : WordTrace (prefixWord ++ tailWord_7175826) baseStart_7175826 baseEnd_7175826 := by
    simpa [prefixWord, tailWord_7175826, baseEnd_7175826] using wordTrace_append hprefix tailTrace_7175826
  have hstable : (prefixWord ++ tailWord_7175826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7175826).length < 2 ^ (prefixWord ++ tailWord_7175826).sum := by decide
  have hdescent : baseEnd_7175826 < baseStart_7175826 := by decide
  rcases family_descends (prefixWord ++ tailWord_7175826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7175829 : List Nat := [1, 3, 2, 1, 1, 1, 1, 3, 2, 6, 2]
def baseStart_7175829 : Nat := 118140960795 + 7175829 * 2 ^ 59
def prefixEnd_7175829 : Nat := 4983230072969 + 3 ^ 40 * 7175829 * 2
def baseEnd_7175829 : Nat := 3684649371472110269736469

theorem tailTrace_7175829 : CollatzResearch.WordTrace tailWord_7175829 prefixEnd_7175829 3684649371472110269736469 := by
  unfold tailWord_7175829
  simp only [CollatzResearch.WordTrace]
  refine ⟨261723985120204541868562541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174482656746803027912375027 261723985120204541868562541)
  ·
    refine ⟨98146494420076703200710953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261723985120204541868562541 98146494420076703200710953)
    ·
      refine ⟨73609870815057527400533215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98146494420076703200710953 73609870815057527400533215)
      ·
        refine ⟨110414806222586291100799823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73609870815057527400533215 110414806222586291100799823)
        ·
          refine ⟨165622209333879436651199735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110414806222586291100799823 165622209333879436651199735)
          ·
            refine ⟨248433314000819154976799603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165622209333879436651199735 248433314000819154976799603)
            ·
              refine ⟨372649971001228732465199405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248433314000819154976799603 372649971001228732465199405)
              ·
                refine ⟨139743739125460774674449777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 372649971001228732465199405 139743739125460774674449777)
                ·
                  refine ⟨104807804344095581005837333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139743739125460774674449777 104807804344095581005837333)
                  ·
                    refine ⟨4912865828629480359648625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 104807804344095581005837333 4912865828629480359648625)
                    ·
                      refine ⟨3684649371472110269736469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4912865828629480359648625 3684649371472110269736469)
                      ·
                        rfl

theorem cell23_7175829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 6, 2].length) (baseStart_7175829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7175829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7175829 prefixEnd_7175829 := by exact prefixLift 7175829
  have htrace : WordTrace (prefixWord ++ tailWord_7175829) baseStart_7175829 baseEnd_7175829 := by
    simpa [prefixWord, tailWord_7175829, baseEnd_7175829] using wordTrace_append hprefix tailTrace_7175829
  have hstable : (prefixWord ++ tailWord_7175829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7175829).length < 2 ^ (prefixWord ++ tailWord_7175829).sum := by decide
  have hdescent : baseEnd_7175829 < baseStart_7175829 := by decide
  rcases family_descends (prefixWord ++ tailWord_7175829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7175876 : List Nat := [2, 3, 3, 1, 1, 1, 4, 1, 1, 2, 4]
def baseStart_7175876 : Nat := 118140960795 + 7175876 * 2 ^ 59
def prefixEnd_7175876 : Nat := 4983230072969 + 3 ^ 40 * 7175876 * 2
def baseEnd_7175876 : Nat := 3684673505062871585848753

theorem tailTrace_7175876 : CollatzResearch.WordTrace tailWord_7175876 prefixEnd_7175876 3684673505062871585848753 := by
  unfold tailWord_7175876
  simp only [CollatzResearch.WordTrace]
  refine ⟨130862849675517134447761741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174483799567356179263682321 130862849675517134447761741)
  ·
    refine ⟨49073568628318925417910653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130862849675517134447761741 49073568628318925417910653)
    ·
      refine ⟨18402588235619597031716495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49073568628318925417910653 18402588235619597031716495)
      ·
        refine ⟨27603882353429395547574743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18402588235619597031716495 27603882353429395547574743)
        ·
          refine ⟨41405823530144093321362115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27603882353429395547574743 41405823530144093321362115)
          ·
            refine ⟨62108735295216139982043173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41405823530144093321362115 62108735295216139982043173)
            ·
              refine ⟨11645387867853026246633095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62108735295216139982043173 11645387867853026246633095)
              ·
                refine ⟨17468081801779539369949643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11645387867853026246633095 17468081801779539369949643)
                ·
                  refine ⟨26202122702669309054924465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17468081801779539369949643 26202122702669309054924465)
                  ·
                    refine ⟨19651592027001981791193349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26202122702669309054924465 19651592027001981791193349)
                    ·
                      refine ⟨3684673505062871585848753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19651592027001981791193349 3684673505062871585848753)
                      ·
                        rfl

theorem cell23_7175876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_7175876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7175876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7175876 prefixEnd_7175876 := by exact prefixLift 7175876
  have htrace : WordTrace (prefixWord ++ tailWord_7175876) baseStart_7175876 baseEnd_7175876 := by
    simpa [prefixWord, tailWord_7175876, baseEnd_7175876] using wordTrace_append hprefix tailTrace_7175876
  have hstable : (prefixWord ++ tailWord_7175876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7175876).length < 2 ^ (prefixWord ++ tailWord_7175876).sum := by decide
  have hdescent : baseEnd_7175876 < baseStart_7175876 := by decide
  rcases family_descends (prefixWord ++ tailWord_7175876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7175894 : List Nat := [5, 2, 1, 3, 2, 1, 2, 1, 1, 5]
def baseStart_7175894 : Nat := 118140960795 + 7175894 * 2 ^ 59
def prefixEnd_7175894 : Nat := 4983230072969 + 3 ^ 40 * 7175894 * 2
def baseEnd_7175894 : Nat := 1228227582571550838474557

theorem tailTrace_7175894 : CollatzResearch.WordTrace tailWord_7175894 prefixEnd_7175894 1228227582571550838474557 := by
  unfold tailWord_7175894
  simp only [CollatzResearch.WordTrace]
  refine ⟨16357897241560566123104921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 174484237243312705313119157 16357897241560566123104921)
  ·
    refine ⟨12268422931170424592328691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16357897241560566123104921 12268422931170424592328691)
    ·
      refine ⟨18402634396755636888493037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12268422931170424592328691 18402634396755636888493037)
      ·
        refine ⟨6900987898783363833184889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18402634396755636888493037 6900987898783363833184889)
        ·
          refine ⟨5175740924087522874888667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6900987898783363833184889 5175740924087522874888667)
          ·
            refine ⟨7763611386131284312333001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5175740924087522874888667 7763611386131284312333001)
            ·
              refine ⟨5822708539598463234249751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7763611386131284312333001 5822708539598463234249751)
              ·
                refine ⟨8734062809397694851374627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5822708539598463234249751 8734062809397694851374627)
                ·
                  refine ⟨13101094214096542277061941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8734062809397694851374627 13101094214096542277061941)
                  ·
                    refine ⟨1228227582571550838474557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13101094214096542277061941 1228227582571550838474557)
                    ·
                      rfl

theorem cell23_7175894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_7175894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7175894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7175894 prefixEnd_7175894 := by exact prefixLift 7175894
  have htrace : WordTrace (prefixWord ++ tailWord_7175894) baseStart_7175894 baseEnd_7175894 := by
    simpa [prefixWord, tailWord_7175894, baseEnd_7175894] using wordTrace_append hprefix tailTrace_7175894
  have hstable : (prefixWord ++ tailWord_7175894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7175894).length < 2 ^ (prefixWord ++ tailWord_7175894).sum := by decide
  have hdescent : baseEnd_7175894 < baseStart_7175894 := by decide
  rcases family_descends (prefixWord ++ tailWord_7175894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7175896 : List Nat := [2, 1, 2, 2, 3, 1, 2, 2, 4, 1, 3]
def baseStart_7175896 : Nat := 118140960795 + 7175896 * 2 ^ 59
def prefixEnd_7175896 : Nat := 4983230072969 + 3 ^ 40 * 7175896 * 2
def baseEnd_7175896 : Nat := 3684683774675961507598661

theorem tailTrace_7175896 : CollatzResearch.WordTrace tailWord_7175896 prefixEnd_7175896 3684683774675961507598661 := by
  unfold tailWord_7175896
  simp only [CollatzResearch.WordTrace]
  refine ⟨130863214405480906155625771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174484285873974541540834361 130863214405480906155625771)
  ·
    refine ⟨196294821608221359233438657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130863214405480906155625771 196294821608221359233438657)
    ·
      refine ⟨147221116206166019425078993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196294821608221359233438657 147221116206166019425078993)
      ·
        refine ⟨110415837154624514568809245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147221116206166019425078993 110415837154624514568809245)
        ·
          refine ⟨41405938932984192963303467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110415837154624514568809245 41405938932984192963303467)
          ·
            refine ⟨62108908399476289444955201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41405938932984192963303467 62108908399476289444955201)
            ·
              refine ⟨46581681299607217083716401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62108908399476289444955201 46581681299607217083716401)
              ·
                refine ⟨34936260974705412812787301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46581681299607217083716401 34936260974705412812787301)
                ·
                  refine ⟨6550548932757264902397619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34936260974705412812787301 6550548932757264902397619)
                  ·
                    refine ⟨9825823399135897353596429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6550548932757264902397619 9825823399135897353596429)
                    ·
                      refine ⟨3684683774675961507598661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9825823399135897353596429 3684683774675961507598661)
                      ·
                        rfl

theorem cell23_7175896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 4, 1, 3].length) (baseStart_7175896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7175896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7175896 prefixEnd_7175896 := by exact prefixLift 7175896
  have htrace : WordTrace (prefixWord ++ tailWord_7175896) baseStart_7175896 baseEnd_7175896 := by
    simpa [prefixWord, tailWord_7175896, baseEnd_7175896] using wordTrace_append hprefix tailTrace_7175896
  have hstable : (prefixWord ++ tailWord_7175896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7175896).length < 2 ^ (prefixWord ++ tailWord_7175896).sum := by decide
  have hdescent : baseEnd_7175896 < baseStart_7175896 := by decide
  rcases family_descends (prefixWord ++ tailWord_7175896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7175900 : List Nat := [2, 2, 5, 1, 2, 1, 1, 3, 1, 2, 3]
def baseStart_7175900 : Nat := 118140960795 + 7175900 * 2 ^ 59
def prefixEnd_7175900 : Nat := 4983230072969 + 3 ^ 40 * 7175900 * 2
def baseEnd_7175900 : Nat := 3684685828598579491948643

theorem tailTrace_7175900 : CollatzResearch.WordTrace tailWord_7175900 prefixEnd_7175900 3684685828598579491948643 := by
  unfold tailWord_7175900
  simp only [CollatzResearch.WordTrace]
  refine ⟨130863287351473660497198577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174484383135298213996264769 130863287351473660497198577)
  ·
    refine ⟨98147465513605245372898933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130863287351473660497198577 98147465513605245372898933)
    ·
      refine ⟨9201324891900491753709275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 98147465513605245372898933 9201324891900491753709275)
      ·
        refine ⟨13801987337850737630563913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9201324891900491753709275 13801987337850737630563913)
        ·
          refine ⟨10351490503388053222922935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13801987337850737630563913 10351490503388053222922935)
          ·
            refine ⟨15527235755082079834384403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10351490503388053222922935 15527235755082079834384403)
            ·
              refine ⟨23290853632623119751576605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15527235755082079834384403 23290853632623119751576605)
              ·
                refine ⟨8734070112233669906841227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23290853632623119751576605 8734070112233669906841227)
                ·
                  refine ⟨13101105168350504860261841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8734070112233669906841227 13101105168350504860261841)
                  ·
                    refine ⟨9825828876262878645196381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13101105168350504860261841 9825828876262878645196381)
                    ·
                      refine ⟨3684685828598579491948643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9825828876262878645196381 3684685828598579491948643)
                      ·
                        rfl

theorem cell23_7175900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_7175900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7175900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7175900 prefixEnd_7175900 := by exact prefixLift 7175900
  have htrace : WordTrace (prefixWord ++ tailWord_7175900) baseStart_7175900 baseEnd_7175900 := by
    simpa [prefixWord, tailWord_7175900, baseEnd_7175900] using wordTrace_append hprefix tailTrace_7175900
  have hstable : (prefixWord ++ tailWord_7175900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7175900).length < 2 ^ (prefixWord ++ tailWord_7175900).sum := by decide
  have hdescent : baseEnd_7175900 < baseStart_7175900 := by decide
  rcases family_descends (prefixWord ++ tailWord_7175900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7175939 : List Nat := [1, 1, 1, 3, 2, 2, 2, 2, 2, 4, 3]
def baseStart_7175939 : Nat := 118140960795 + 7175939 * 2 ^ 59
def prefixEnd_7175939 : Nat := 4983230072969 + 3 ^ 40 * 7175939 * 2
def baseEnd_7175939 : Nat := 3684705854344104839360963

theorem tailTrace_7175939 : CollatzResearch.WordTrace tailWord_7175939 prefixEnd_7175939 3684705854344104839360963 := by
  unfold tailWord_7175939
  simp only [CollatzResearch.WordTrace]
  refine ⟨261727997149806030655066871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174485331433204020436711247 261727997149806030655066871)
  ·
    refine ⟨392591995724709045982600307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261727997149806030655066871 392591995724709045982600307)
    ·
      refine ⟨588887993587063568973900461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392591995724709045982600307 588887993587063568973900461)
      ·
        refine ⟨220832997595148838365212673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 588887993587063568973900461 220832997595148838365212673)
        ·
          refine ⟨165624748196361628773909505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220832997595148838365212673 165624748196361628773909505)
          ·
            refine ⟨124218561147271221580432129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165624748196361628773909505 124218561147271221580432129)
            ·
              refine ⟨93163920860453416185324097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124218561147271221580432129 93163920860453416185324097)
              ·
                refine ⟨69872940645340062138993073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93163920860453416185324097 69872940645340062138993073)
                ·
                  refine ⟨52404705484005046604244805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69872940645340062138993073 52404705484005046604244805)
                  ·
                    refine ⟨9825882278250946238295901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52404705484005046604244805 9825882278250946238295901)
                    ·
                      refine ⟨3684705854344104839360963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9825882278250946238295901 3684705854344104839360963)
                      ·
                        rfl

theorem cell23_7175939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 2, 4, 3].length) (baseStart_7175939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7175939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7175939 prefixEnd_7175939 := by exact prefixLift 7175939
  have htrace : WordTrace (prefixWord ++ tailWord_7175939) baseStart_7175939 baseEnd_7175939 := by
    simpa [prefixWord, tailWord_7175939, baseEnd_7175939] using wordTrace_append hprefix tailTrace_7175939
  have hstable : (prefixWord ++ tailWord_7175939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7175939).length < 2 ^ (prefixWord ++ tailWord_7175939).sum := by decide
  have hdescent : baseEnd_7175939 < baseStart_7175939 := by decide
  rcases family_descends (prefixWord ++ tailWord_7175939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7175940 : List Nat := [2, 3, 2, 2, 1, 3, 2, 2, 1, 3, 2]
def baseStart_7175940 : Nat := 118140960795 + 7175940 * 2 ^ 59
def prefixEnd_7175940 : Nat := 4983230072969 + 3 ^ 40 * 7175940 * 2
def baseEnd_7175940 : Nat := 3684706367824759335448459

theorem tailTrace_7175940 : CollatzResearch.WordTrace tailWord_7175940 prefixEnd_7175940 3684706367824759335448459 := by
  unfold tailWord_7175940
  simp only [CollatzResearch.WordTrace]
  refine ⟨130864016811401203912926637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174485355748534938550568849 130864016811401203912926637)
  ·
    refine ⟨49074006304275451467347489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130864016811401203912926637 49074006304275451467347489)
    ·
      refine ⟨36805504728206588600510617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49074006304275451467347489 36805504728206588600510617)
      ·
        refine ⟨27604128546154941450382963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36805504728206588600510617 27604128546154941450382963)
        ·
          refine ⟨41406192819232412175574445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27604128546154941450382963 41406192819232412175574445)
          ·
            refine ⟨15527322307212154565840417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41406192819232412175574445 15527322307212154565840417)
            ·
              refine ⟨11645491730409115924380313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15527322307212154565840417 11645491730409115924380313)
              ·
                refine ⟨8734118797806836943285235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11645491730409115924380313 8734118797806836943285235)
                ·
                  refine ⟨13101178196710255414927853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8734118797806836943285235 13101178196710255414927853)
                  ·
                    refine ⟨4912941823766345780597945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13101178196710255414927853 4912941823766345780597945)
                    ·
                      refine ⟨3684706367824759335448459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4912941823766345780597945 3684706367824759335448459)
                      ·
                        rfl

theorem cell23_7175940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 2, 1, 3, 2].length) (baseStart_7175940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7175940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7175940 prefixEnd_7175940 := by exact prefixLift 7175940
  have htrace : WordTrace (prefixWord ++ tailWord_7175940) baseStart_7175940 baseEnd_7175940 := by
    simpa [prefixWord, tailWord_7175940, baseEnd_7175940] using wordTrace_append hprefix tailTrace_7175940
  have hstable : (prefixWord ++ tailWord_7175940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7175940).length < 2 ^ (prefixWord ++ tailWord_7175940).sum := by decide
  have hdescent : baseEnd_7175940 < baseStart_7175940 := by decide
  rcases family_descends (prefixWord ++ tailWord_7175940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7175970 : List Nat := [3, 3, 1, 1, 2, 1, 2, 4, 2, 2, 2]
def baseStart_7175970 : Nat := 118140960795 + 7175970 * 2 ^ 59
def prefixEnd_7175970 : Nat := 4983230072969 + 3 ^ 40 * 7175970 * 2
def baseEnd_7175970 : Nat := 3684721772244394218073321

theorem tailTrace_7175970 : CollatzResearch.WordTrace tailWord_7175970 prefixEnd_7175970 3684721772244394218073321 := by
  unfold tailWord_7175970
  simp only [CollatzResearch.WordTrace]
  refine ⟨65432281953173430737361341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174486085208462481966296909 65432281953173430737361341)
  ·
    refine ⟨24537105732440036526510503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65432281953173430737361341 24537105732440036526510503)
    ·
      refine ⟨36805658598660054789765755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24537105732440036526510503 36805658598660054789765755)
      ·
        refine ⟨55208487897990082184648633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36805658598660054789765755 55208487897990082184648633)
        ·
          refine ⟨41406365923492561638486475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55208487897990082184648633 41406365923492561638486475)
          ·
            refine ⟨62109548885238842457729713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41406365923492561638486475 62109548885238842457729713)
            ·
              refine ⟨46582161663929131843297285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62109548885238842457729713 46582161663929131843297285)
              ·
                refine ⟨8734155311986712220618241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46582161663929131843297285 8734155311986712220618241)
                ·
                  refine ⟨6550616483990034165463681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8734155311986712220618241 6550616483990034165463681)
                  ·
                    refine ⟨4912962362992525624097761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6550616483990034165463681 4912962362992525624097761)
                    ·
                      refine ⟨3684721772244394218073321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4912962362992525624097761 3684721772244394218073321)
                      ·
                        rfl

theorem cell23_7175970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 4, 2, 2, 2].length) (baseStart_7175970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7175970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7175970 prefixEnd_7175970 := by exact prefixLift 7175970
  have htrace : WordTrace (prefixWord ++ tailWord_7175970) baseStart_7175970 baseEnd_7175970 := by
    simpa [prefixWord, tailWord_7175970, baseEnd_7175970] using wordTrace_append hprefix tailTrace_7175970
  have hstable : (prefixWord ++ tailWord_7175970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7175970).length < 2 ^ (prefixWord ++ tailWord_7175970).sum := by decide
  have hdescent : baseEnd_7175970 < baseStart_7175970 := by decide
  rcases family_descends (prefixWord ++ tailWord_7175970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7175976 : List Nat := [2, 1, 5, 1, 1, 2, 3, 1, 7]
def baseStart_7175976 : Nat := 118140960795 + 7175976 * 2 ^ 59
def prefixEnd_7175976 : Nat := 4983230072969 + 3 ^ 40 * 7175976 * 2
def baseEnd_7175976 : Nat := 409413872569813466066477

theorem tailTrace_7175976 : CollatzResearch.WordTrace tailWord_7175976 prefixEnd_7175976 409413872569813466066477 := by
  unfold tailWord_7175976
  simp only [CollatzResearch.WordTrace]
  refine ⟨130864673325335992987081891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174486231100447990649442521 130864673325335992987081891)
  ·
    refine ⟨196297009988003989480622837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130864673325335992987081891 196297009988003989480622837)
    ·
      refine ⟨18402844686375374013808391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 196297009988003989480622837 18402844686375374013808391)
      ·
        refine ⟨27604267029563061020712587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18402844686375374013808391 27604267029563061020712587)
        ·
          refine ⟨41406400544344591531068881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27604267029563061020712587 41406400544344591531068881)
          ·
            refine ⟨31054800408258443648301661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41406400544344591531068881 31054800408258443648301661)
            ·
              refine ⟨11645550153096916368113123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31054800408258443648301661 11645550153096916368113123)
              ·
                refine ⟨17468325229645374552169685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11645550153096916368113123 17468325229645374552169685)
                ·
                  refine ⟨409413872569813466066477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17468325229645374552169685 409413872569813466066477)
                  ·
                    rfl

theorem cell23_7175976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 1, 7].length) (baseStart_7175976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7175976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7175976 prefixEnd_7175976 := by exact prefixLift 7175976
  have htrace : WordTrace (prefixWord ++ tailWord_7175976) baseStart_7175976 baseEnd_7175976 := by
    simpa [prefixWord, tailWord_7175976, baseEnd_7175976] using wordTrace_append hprefix tailTrace_7175976
  have hstable : (prefixWord ++ tailWord_7175976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7175976).length < 2 ^ (prefixWord ++ tailWord_7175976).sum := by decide
  have hdescent : baseEnd_7175976 < baseStart_7175976 := by decide
  rcases family_descends (prefixWord ++ tailWord_7175976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7176026 : List Nat := [3, 1, 1, 2, 1, 3, 1, 4, 2, 1, 4]
def baseStart_7176026 : Nat := 118140960795 + 7176026 * 2 ^ 59
def prefixEnd_7176026 : Nat := 4983230072969 + 3 ^ 40 * 7176026 * 2
def baseEnd_7176026 : Nat := 3684750527161045998973063

theorem tailTrace_7176026 : CollatzResearch.WordTrace tailWord_7176026 prefixEnd_7176026 3684750527161045998973063 := by
  unfold tailWord_7176026
  simp only [CollatzResearch.WordTrace]
  refine ⟨65432792575122711128370983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174487446866993896342322621 65432792575122711128370983)
  ·
    refine ⟨98149188862684066692556475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65432792575122711128370983 98149188862684066692556475)
    ·
      refine ⟨147223783294026100038834713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98149188862684066692556475 147223783294026100038834713)
      ·
        refine ⟨110417837470519575029126035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147223783294026100038834713 110417837470519575029126035)
        ·
          refine ⟨165626756205779362543689053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110417837470519575029126035 165626756205779362543689053)
          ·
            refine ⟨62110033577167260953883395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165626756205779362543689053 62110033577167260953883395)
            ·
              refine ⟨93165050365750891430825093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62110033577167260953883395 93165050365750891430825093)
              ·
                refine ⟨17468446943578292143279705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93165050365750891430825093 17468446943578292143279705)
                ·
                  refine ⟨13101335207683719107459779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17468446943578292143279705 13101335207683719107459779)
                  ·
                    refine ⟨19652002811525578661189669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13101335207683719107459779 19652002811525578661189669)
                    ·
                      refine ⟨3684750527161045998973063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19652002811525578661189669 3684750527161045998973063)
                      ·
                        rfl

theorem cell23_7176026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 4, 2, 1, 4].length) (baseStart_7176026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7176026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7176026 prefixEnd_7176026 := by exact prefixLift 7176026
  have htrace : WordTrace (prefixWord ++ tailWord_7176026) baseStart_7176026 baseEnd_7176026 := by
    simpa [prefixWord, tailWord_7176026, baseEnd_7176026] using wordTrace_append hprefix tailTrace_7176026
  have hstable : (prefixWord ++ tailWord_7176026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7176026).length < 2 ^ (prefixWord ++ tailWord_7176026).sum := by decide
  have hdescent : baseEnd_7176026 < baseStart_7176026 := by decide
  rcases family_descends (prefixWord ++ tailWord_7176026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7176053 : List Nat := [1, 3, 4, 1, 1, 1, 3, 2, 3, 4]
def baseStart_7176053 : Nat := 118140960795 + 7176053 * 2 ^ 59
def prefixEnd_7176053 : Nat := 4983230072969 + 3 ^ 40 * 7176053 * 2
def baseEnd_7176053 : Nat := 1228254797046239131111813

theorem tailTrace_7176053 : CollatzResearch.WordTrace tailWord_7176053 prefixEnd_7176053 1228254797046239131111813 := by
  unfold tailWord_7176053
  simp only [CollatzResearch.WordTrace]
  refine ⟨261732155071393028124716813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174488103380928685416477875 261732155071393028124716813)
  ·
    refine ⟨98149558151772385546768805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261732155071393028124716813 98149558151772385546768805)
    ·
      refine ⟨18403042153457322290019151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98149558151772385546768805 18403042153457322290019151)
      ·
        refine ⟨27604563230185983435028727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18403042153457322290019151 27604563230185983435028727)
        ·
          refine ⟨41406844845278975152543091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27604563230185983435028727 41406844845278975152543091)
          ·
            refine ⟨62110267267918462728814637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41406844845278975152543091 62110267267918462728814637)
            ·
              refine ⟨23291350225469423523305489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62110267267918462728814637 23291350225469423523305489)
              ·
                refine ⟨17468512669102067642479117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23291350225469423523305489 17468512669102067642479117)
                ·
                  refine ⟨6550692250913275365929669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17468512669102067642479117 6550692250913275365929669)
                  ·
                    refine ⟨1228254797046239131111813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6550692250913275365929669 1228254797046239131111813)
                    ·
                      rfl

theorem cell23_7176053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_7176053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7176053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7176053 prefixEnd_7176053 := by exact prefixLift 7176053
  have htrace : WordTrace (prefixWord ++ tailWord_7176053) baseStart_7176053 baseEnd_7176053 := by
    simpa [prefixWord, tailWord_7176053, baseEnd_7176053] using wordTrace_append hprefix tailTrace_7176053
  have hstable : (prefixWord ++ tailWord_7176053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7176053).length < 2 ^ (prefixWord ++ tailWord_7176053).sum := by decide
  have hdescent : baseEnd_7176053 < baseStart_7176053 := by decide
  rcases family_descends (prefixWord ++ tailWord_7176053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7176113 : List Nat := [1, 2, 2, 4, 2, 1, 1, 4, 1, 5]
def baseStart_7176113 : Nat := 118140960795 + 7176113 * 2 ^ 59
def prefixEnd_7176113 : Nat := 4983230072969 + 3 ^ 40 * 7176113 * 2
def baseEnd_7176113 : Nat := 1228265066659329052861721

theorem tailTrace_7176113 : CollatzResearch.WordTrace tailWord_7176113 prefixEnd_7176113 1228265066659329052861721 := by
  unfold tailWord_7176113
  simp only [CollatzResearch.WordTrace]
  refine ⟨261734343451175658371900993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174489562300783772247933995 261734343451175658371900993)
  ·
    refine ⟨196300757588381743778925745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261734343451175658371900993 196300757588381743778925745)
    ·
      refine ⟨147225568191286307834194309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196300757588381743778925745 147225568191286307834194309)
      ·
        refine ⟨27604794035866182718911433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 147225568191286307834194309 27604794035866182718911433)
        ·
          refine ⟨20703595526899637039183575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27604794035866182718911433 20703595526899637039183575)
          ·
            refine ⟨31055393290349455558775363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20703595526899637039183575 31055393290349455558775363)
            ·
              refine ⟨46583089935524183338163045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31055393290349455558775363 46583089935524183338163045)
              ·
                refine ⟨8734329362910784375905571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46583089935524183338163045 8734329362910784375905571)
                ·
                  refine ⟨13101494044366176563858357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8734329362910784375905571 13101494044366176563858357)
                  ·
                    refine ⟨1228265066659329052861721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13101494044366176563858357 1228265066659329052861721)
                    ·
                      rfl

theorem cell23_7176113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 4, 1, 5].length) (baseStart_7176113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7176113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7176113 prefixEnd_7176113 := by exact prefixLift 7176113
  have htrace : WordTrace (prefixWord ++ tailWord_7176113) baseStart_7176113 baseEnd_7176113 := by
    simpa [prefixWord, tailWord_7176113, baseEnd_7176113] using wordTrace_append hprefix tailTrace_7176113
  have hstable : (prefixWord ++ tailWord_7176113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7176113).length < 2 ^ (prefixWord ++ tailWord_7176113).sum := by decide
  have hdescent : baseEnd_7176113 < baseStart_7176113 := by decide
  rcases family_descends (prefixWord ++ tailWord_7176113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7176143 : List Nat := [1, 1, 2, 1, 1, 5, 2, 4, 2, 4]
def baseStart_7176143 : Nat := 118140960795 + 7176143 * 2 ^ 59
def prefixEnd_7176143 : Nat := 4983230072969 + 3 ^ 40 * 7176143 * 2
def baseEnd_7176143 : Nat := 1228270201465874013736675

theorem tailTrace_7176143 : CollatzResearch.WordTrace tailWord_7176143 prefixEnd_7176143 1228270201465874013736675 := by
  unfold tailWord_7176143
  simp only [CollatzResearch.WordTrace]
  refine ⟨261735437641066973495493083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174490291760711315663662055 261735437641066973495493083)
  ·
    refine ⟨392603156461600460243239625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261735437641066973495493083 392603156461600460243239625)
    ·
      refine ⟨294452367346200345182429719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 392603156461600460243239625 294452367346200345182429719)
      ·
        refine ⟨441678551019300517773644579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294452367346200345182429719 441678551019300517773644579)
        ·
          refine ⟨662517826528950776660466869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 441678551019300517773644579 662517826528950776660466869)
          ·
            refine ⟨62111046237089135311918769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 662517826528950776660466869 62111046237089135311918769)
            ·
              refine ⟨46583284677816851483939077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62111046237089135311918769 46583284677816851483939077)
              ·
                refine ⟨8734365877090659653238577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46583284677816851483939077 8734365877090659653238577)
                ·
                  refine ⟨6550774407817994739928933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8734365877090659653238577 6550774407817994739928933)
                  ·
                    refine ⟨1228270201465874013736675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6550774407817994739928933 1228270201465874013736675)
                    ·
                      rfl

theorem cell23_7176143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 4, 2, 4].length) (baseStart_7176143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7176143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7176143 prefixEnd_7176143 := by exact prefixLift 7176143
  have htrace : WordTrace (prefixWord ++ tailWord_7176143) baseStart_7176143 baseEnd_7176143 := by
    simpa [prefixWord, tailWord_7176143, baseEnd_7176143] using wordTrace_append hprefix tailTrace_7176143
  have hstable : (prefixWord ++ tailWord_7176143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7176143).length < 2 ^ (prefixWord ++ tailWord_7176143).sum := by decide
  have hdescent : baseEnd_7176143 < baseStart_7176143 := by decide
  rcases family_descends (prefixWord ++ tailWord_7176143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7176167 : List Nat := [1, 1, 5, 2, 3, 2, 1, 2, 1, 1, 4]
def baseStart_7176167 : Nat := 118140960795 + 7176167 * 2 ^ 59
def prefixEnd_7176167 : Nat := 4983230072969 + 3 ^ 40 * 7176167 * 2
def baseEnd_7176167 : Nat := 3684822927933329947309915

theorem tailTrace_7176167 : CollatzResearch.WordTrace tailWord_7176167 prefixEnd_7176167 3684822927933329947309915 := by
  unfold tailWord_7176167
  simp only [CollatzResearch.WordTrace]
  refine ⟨261736312992980025594366755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174490875328653350396244503 261736312992980025594366755)
  ·
    refine ⟨392604469489470038391550133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261736312992980025594366755 392604469489470038391550133)
    ·
      refine ⟨36806669014637816099207825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 392604469489470038391550133 36806669014637816099207825)
      ·
        refine ⟨27605001760978362074405869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36806669014637816099207825 27605001760978362074405869)
        ·
          refine ⟨10351875660366885777902201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27605001760978362074405869 10351875660366885777902201)
          ·
            refine ⟨7763906745275164333426651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10351875660366885777902201 7763906745275164333426651)
            ·
              refine ⟨11645860117912746500139977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7763906745275164333426651 11645860117912746500139977)
              ·
                refine ⟨8734395088434559875104983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11645860117912746500139977 8734395088434559875104983)
                ·
                  refine ⟨13101592632651839812657475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8734395088434559875104983 13101592632651839812657475)
                  ·
                    refine ⟨19652388948977759718986213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13101592632651839812657475 19652388948977759718986213)
                    ·
                      refine ⟨3684822927933329947309915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19652388948977759718986213 3684822927933329947309915)
                      ·
                        rfl

theorem cell23_7176167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_7176167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7176167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7176167 prefixEnd_7176167 := by exact prefixLift 7176167
  have htrace : WordTrace (prefixWord ++ tailWord_7176167) baseStart_7176167 baseEnd_7176167 := by
    simpa [prefixWord, tailWord_7176167, baseEnd_7176167] using wordTrace_append hprefix tailTrace_7176167
  have hstable : (prefixWord ++ tailWord_7176167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7176167).length < 2 ^ (prefixWord ++ tailWord_7176167).sum := by decide
  have hdescent : baseEnd_7176167 < baseStart_7176167 := by decide
  rcases family_descends (prefixWord ++ tailWord_7176167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7176240 : List Nat := [2, 1, 1, 1, 2, 5, 2, 2, 1, 4, 2]
def baseStart_7176240 : Nat := 118140960795 + 7176240 * 2 ^ 59
def prefixEnd_7176240 : Nat := 4983230072969 + 3 ^ 40 * 7176240 * 2
def baseEnd_7176240 : Nat := 3684860412021108161697079

theorem tailTrace_7176240 : CollatzResearch.WordTrace tailWord_7176240 prefixEnd_7176240 3684860412021108161697079 := by
  unfold tailWord_7176240
  simp only [CollatzResearch.WordTrace]
  refine ⟨130869487760857779530887087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174492650347810372707849449 130869487760857779530887087)
  ·
    refine ⟨196304231641286669296330631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130869487760857779530887087 196304231641286669296330631)
    ·
      refine ⟨294456347461930003944495947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196304231641286669296330631 294456347461930003944495947)
      ·
        refine ⟨441684521192895005916743921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294456347461930003944495947 441684521192895005916743921)
        ·
          refine ⟨331263390894671254437557941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 441684521192895005916743921 331263390894671254437557941)
          ·
            refine ⟨31055942896375430103521057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 331263390894671254437557941 31055942896375430103521057)
            ·
              refine ⟨23291957172281572577640793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31055942896375430103521057 23291957172281572577640793)
              ·
                refine ⟨17468967879211179433230595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23291957172281572577640793 17468967879211179433230595)
                ·
                  refine ⟨26203451818816769149845893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17468967879211179433230595 26203451818816769149845893)
                  ·
                    refine ⟨4913147216028144215596105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26203451818816769149845893 4913147216028144215596105)
                    ·
                      refine ⟨3684860412021108161697079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4913147216028144215596105 3684860412021108161697079)
                      ·
                        rfl

theorem cell23_7176240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 2, 1, 4, 2].length) (baseStart_7176240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7176240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7176240 prefixEnd_7176240 := by exact prefixLift 7176240
  have htrace : WordTrace (prefixWord ++ tailWord_7176240) baseStart_7176240 baseEnd_7176240 := by
    simpa [prefixWord, tailWord_7176240, baseEnd_7176240] using wordTrace_append hprefix tailTrace_7176240
  have hstable : (prefixWord ++ tailWord_7176240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7176240).length < 2 ^ (prefixWord ++ tailWord_7176240).sum := by decide
  have hdescent : baseEnd_7176240 < baseStart_7176240 := by decide
  rcases family_descends (prefixWord ++ tailWord_7176240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7176253 : List Nat := [1, 4, 1, 3, 1, 1, 1, 1, 4, 2, 4]
def baseStart_7176253 : Nat := 118140960795 + 7176253 * 2 ^ 59
def prefixEnd_7176253 : Nat := 4983230072969 + 3 ^ 40 * 7176253 * 2
def baseEnd_7176253 : Nat := 3684867087269616610834519

theorem tailTrace_7176253 : CollatzResearch.WordTrace tailWord_7176253 prefixEnd_7176253 3684867087269616610834519 := by
  unfold tailWord_7176253
  simp only [CollatzResearch.WordTrace]
  refine ⟨261739449670668462281997413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174492966447112308187998275 261739449670668462281997413)
  ·
    refine ⟨49076146813250336677874515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 261739449670668462281997413 49076146813250336677874515)
    ·
      refine ⟨73614220219875505016811773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49076146813250336677874515 73614220219875505016811773)
      ·
        refine ⟨27605332582453314381304415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73614220219875505016811773 27605332582453314381304415)
        ·
          refine ⟨41407998873679971571956623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27605332582453314381304415 41407998873679971571956623)
          ·
            refine ⟨62111998310519957357934935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41407998873679971571956623 62111998310519957357934935)
            ·
              refine ⟨93167997465779936036902403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62111998310519957357934935 93167997465779936036902403)
              ·
                refine ⟨139751996198669904055353605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93167997465779936036902403 139751996198669904055353605)
                ·
                  refine ⟨26203499287250607010378801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 139751996198669904055353605 26203499287250607010378801)
                  ·
                    refine ⟨19652624465437955257784101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26203499287250607010378801 19652624465437955257784101)
                    ·
                      refine ⟨3684867087269616610834519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19652624465437955257784101 3684867087269616610834519)
                      ·
                        rfl

theorem cell23_7176253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_7176253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7176253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7176253 prefixEnd_7176253 := by exact prefixLift 7176253
  have htrace : WordTrace (prefixWord ++ tailWord_7176253) baseStart_7176253 baseEnd_7176253 := by
    simpa [prefixWord, tailWord_7176253, baseEnd_7176253] using wordTrace_append hprefix tailTrace_7176253
  have hstable : (prefixWord ++ tailWord_7176253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7176253).length < 2 ^ (prefixWord ++ tailWord_7176253).sum := by decide
  have hdescent : baseEnd_7176253 < baseStart_7176253 := by decide
  rcases family_descends (prefixWord ++ tailWord_7176253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7176263 : List Nat := [1, 1, 4, 1, 3, 1, 4, 1, 7]
def baseStart_7176263 : Nat := 118140960795 + 7176263 * 2 ^ 59
def prefixEnd_7176263 : Nat := 4983230072969 + 3 ^ 40 * 7176263 * 2
def baseEnd_7176263 : Nat := 409430246897351285745497

theorem tailTrace_7176263 : CollatzResearch.WordTrace tailWord_7176263 prefixEnd_7176263 409430246897351285745497 := by
  unfold tailWord_7176263
  simp only [CollatzResearch.WordTrace]
  refine ⟨261739814400632233989861443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174493209600421489326574295 261739814400632233989861443)
  ·
    refine ⟨392609721600948350984792165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261739814400632233989861443 392609721600948350984792165)
    ·
      refine ⟨73614322800177815809648531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 392609721600948350984792165 73614322800177815809648531)
      ·
        refine ⟨110421484200266723714472797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73614322800177815809648531 110421484200266723714472797)
        ·
          refine ⟨41408056575100021392927299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110421484200266723714472797 41408056575100021392927299)
          ·
            refine ⟨62112084862650032089390949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41408056575100021392927299 62112084862650032089390949)
            ·
              refine ⟨11646015911746881016760803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62112084862650032089390949 11646015911746881016760803)
              ·
                refine ⟨17469023867620321525141205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11646015911746881016760803 17469023867620321525141205)
                ·
                  refine ⟨409430246897351285745497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17469023867620321525141205 409430246897351285745497)
                  ·
                    rfl

theorem cell23_7176263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 1, 7].length) (baseStart_7176263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7176263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7176263 prefixEnd_7176263 := by exact prefixLift 7176263
  have htrace : WordTrace (prefixWord ++ tailWord_7176263) baseStart_7176263 baseEnd_7176263 := by
    simpa [prefixWord, tailWord_7176263, baseEnd_7176263] using wordTrace_append hprefix tailTrace_7176263
  have hstable : (prefixWord ++ tailWord_7176263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7176263).length < 2 ^ (prefixWord ++ tailWord_7176263).sum := by decide
  have hdescent : baseEnd_7176263 < baseStart_7176263 := by decide
  rcases family_descends (prefixWord ++ tailWord_7176263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7176274 : List Nat := [3, 2, 2, 1, 4, 2, 1, 1, 1, 4, 2]
def baseStart_7176274 : Nat := 118140960795 + 7176274 * 2 ^ 59
def prefixEnd_7176274 : Nat := 4983230072969 + 3 ^ 40 * 7176274 * 2
def baseEnd_7176274 : Nat := 3684877870363361028671923

theorem tailTrace_7176274 : CollatzResearch.WordTrace tailWord_7176274 prefixEnd_7176274 3684877870363361028671923 := by
  unfold tailWord_7176274
  simp only [CollatzResearch.WordTrace]
  refine ⟨65435053900898095717127969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174493477069061588579007917 65435053900898095717127969)
  ·
    refine ⟨49076290425673571787845977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65435053900898095717127969 49076290425673571787845977)
    ·
      refine ⟨36807217819255178840884483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49076290425673571787845977 36807217819255178840884483)
      ·
        refine ⟨55210826728882768261326725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36807217819255178840884483 55210826728882768261326725)
        ·
          refine ⟨10352030011665519048998761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55210826728882768261326725 10352030011665519048998761)
          ·
            refine ⟨7764022508749139286749071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10352030011665519048998761 7764022508749139286749071)
            ·
              refine ⟨11646033763123708930123607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7764022508749139286749071 11646033763123708930123607)
              ·
                refine ⟨17469050644685563395185411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11646033763123708930123607 17469050644685563395185411)
                ·
                  refine ⟨26203575967028345092778117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17469050644685563395185411 26203575967028345092778117)
                  ·
                    refine ⟨4913170493817814704895897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26203575967028345092778117 4913170493817814704895897)
                    ·
                      refine ⟨3684877870363361028671923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4913170493817814704895897 3684877870363361028671923)
                      ·
                        rfl

theorem cell23_7176274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 1, 1, 4, 2].length) (baseStart_7176274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7176274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7176274 prefixEnd_7176274 := by exact prefixLift 7176274
  have htrace : WordTrace (prefixWord ++ tailWord_7176274) baseStart_7176274 baseEnd_7176274 := by
    simpa [prefixWord, tailWord_7176274, baseEnd_7176274] using wordTrace_append hprefix tailTrace_7176274
  have hstable : (prefixWord ++ tailWord_7176274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7176274).length < 2 ^ (prefixWord ++ tailWord_7176274).sum := by decide
  have hdescent : baseEnd_7176274 < baseStart_7176274 := by decide
  rcases family_descends (prefixWord ++ tailWord_7176274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7176293 : List Nat := [1, 3, 1, 3, 2, 2, 2, 1, 1, 7]
def baseStart_7176293 : Nat := 118140960795 + 7176293 * 2 ^ 59
def prefixEnd_7176293 : Nat := 4983230072969 + 3 ^ 40 * 7176293 * 2
def baseEnd_7176293 : Nat := 1228295875498598818111445

theorem tailTrace_7176293 : CollatzResearch.WordTrace tailWord_7176293 prefixEnd_7176293 1228295875498598818111445 := by
  unfold tailWord_7176293
  simp only [CollatzResearch.WordTrace]
  refine ⟨261740908590523549113453533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174493939060349032742302355 261740908590523549113453533)
  ·
    refine ⟨98152840721446330917545075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261740908590523549113453533 98152840721446330917545075)
    ·
      refine ⟨147229261082169496376317613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98152840721446330917545075 147229261082169496376317613)
      ·
        refine ⟨55210972905813561141119105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147229261082169496376317613 55210972905813561141119105)
        ·
          refine ⟨41408229679360170855839329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55210972905813561141119105 41408229679360170855839329)
          ·
            refine ⟨31056172259520128141879497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41408229679360170855839329 31056172259520128141879497)
            ·
              refine ⟨23292129194640096106409623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31056172259520128141879497 23292129194640096106409623)
              ·
                refine ⟨34938193791960144159614435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23292129194640096106409623 34938193791960144159614435)
                ·
                  refine ⟨52407290687940216239421653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34938193791960144159614435 52407290687940216239421653)
                  ·
                    refine ⟨1228295875498598818111445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52407290687940216239421653 1228295875498598818111445)
                    ·
                      rfl

theorem cell23_7176293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 1, 1, 7].length) (baseStart_7176293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7176293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7176293 prefixEnd_7176293 := by exact prefixLift 7176293
  have htrace : WordTrace (prefixWord ++ tailWord_7176293) baseStart_7176293 baseEnd_7176293 := by
    simpa [prefixWord, tailWord_7176293, baseEnd_7176293] using wordTrace_append hprefix tailTrace_7176293
  have hstable : (prefixWord ++ tailWord_7176293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7176293).length < 2 ^ (prefixWord ++ tailWord_7176293).sum := by decide
  have hdescent : baseEnd_7176293 < baseStart_7176293 := by decide
  rcases family_descends (prefixWord ++ tailWord_7176293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7176310 : List Nat := [5, 1, 1, 2, 1, 2, 1, 1, 4, 5]
def baseStart_7176310 : Nat := 118140960795 + 7176310 * 2 ^ 59
def prefixEnd_7176310 : Nat := 4983230072969 + 3 ^ 40 * 7176310 * 2
def baseEnd_7176310 : Nat := 1228298785222307629273919

theorem tailTrace_7176310 : CollatzResearch.WordTrace tailWord_7176310 prefixEnd_7176310 1228298785222307629273919 := by
  unfold tailWord_7176310
  simp only [CollatzResearch.WordTrace]
  refine ⟨16358845539466372563551399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 174494352420974640677881589 16358845539466372563551399)
  ·
    refine ⟨24538268309199558845327099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16358845539466372563551399 24538268309199558845327099)
    ·
      refine ⟨36807402463799338267990649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24538268309199558845327099 36807402463799338267990649)
      ·
        refine ⟨27605551847849503700992987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36807402463799338267990649 27605551847849503700992987)
        ·
          refine ⟨41408327771774255551489481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27605551847849503700992987 41408327771774255551489481)
          ·
            refine ⟨31056245828830691663617111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41408327771774255551489481 31056245828830691663617111)
            ·
              refine ⟨46584368743246037495425667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31056245828830691663617111 46584368743246037495425667)
              ·
                refine ⟨69876553114869056243138501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46584368743246037495425667 69876553114869056243138501)
                ·
                  refine ⟨13101853709037948045588469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69876553114869056243138501 13101853709037948045588469)
                  ·
                    refine ⟨1228298785222307629273919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13101853709037948045588469 1228298785222307629273919)
                    ·
                      rfl

theorem cell23_7176310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 4, 5].length) (baseStart_7176310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7176310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7176310 prefixEnd_7176310 := by exact prefixLift 7176310
  have htrace : WordTrace (prefixWord ++ tailWord_7176310) baseStart_7176310 baseEnd_7176310 := by
    simpa [prefixWord, tailWord_7176310, baseEnd_7176310] using wordTrace_append hprefix tailTrace_7176310
  have hstable : (prefixWord ++ tailWord_7176310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7176310).length < 2 ^ (prefixWord ++ tailWord_7176310).sum := by decide
  have hdescent : baseEnd_7176310 < baseStart_7176310 := by decide
  rcases family_descends (prefixWord ++ tailWord_7176310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7176357 : List Nat := [1, 3, 1, 2, 1, 3, 2, 5, 1, 4]
def baseStart_7176357 : Nat := 118140960795 + 7176357 * 2 ^ 59
def prefixEnd_7176357 : Nat := 4983230072969 + 3 ^ 40 * 7176357 * 2
def baseEnd_7176357 : Nat := 1228306829752561401311347

theorem tailTrace_7176357 : CollatzResearch.WordTrace tailWord_7176357 prefixEnd_7176357 1228306829752561401311347 := by
  unfold tailWord_7176357
  simp only [CollatzResearch.WordTrace]
  refine ⟨261743242862291688043783325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174495495241527792029188883 261743242862291688043783325)
  ·
    refine ⟨98153716073359383016418747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261743242862291688043783325 98153716073359383016418747)
    ·
      refine ⟨147230574110039074524628121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98153716073359383016418747 147230574110039074524628121)
      ·
        refine ⟨110422930582529305893471091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147230574110039074524628121 110422930582529305893471091)
        ·
          refine ⟨165634395873793958840206637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110422930582529305893471091 165634395873793958840206637)
          ·
            refine ⟨62112898452672734565077489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165634395873793958840206637 62112898452672734565077489)
            ·
              refine ⟨46584673839504550923808117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62112898452672734565077489 46584673839504550923808117)
              ·
                refine ⟨4367313172453551649107011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46584673839504550923808117 4367313172453551649107011)
                ·
                  refine ⟨6550969758680327473660517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4367313172453551649107011 6550969758680327473660517)
                  ·
                    refine ⟨1228306829752561401311347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6550969758680327473660517 1228306829752561401311347)
                    ·
                      rfl

theorem cell23_7176357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 5, 1, 4].length) (baseStart_7176357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7176357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7176357 prefixEnd_7176357 := by exact prefixLift 7176357
  have htrace : WordTrace (prefixWord ++ tailWord_7176357) baseStart_7176357 baseEnd_7176357 := by
    simpa [prefixWord, tailWord_7176357, baseEnd_7176357] using wordTrace_append hprefix tailTrace_7176357
  have hstable : (prefixWord ++ tailWord_7176357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7176357).length < 2 ^ (prefixWord ++ tailWord_7176357).sum := by decide
  have hdescent : baseEnd_7176357 < baseStart_7176357 := by decide
  rcases family_descends (prefixWord ++ tailWord_7176357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7176363 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 6, 5, 3]
def baseStart_7176363 : Nat := 118140960795 + 7176363 * 2 ^ 59
def prefixEnd_7176363 : Nat := 4983230072969 + 3 ^ 40 * 7176363 * 2
def baseEnd_7176363 : Nat := 3684923570141611180459013

theorem tailTrace_7176363 : CollatzResearch.WordTrace tailWord_7176363 prefixEnd_7176363 3684923570141611180459013 := by
  unfold tailWord_7176363
  simp only [CollatzResearch.WordTrace]
  refine ⟨261743461700269951068501743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174495641133513300712334495 261743461700269951068501743)
  ·
    refine ⟨392615192550404926602752615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261743461700269951068501743 392615192550404926602752615)
    ·
      refine ⟨588922788825607389904128923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392615192550404926602752615 588922788825607389904128923)
      ·
        refine ⟨883384183238411084856193385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 588922788825607389904128923 883384183238411084856193385)
        ·
          refine ⟨662538137428808313642145039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 883384183238411084856193385 662538137428808313642145039)
          ·
            refine ⟨993807206143212470463217559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 662538137428808313642145039 993807206143212470463217559)
            ·
              refine ⟨1490710809214818705694826339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 993807206143212470463217559 1490710809214818705694826339)
              ·
                refine ⟨2236066213822228058542239509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1490710809214818705694826339 2236066213822228058542239509)
                ·
                  refine ⟨104815603772916940244167477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2236066213822228058542239509 104815603772916940244167477)
                  ·
                    refine ⟨9826462853710963147890701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 104815603772916940244167477 9826462853710963147890701)
                    ·
                      refine ⟨3684923570141611180459013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9826462853710963147890701 3684923570141611180459013)
                      ·
                        rfl

theorem cell23_7176363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 5, 3].length) (baseStart_7176363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7176363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7176363 prefixEnd_7176363 := by exact prefixLift 7176363
  have htrace : WordTrace (prefixWord ++ tailWord_7176363) baseStart_7176363 baseEnd_7176363 := by
    simpa [prefixWord, tailWord_7176363, baseEnd_7176363] using wordTrace_append hprefix tailTrace_7176363
  have hstable : (prefixWord ++ tailWord_7176363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7176363).length < 2 ^ (prefixWord ++ tailWord_7176363).sum := by decide
  have hdescent : baseEnd_7176363 < baseStart_7176363 := by decide
  rcases family_descends (prefixWord ++ tailWord_7176363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7176370 : List Nat := [3, 2, 1, 1, 1, 3, 4, 2, 6]
def baseStart_7176370 : Nat := 118140960795 + 7176370 * 2 ^ 59
def prefixEnd_7176370 : Nat := 4983230072969 + 3 ^ 40 * 7176370 * 2
def baseEnd_7176370 : Nat := 409436351611799183674609

theorem tailTrace_7176370 : CollatzResearch.WordTrace tailWord_7176370 prefixEnd_7176370 409436351611799183674609 := by
  unfold tailWord_7176370
  simp only [CollatzResearch.WordTrace]
  refine ⟨65435929252811147816001641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174495811340829727509337709 65435929252811147816001641)
  ·
    refine ⟨49076946939608360862001231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65435929252811147816001641 49076946939608360862001231)
    ·
      refine ⟨73615420409412541293001847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49076946939608360862001231 73615420409412541293001847)
      ·
        refine ⟨110423130614118811939502771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73615420409412541293001847 110423130614118811939502771)
        ·
          refine ⟨165634695921178217909254157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110423130614118811939502771 165634695921178217909254157)
          ·
            refine ⟨62113010970441831715970309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165634695921178217909254157 62113010970441831715970309)
            ·
              refine ⟨11646189556957843446744433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62113010970441831715970309 11646189556957843446744433)
              ·
                refine ⟨8734642167718382585058325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11646189556957843446744433 8734642167718382585058325)
                ·
                  refine ⟨409436351611799183674609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8734642167718382585058325 409436351611799183674609)
                  ·
                    rfl

theorem cell23_7176370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 2, 6].length) (baseStart_7176370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7176370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7176370 prefixEnd_7176370 := by exact prefixLift 7176370
  have htrace : WordTrace (prefixWord ++ tailWord_7176370) baseStart_7176370 baseEnd_7176370 := by
    simpa [prefixWord, tailWord_7176370, baseEnd_7176370] using wordTrace_append hprefix tailTrace_7176370
  have hstable : (prefixWord ++ tailWord_7176370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7176370).length < 2 ^ (prefixWord ++ tailWord_7176370).sum := by decide
  have hdescent : baseEnd_7176370 < baseStart_7176370 := by decide
  rcases family_descends (prefixWord ++ tailWord_7176370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7176440 : List Nat := [2, 1, 2, 1, 1, 2, 1, 3, 5, 2, 3]
def baseStart_7176440 : Nat := 118140960795 + 7176440 * 2 ^ 59
def prefixEnd_7176440 : Nat := 4983230072969 + 3 ^ 40 * 7176440 * 2
def baseEnd_7176440 : Nat := 3684963108152007379196159

theorem tailTrace_7176440 : CollatzResearch.WordTrace tailWord_7176440 prefixEnd_7176440 3684963108152007379196159 := by
  unfold tailWord_7176440
  simp only [CollatzResearch.WordTrace]
  refine ⟨130873135060495496609527387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174497513413993995479369849 130873135060495496609527387)
  ·
    refine ⟨196309702590743244914291081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130873135060495496609527387 196309702590743244914291081)
    ·
      refine ⟨147232276943057433685718311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196309702590743244914291081 147232276943057433685718311)
      ·
        refine ⟨220848415414586150528577467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147232276943057433685718311 220848415414586150528577467)
        ·
          refine ⟨331272623121879225792866201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220848415414586150528577467 331272623121879225792866201)
          ·
            refine ⟨248454467341409419344649651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 331272623121879225792866201 248454467341409419344649651)
            ·
              refine ⟨372681701012114129016974477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248454467341409419344649651 372681701012114129016974477)
              ·
                refine ⟨139755637879542798381365429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 372681701012114129016974477 139755637879542798381365429)
                ·
                  refine ⟨13102091051207137348253009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 139755637879542798381365429 13102091051207137348253009)
                  ·
                    refine ⟨9826568288405353011189757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13102091051207137348253009 9826568288405353011189757)
                    ·
                      refine ⟨3684963108152007379196159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9826568288405353011189757 3684963108152007379196159)
                      ·
                        rfl

theorem cell23_7176440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 5, 2, 3].length) (baseStart_7176440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7176440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7176440 prefixEnd_7176440 := by exact prefixLift 7176440
  have htrace : WordTrace (prefixWord ++ tailWord_7176440) baseStart_7176440 baseEnd_7176440 := by
    simpa [prefixWord, tailWord_7176440, baseEnd_7176440] using wordTrace_append hprefix tailTrace_7176440
  have hstable : (prefixWord ++ tailWord_7176440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7176440).length < 2 ^ (prefixWord ++ tailWord_7176440).sum := by decide
  have hdescent : baseEnd_7176440 < baseStart_7176440 := by decide
  rcases family_descends (prefixWord ++ tailWord_7176440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7176457 : List Nat := [1, 2, 1, 1, 3, 4, 1, 4, 1, 2, 3]
def baseStart_7176457 : Nat := 118140960795 + 7176457 * 2 ^ 59
def prefixEnd_7176457 : Nat := 4983230072969 + 3 ^ 40 * 7176457 * 2
def baseEnd_7176457 : Nat := 3684971837323133812683581

theorem tailTrace_7176457 : CollatzResearch.WordTrace tailWord_7176457 prefixEnd_7176457 3684971837323133812683581 := by
  unfold tailWord_7176457
  simp only [CollatzResearch.WordTrace]
  refine ⟨261746890161929405122423625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174497926774619603414949083 261746890161929405122423625)
  ·
    refine ⟨196310167621447053841817719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261746890161929405122423625 196310167621447053841817719)
    ·
      refine ⟨294465251432170580762726579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196310167621447053841817719 294465251432170580762726579)
      ·
        refine ⟨441697877148255871144089869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294465251432170580762726579 441697877148255871144089869)
        ·
          refine ⟨165636703930595951679033701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 441697877148255871144089869 165636703930595951679033701)
          ·
            refine ⟨31056881986986740939818819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 165636703930595951679033701 31056881986986740939818819)
            ·
              refine ⟨46585322980480111409728229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31056881986986740939818819 46585322980480111409728229)
              ·
                refine ⟨8734748058840020889324043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46585322980480111409728229 8734748058840020889324043)
                ·
                  refine ⟨13102122088260031333986065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8734748058840020889324043 13102122088260031333986065)
                  ·
                    refine ⟨9826591566195023500489549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13102122088260031333986065 9826591566195023500489549)
                    ·
                      refine ⟨3684971837323133812683581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9826591566195023500489549 3684971837323133812683581)
                      ·
                        rfl

theorem cell23_7176457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 4, 1, 2, 3].length) (baseStart_7176457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7176457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7176457 prefixEnd_7176457 := by exact prefixLift 7176457
  have htrace : WordTrace (prefixWord ++ tailWord_7176457) baseStart_7176457 baseEnd_7176457 := by
    simpa [prefixWord, tailWord_7176457, baseEnd_7176457] using wordTrace_append hprefix tailTrace_7176457
  have hstable : (prefixWord ++ tailWord_7176457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7176457).length < 2 ^ (prefixWord ++ tailWord_7176457).sum := by decide
  have hdescent : baseEnd_7176457 < baseStart_7176457 := by decide
  rcases family_descends (prefixWord ++ tailWord_7176457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7176463 : List Nat := [1, 1, 2, 1, 1, 1, 3, 2, 1, 4, 6]
def baseStart_7176463 : Nat := 118140960795 + 7176463 * 2 ^ 59
def prefixEnd_7176463 : Nat := 4983230072969 + 3 ^ 40 * 7176463 * 2
def baseEnd_7176463 : Nat := 3684974918207060789208553

theorem tailTrace_7176463 : CollatzResearch.WordTrace tailWord_7176463 prefixEnd_7176463 3684974918207060789208553 := by
  unfold tailWord_7176463
  simp only [CollatzResearch.WordTrace]
  refine ⟨261747108999907668147142043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174498072666605112098094695 261747108999907668147142043)
  ·
    refine ⟨392620663499861502220713065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261747108999907668147142043 392620663499861502220713065)
    ·
      refine ⟨294465497624896126665534799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 392620663499861502220713065 294465497624896126665534799)
      ·
        refine ⟨441698246437344189998302199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294465497624896126665534799 441698246437344189998302199)
        ·
          refine ⟨662547369656016284997453299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 441698246437344189998302199 662547369656016284997453299)
          ·
            refine ⟨993821054484024427496179949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 662547369656016284997453299 993821054484024427496179949)
            ·
              refine ⟨372682895431509160311067481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 993821054484024427496179949 372682895431509160311067481)
              ·
                refine ⟨279512171573631870233300611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 372682895431509160311067481 279512171573631870233300611)
                ·
                  refine ⟨419268257360447805349950917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 279512171573631870233300611 419268257360447805349950917)
                  ·
                    refine ⟨78612798255083963503115797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 419268257360447805349950917 78612798255083963503115797)
                    ·
                      refine ⟨3684974918207060789208553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78612798255083963503115797 3684974918207060789208553)
                      ·
                        rfl

theorem cell23_7176463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 4, 6].length) (baseStart_7176463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7176463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7176463 prefixEnd_7176463 := by exact prefixLift 7176463
  have htrace : WordTrace (prefixWord ++ tailWord_7176463) baseStart_7176463 baseEnd_7176463 := by
    simpa [prefixWord, tailWord_7176463, baseEnd_7176463] using wordTrace_append hprefix tailTrace_7176463
  have hstable : (prefixWord ++ tailWord_7176463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7176463).length < 2 ^ (prefixWord ++ tailWord_7176463).sum := by decide
  have hdescent : baseEnd_7176463 < baseStart_7176463 := by decide
  rcases family_descends (prefixWord ++ tailWord_7176463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7176477 : List Nat := [1, 4, 2, 3, 2, 2, 9]
def baseStart_7176477 : Nat := 118140960795 + 7176477 * 2 ^ 59
def prefixEnd_7176477 : Nat := 4983230072969 + 3 ^ 40 * 7176477 * 2
def baseEnd_7176477 : Nat := 45493606258471897955969

theorem tailTrace_7176477 : CollatzResearch.WordTrace tailWord_7176477 prefixEnd_7176477 45493606258471897955969 := by
  unfold tailWord_7176477
  simp only [CollatzResearch.WordTrace]
  refine ⟨261747619621856948538151685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174498413081237965692101123 261747619621856948538151685)
  ·
    refine ⟨49077678679098177850903441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 261747619621856948538151685 49077678679098177850903441)
    ·
      refine ⟨36808259009323633388177581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49077678679098177850903441 36808259009323633388177581)
      ·
        refine ⟨13803097128496362520566593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36808259009323633388177581 13803097128496362520566593)
        ·
          refine ⟨10352322846372271890424945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13803097128496362520566593 10352322846372271890424945)
          ·
            refine ⟨7764242134779203917818709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10352322846372271890424945 7764242134779203917818709)
            ·
              refine ⟨45493606258471897955969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7764242134779203917818709 45493606258471897955969)
              ·
                rfl

theorem cell23_7176477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 9].length) (baseStart_7176477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7176477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7176477 prefixEnd_7176477 := by exact prefixLift 7176477
  have htrace : WordTrace (prefixWord ++ tailWord_7176477) baseStart_7176477 baseEnd_7176477 := by
    simpa [prefixWord, tailWord_7176477, baseEnd_7176477] using wordTrace_append hprefix tailTrace_7176477
  have hstable : (prefixWord ++ tailWord_7176477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7176477).length < 2 ^ (prefixWord ++ tailWord_7176477).sum := by decide
  have hdescent : baseEnd_7176477 < baseStart_7176477 := by decide
  rcases family_descends (prefixWord ++ tailWord_7176477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7176488 : List Nat := [2, 1, 5, 1, 3, 2, 1, 1, 3, 2, 2]
def baseStart_7176488 : Nat := 118140960795 + 7176488 * 2 ^ 59
def prefixEnd_7176488 : Nat := 4983230072969 + 3 ^ 40 * 7176488 * 2
def baseEnd_7176488 : Nat := 3684987755223423191395939

theorem tailTrace_7176488 : CollatzResearch.WordTrace tailWord_7176488 prefixEnd_7176488 3684987755223423191395939 := by
  unfold tailWord_7176488
  simp only [CollatzResearch.WordTrace]
  refine ⟨130874010412408548708401059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174498680549878064944534745 130874010412408548708401059)
  ·
    refine ⟨196311015618612823062601589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130874010412408548708401059 196311015618612823062601589)
    ·
      refine ⟨18404157714244952162118899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 196311015618612823062601589 18404157714244952162118899)
      ·
        refine ⟨27606236571367428243178349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18404157714244952162118899 27606236571367428243178349)
        ·
          refine ⟨10352338714262785591191881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27606236571367428243178349 10352338714262785591191881)
          ·
            refine ⟨7764254035697089193393911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10352338714262785591191881 7764254035697089193393911)
            ·
              refine ⟨11646381053545633790090867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7764254035697089193393911 11646381053545633790090867)
              ·
                refine ⟨17469571580318450685136301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11646381053545633790090867 17469571580318450685136301)
                ·
                  refine ⟨6551089342619419006926113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17469571580318450685136301 6551089342619419006926113)
                  ·
                    refine ⟨4913317006964564255194585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6551089342619419006926113 4913317006964564255194585)
                    ·
                      refine ⟨3684987755223423191395939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4913317006964564255194585 3684987755223423191395939)
                      ·
                        rfl

theorem cell23_7176488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 1, 3, 2, 2].length) (baseStart_7176488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7176488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7176488 prefixEnd_7176488 := by exact prefixLift 7176488
  have htrace : WordTrace (prefixWord ++ tailWord_7176488) baseStart_7176488 baseEnd_7176488 := by
    simpa [prefixWord, tailWord_7176488, baseEnd_7176488] using wordTrace_append hprefix tailTrace_7176488
  have hstable : (prefixWord ++ tailWord_7176488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7176488).length < 2 ^ (prefixWord ++ tailWord_7176488).sum := by decide
  have hdescent : baseEnd_7176488 < baseStart_7176488 := by decide
  rcases family_descends (prefixWord ++ tailWord_7176488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7176494 : List Nat := [4, 1, 3, 3, 1, 1, 2, 8]
def baseStart_7176494 : Nat := 118140960795 + 7176494 * 2 ^ 59
def prefixEnd_7176494 : Nat := 4983230072969 + 3 ^ 40 * 7176494 * 2
def baseEnd_7176494 : Nat := 136481142078050006219293

theorem tailTrace_7176494 : CollatzResearch.WordTrace tailWord_7176494 prefixEnd_7176494 136481142078050006219293 := by
  unfold tailWord_7176494
  simp only [CollatzResearch.WordTrace]
  refine ⟨32718529957849420055190067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174498826441863573627680357 32718529957849420055190067)
  ·
    refine ⟨49077794936774130082785101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32718529957849420055190067 49077794936774130082785101)
    ·
      refine ⟨18404173101290298781044413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49077794936774130082785101 18404173101290298781044413)
      ·
        refine ⟨6901564912983862042891655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18404173101290298781044413 6901564912983862042891655)
        ·
          refine ⟨10352347369475793064337483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6901564912983862042891655 10352347369475793064337483)
          ·
            refine ⟨15528521054213689596506225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10352347369475793064337483 15528521054213689596506225)
            ·
              refine ⟨11646390790660267197379669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15528521054213689596506225 11646390790660267197379669)
              ·
                refine ⟨136481142078050006219293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11646390790660267197379669 136481142078050006219293)
                ·
                  rfl

theorem cell23_7176494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 8].length) (baseStart_7176494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7176494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7176494 prefixEnd_7176494 := by exact prefixLift 7176494
  have htrace : WordTrace (prefixWord ++ tailWord_7176494) baseStart_7176494 baseEnd_7176494 := by
    simpa [prefixWord, tailWord_7176494, baseEnd_7176494] using wordTrace_append hprefix tailTrace_7176494
  have hstable : (prefixWord ++ tailWord_7176494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7176494).length < 2 ^ (prefixWord ++ tailWord_7176494).sum := by decide
  have hdescent : baseEnd_7176494 < baseStart_7176494 := by decide
  rcases family_descends (prefixWord ++ tailWord_7176494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7176498 : List Nat := [3, 2, 1, 1, 6, 1, 2, 1, 2, 4]
def baseStart_7176498 : Nat := 118140960795 + 7176498 * 2 ^ 59
def prefixEnd_7176498 : Nat := 4983230072969 + 3 ^ 40 * 7176498 * 2
def baseEnd_7176498 : Nat := 1228330963343322717423631

theorem tailTrace_7176498 : CollatzResearch.WordTrace tailWord_7176498 prefixEnd_7176498 1228330963343322717423631 := by
  unfold tailWord_7176498
  simp only [CollatzResearch.WordTrace]
  refine ⟨65437096388695217281166537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174498923703187246083110765 65437096388695217281166537)
  ·
    refine ⟨49077822291521412960874903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65437096388695217281166537 49077822291521412960874903)
    ·
      refine ⟨73616733437282119441312355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49077822291521412960874903 73616733437282119441312355)
      ·
        refine ⟨110425100155923179161968533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73616733437282119441312355 110425100155923179161968533)
        ·
          refine ⟨5176176569808899023217275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 110425100155923179161968533 5176176569808899023217275)
          ·
            refine ⟨7764264854713348534825913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5176176569808899023217275 7764264854713348534825913)
            ·
              refine ⟨5823198641035011401119435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7764264854713348534825913 5823198641035011401119435)
              ·
                refine ⟨8734797961552517101679153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5823198641035011401119435 8734797961552517101679153)
                ·
                  refine ⟨6551098471164387826259365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8734797961552517101679153 6551098471164387826259365)
                  ·
                    refine ⟨1228330963343322717423631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6551098471164387826259365 1228330963343322717423631)
                    ·
                      rfl

theorem cell23_7176498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 2, 1, 2, 4].length) (baseStart_7176498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7176498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7176498 prefixEnd_7176498 := by exact prefixLift 7176498
  have htrace : WordTrace (prefixWord ++ tailWord_7176498) baseStart_7176498 baseEnd_7176498 := by
    simpa [prefixWord, tailWord_7176498, baseEnd_7176498] using wordTrace_append hprefix tailTrace_7176498
  have hstable : (prefixWord ++ tailWord_7176498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7176498).length < 2 ^ (prefixWord ++ tailWord_7176498).sum := by decide
  have hdescent : baseEnd_7176498 < baseStart_7176498 := by decide
  rcases family_descends (prefixWord ++ tailWord_7176498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7176557 : List Nat := [1, 5, 1, 1, 1, 2, 3, 1, 2, 2, 4]
def baseStart_7176557 : Nat := 118140960795 + 7176557 * 2 ^ 59
def prefixEnd_7176557 : Nat := 4983230072969 + 3 ^ 40 * 7176557 * 2
def baseEnd_7176557 : Nat := 3685023185388583421433121

theorem tailTrace_7176557 : CollatzResearch.WordTrace tailWord_7176557 prefixEnd_7176557 3685023185388583421433121 := by
  unfold tailWord_7176557
  simp only [CollatzResearch.WordTrace]
  refine ⟨261750537461567122201063925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174500358307711414800709283 261750537461567122201063925)
  ·
    refine ⟨24539112887021917706349743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 261750537461567122201063925 24539112887021917706349743)
    ·
      refine ⟨36808669330532876559524615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24539112887021917706349743 36808669330532876559524615)
      ·
        refine ⟨55213003995799314839286923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36808669330532876559524615 55213003995799314839286923)
        ·
          refine ⟨82819505993698972258930385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55213003995799314839286923 82819505993698972258930385)
          ·
            refine ⟨62114629495274229194197789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82819505993698972258930385 62114629495274229194197789)
            ·
              refine ⟨23292986060727835947824171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62114629495274229194197789 23292986060727835947824171)
              ·
                refine ⟨34939479091091753921736257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23292986060727835947824171 34939479091091753921736257)
                ·
                  refine ⟨26204609318318815441302193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34939479091091753921736257 26204609318318815441302193)
                  ·
                    refine ⟨19653456988739111580976645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26204609318318815441302193 19653456988739111580976645)
                    ·
                      refine ⟨3685023185388583421433121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19653456988739111580976645 3685023185388583421433121)
                      ·
                        rfl

theorem cell23_7176557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_7176557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7176557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7176557 prefixEnd_7176557 := by exact prefixLift 7176557
  have htrace : WordTrace (prefixWord ++ tailWord_7176557) baseStart_7176557 baseEnd_7176557 := by
    simpa [prefixWord, tailWord_7176557, baseEnd_7176557] using wordTrace_append hprefix tailTrace_7176557
  have hstable : (prefixWord ++ tailWord_7176557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7176557).length < 2 ^ (prefixWord ++ tailWord_7176557).sum := by decide
  have hdescent : baseEnd_7176557 < baseStart_7176557 := by decide
  rcases family_descends (prefixWord ++ tailWord_7176557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7176584 : List Nat := [2, 1, 3, 3, 1, 1, 4, 3, 5]
def baseStart_7176584 : Nat := 118140960795 + 7176584 * 2 ^ 59
def prefixEnd_7176584 : Nat := 4983230072969 + 3 ^ 40 * 7176584 * 2
def baseEnd_7176584 : Nat := 409448561040694979532833

theorem tailTrace_7176584 : CollatzResearch.WordTrace tailWord_7176584 prefixEnd_7176584 409448561040694979532833 := by
  unfold tailWord_7176584
  simp only [CollatzResearch.WordTrace]
  refine ⟨130875761116234652906148403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174501014821646203874864537 130875761116234652906148403)
  ·
    refine ⟨196313641674351979359222605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130875761116234652906148403 196313641674351979359222605)
    ·
      refine ⟨73617615627881992259708477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196313641674351979359222605 73617615627881992259708477)
      ·
        refine ⟨27606605860455747097390679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73617615627881992259708477 27606605860455747097390679)
        ·
          refine ⟨41409908790683620646086019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27606605860455747097390679 41409908790683620646086019)
          ·
            refine ⟨62114863186025430969129029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41409908790683620646086019 62114863186025430969129029)
            ·
              refine ⟨11646536847379768306711693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62114863186025430969129029 11646536847379768306711693)
              ·
                refine ⟨4367451317767413115016885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11646536847379768306711693 4367451317767413115016885)
                ·
                  refine ⟨409448561040694979532833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4367451317767413115016885 409448561040694979532833)
                  ·
                    rfl

theorem cell23_7176584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 3, 5].length) (baseStart_7176584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7176584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7176584 prefixEnd_7176584 := by exact prefixLift 7176584
  have htrace : WordTrace (prefixWord ++ tailWord_7176584) baseStart_7176584 baseEnd_7176584 := by
    simpa [prefixWord, tailWord_7176584, baseEnd_7176584] using wordTrace_append hprefix tailTrace_7176584
  have hstable : (prefixWord ++ tailWord_7176584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7176584).length < 2 ^ (prefixWord ++ tailWord_7176584).sum := by decide
  have hdescent : baseEnd_7176584 < baseStart_7176584 := by decide
  rcases family_descends (prefixWord ++ tailWord_7176584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7176661 : List Nat := [1, 3, 2, 3, 1, 4, 1, 1, 3, 4]
def baseStart_7176661 : Nat := 118140960795 + 7176661 * 2 ^ 59
def prefixEnd_7176661 : Nat := 4983230072969 + 3 ^ 40 * 7176661 * 2
def baseEnd_7176661 : Nat := 1228358862458883671510881

theorem tailTrace_7176661 : CollatzResearch.WordTrace tailWord_7176661 prefixEnd_7176661 1228358862458883671510881 := by
  unfold tailWord_7176661
  simp only [CollatzResearch.WordTrace]
  refine ⟨261754330653190347962849837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174502887102126898641899891 261754330653190347962849837)
  ·
    refine ⟨98157873994946380486068689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261754330653190347962849837 98157873994946380486068689)
    ·
      refine ⟨73618405496209785364551517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98157873994946380486068689 73618405496209785364551517)
      ·
        refine ⟨27606902061078669511706819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73618405496209785364551517 27606902061078669511706819)
        ·
          refine ⟨41410353091618004267560229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27606902061078669511706819 41410353091618004267560229)
          ·
            refine ⟨7764441204678375800167543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41410353091618004267560229 7764441204678375800167543)
            ·
              refine ⟨11646661807017563700251315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7764441204678375800167543 11646661807017563700251315)
              ·
                refine ⟨17469992710526345550376973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11646661807017563700251315 17469992710526345550376973)
                ·
                  refine ⟨6551247266447379581391365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17469992710526345550376973 6551247266447379581391365)
                  ·
                    refine ⟨1228358862458883671510881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6551247266447379581391365 1228358862458883671510881)
                    ·
                      rfl

theorem cell23_7176661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 1, 3, 4].length) (baseStart_7176661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7176661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7176661 prefixEnd_7176661 := by exact prefixLift 7176661
  have htrace : WordTrace (prefixWord ++ tailWord_7176661) baseStart_7176661 baseEnd_7176661 := by
    simpa [prefixWord, tailWord_7176661, baseEnd_7176661] using wordTrace_append hprefix tailTrace_7176661
  have hstable : (prefixWord ++ tailWord_7176661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7176661).length < 2 ^ (prefixWord ++ tailWord_7176661).sum := by decide
  have hdescent : baseEnd_7176661 < baseStart_7176661 := by decide
  rcases family_descends (prefixWord ++ tailWord_7176661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7176684 : List Nat := [2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 3]
def baseStart_7176684 : Nat := 118140960795 + 7176684 * 2 ^ 59
def prefixEnd_7176684 : Nat := 4983230072969 + 3 ^ 40 * 7176684 * 2
def baseEnd_7176684 : Nat := 3685088397431704424545037

theorem tailTrace_7176684 : CollatzResearch.WordTrace tailWord_7176684 prefixEnd_7176684 3685088397431704424545037 := by
  unfold tailWord_7176684
  simp only [CollatzResearch.WordTrace]
  refine ⟨130877584766053511445468553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174503446354738015260624737 130877584766053511445468553)
  ·
    refine ⟨98158188574540133584101415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130877584766053511445468553 98158188574540133584101415)
    ·
      refine ⟨147237282861810200376152123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98158188574540133584101415 147237282861810200376152123)
      ·
        refine ⟨220855924292715300564228185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147237282861810200376152123 220855924292715300564228185)
        ·
          refine ⟨165641943219536475423171139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220855924292715300564228185 165641943219536475423171139)
          ·
            refine ⟨248462914829304713134756709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165641943219536475423171139 248462914829304713134756709)
            ·
              refine ⟨46586796530494633712766883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 248462914829304713134756709 46586796530494633712766883)
              ·
                refine ⟨69880194795741950569150325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46586796530494633712766883 69880194795741950569150325)
                ·
                  refine ⟨6551268262100807865857843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69880194795741950569150325 6551268262100807865857843)
                  ·
                    refine ⟨9826902393151211798786765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6551268262100807865857843 9826902393151211798786765)
                    ·
                      refine ⟨3685088397431704424545037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9826902393151211798786765 3685088397431704424545037)
                      ·
                        rfl

theorem cell23_7176684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 3].length) (baseStart_7176684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7176684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7176684 prefixEnd_7176684 := by exact prefixLift 7176684
  have htrace : WordTrace (prefixWord ++ tailWord_7176684) baseStart_7176684 baseEnd_7176684 := by
    simpa [prefixWord, tailWord_7176684, baseEnd_7176684] using wordTrace_append hprefix tailTrace_7176684
  have hstable : (prefixWord ++ tailWord_7176684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7176684).length < 2 ^ (prefixWord ++ tailWord_7176684).sum := by decide
  have hdescent : baseEnd_7176684 < baseStart_7176684 := by decide
  rcases family_descends (prefixWord ++ tailWord_7176684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7176741 : List Nat := [1, 3, 1, 2, 2, 1, 3, 1, 5, 2, 2]
def baseStart_7176741 : Nat := 118140960795 + 7176741 * 2 ^ 59
def prefixEnd_7176741 : Nat := 4983230072969 + 3 ^ 40 * 7176741 * 2
def baseEnd_7176741 : Nat := 3685117665829010701532275

theorem tailTrace_7176741 : CollatzResearch.WordTrace tailWord_7176741 prefixEnd_7176741 3685117665829010701532275 := by
  unfold tailWord_7176741
  simp only [CollatzResearch.WordTrace]
  refine ⟨261757248492900521625762077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174504832328600347750508051 261757248492900521625762077)
  ·
    refine ⟨98158968184837695609660779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261757248492900521625762077 98158968184837695609660779)
    ·
      refine ⟨147238452277256543414491169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98158968184837695609660779 147238452277256543414491169)
      ·
        refine ⟨110428839207942407560868377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147238452277256543414491169 110428839207942407560868377)
        ·
          refine ⟨82821629405956805670651283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110428839207942407560868377 82821629405956805670651283)
          ·
            refine ⟨124232444108935208505976925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82821629405956805670651283 124232444108935208505976925)
            ·
              refine ⟨46587166540850703189741347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124232444108935208505976925 46587166540850703189741347)
              ·
                refine ⟨69880749811276054784612021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46587166540850703189741347 69880749811276054784612021)
                ·
                  refine ⟨6551320294807130136057377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69880749811276054784612021 6551320294807130136057377)
                  ·
                    refine ⟨4913490221105347602043033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6551320294807130136057377 4913490221105347602043033)
                    ·
                      refine ⟨3685117665829010701532275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4913490221105347602043033 3685117665829010701532275)
                      ·
                        rfl

theorem cell23_7176741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 5, 2, 2].length) (baseStart_7176741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7176741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7176741 prefixEnd_7176741 := by exact prefixLift 7176741
  have htrace : WordTrace (prefixWord ++ tailWord_7176741) baseStart_7176741 baseEnd_7176741 := by
    simpa [prefixWord, tailWord_7176741, baseEnd_7176741] using wordTrace_append hprefix tailTrace_7176741
  have hstable : (prefixWord ++ tailWord_7176741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7176741).length < 2 ^ (prefixWord ++ tailWord_7176741).sum := by decide
  have hdescent : baseEnd_7176741 < baseStart_7176741 := by decide
  rcases family_descends (prefixWord ++ tailWord_7176741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7176754 : List Nat := [3, 2, 1, 1, 2, 1, 4, 2, 1, 2, 4]
def baseStart_7176754 : Nat := 118140960795 + 7176754 * 2 ^ 59
def prefixEnd_7176754 : Nat := 4983230072969 + 3 ^ 40 * 7176754 * 2
def baseEnd_7176754 : Nat := 3685124341077519150669715

theorem tailTrace_7176754 : CollatzResearch.WordTrace tailWord_7176754 prefixEnd_7176754 3685124341077519150669715 := by
  unfold tailWord_7176754
  simp only [CollatzResearch.WordTrace]
  refine ⟨65439430660463356211496329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174505148427902283230656877 65439430660463356211496329)
  ·
    refine ⟨49079572995347517158622247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65439430660463356211496329 49079572995347517158622247)
    ·
      refine ⟨73619359493021275737933371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49079572995347517158622247 73619359493021275737933371)
      ·
        refine ⟨110429039239531913606900057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73619359493021275737933371 110429039239531913606900057)
        ·
          refine ⟨82821779429648935205175043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110429039239531913606900057 82821779429648935205175043)
          ·
            refine ⟨124232669144473402807762565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82821779429648935205175043 124232669144473402807762565)
            ·
              refine ⟨23293625464588763026455481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 124232669144473402807762565 23293625464588763026455481)
              ·
                refine ⟨17470219098441572269841611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23293625464588763026455481 17470219098441572269841611)
                ·
                  refine ⟨26205328647662358404762417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17470219098441572269841611 26205328647662358404762417)
                  ·
                    refine ⟨19653996485746768803571813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26205328647662358404762417 19653996485746768803571813)
                    ·
                      refine ⟨3685124341077519150669715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19653996485746768803571813 3685124341077519150669715)
                      ·
                        rfl

theorem cell23_7176754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 2, 1, 2, 4].length) (baseStart_7176754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7176754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7176754 prefixEnd_7176754 := by exact prefixLift 7176754
  have htrace : WordTrace (prefixWord ++ tailWord_7176754) baseStart_7176754 baseEnd_7176754 := by
    simpa [prefixWord, tailWord_7176754, baseEnd_7176754] using wordTrace_append hprefix tailTrace_7176754
  have hstable : (prefixWord ++ tailWord_7176754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7176754).length < 2 ^ (prefixWord ++ tailWord_7176754).sum := by decide
  have hdescent : baseEnd_7176754 < baseStart_7176754 := by decide
  rcases family_descends (prefixWord ++ tailWord_7176754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7176758 : List Nat := [5, 1, 2, 1, 2, 2, 1, 3, 1, 1, 4]
def baseStart_7176758 : Nat := 118140960795 + 7176758 * 2 ^ 59
def prefixEnd_7176758 : Nat := 4983230072969 + 3 ^ 40 * 7176758 * 2
def baseEnd_7176758 : Nat := 3685126395000137135019697

theorem tailTrace_7176758 : CollatzResearch.WordTrace tailWord_7176758 prefixEnd_7176758 3685126395000137135019697 := by
  unfold tailWord_7176758
  simp only [CollatzResearch.WordTrace]
  refine ⟨16359866783364933345570683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 174505245689225955686087285 16359866783364933345570683)
  ·
    refine ⟨24539800175047400018356025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16359866783364933345570683 24539800175047400018356025)
    ·
      refine ⟨18404850131285550013767019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24539800175047400018356025 18404850131285550013767019)
      ·
        refine ⟨27607275196928325020650529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18404850131285550013767019 27607275196928325020650529)
        ·
          refine ⟨20705456397696243765487897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27607275196928325020650529 20705456397696243765487897)
          ·
            refine ⟨15529092298272182824115923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20705456397696243765487897 15529092298272182824115923)
            ·
              refine ⟨23293638447408274236173885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15529092298272182824115923 23293638447408274236173885)
              ·
                refine ⟨8735114417778102838565207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23293638447408274236173885 8735114417778102838565207)
                ·
                  refine ⟨13102671626667154257847811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8735114417778102838565207 13102671626667154257847811)
                  ·
                    refine ⟨19654007440000731386771717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13102671626667154257847811 19654007440000731386771717)
                    ·
                      refine ⟨3685126395000137135019697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19654007440000731386771717 3685126395000137135019697)
                      ·
                        rfl

theorem cell23_7176758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_7176758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7176758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7176758 prefixEnd_7176758 := by exact prefixLift 7176758
  have htrace : WordTrace (prefixWord ++ tailWord_7176758) baseStart_7176758 baseEnd_7176758 := by
    simpa [prefixWord, tailWord_7176758, baseEnd_7176758] using wordTrace_append hprefix tailTrace_7176758
  have hstable : (prefixWord ++ tailWord_7176758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7176758).length < 2 ^ (prefixWord ++ tailWord_7176758).sum := by decide
  have hdescent : baseEnd_7176758 < baseStart_7176758 := by decide
  rcases family_descends (prefixWord ++ tailWord_7176758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7176761 : List Nat := [1, 2, 1, 5, 1, 1, 3, 3, 1, 2, 3]
def baseStart_7176761 : Nat := 118140960795 + 7176761 * 2 ^ 59
def prefixEnd_7176761 : Nat := 4983230072969 + 3 ^ 40 * 7176761 * 2
def baseEnd_7176761 : Nat := 3685127935442100623282183

theorem tailTrace_7176761 : CollatzResearch.WordTrace tailWord_7176761 prefixEnd_7176761 3685127935442100623282183 := by
  unfold tailWord_7176761
  simp only [CollatzResearch.WordTrace]
  refine ⟨261757977952828065041490137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174505318635218710027660091 261757977952828065041490137)
  ·
    refine ⟨196318483464621048781117603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261757977952828065041490137 196318483464621048781117603)
    ·
      refine ⟨294477725196931573171676405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196318483464621048781117603 294477725196931573171676405)
      ·
        refine ⟨27607286737212334984844663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 294477725196931573171676405 27607286737212334984844663)
        ·
          refine ⟨41410930105818502477266995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27607286737212334984844663 41410930105818502477266995)
          ·
            refine ⟨62116395158727753715900493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41410930105818502477266995 62116395158727753715900493)
            ·
              refine ⟨23293648184522907643462685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62116395158727753715900493 23293648184522907643462685)
              ·
                refine ⟨8735118069196090366298507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23293648184522907643462685 8735118069196090366298507)
                ·
                  refine ⟨13102677103794135549447761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8735118069196090366298507 13102677103794135549447761)
                  ·
                    refine ⟨9827007827845601662085821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13102677103794135549447761 9827007827845601662085821)
                    ·
                      refine ⟨3685127935442100623282183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9827007827845601662085821 3685127935442100623282183)
                      ·
                        rfl

theorem cell23_7176761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_7176761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7176761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7176761 prefixEnd_7176761 := by exact prefixLift 7176761
  have htrace : WordTrace (prefixWord ++ tailWord_7176761) baseStart_7176761 baseEnd_7176761 := by
    simpa [prefixWord, tailWord_7176761, baseEnd_7176761] using wordTrace_append hprefix tailTrace_7176761
  have hstable : (prefixWord ++ tailWord_7176761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7176761).length < 2 ^ (prefixWord ++ tailWord_7176761).sum := by decide
  have hdescent : baseEnd_7176761 < baseStart_7176761 := by decide
  rcases family_descends (prefixWord ++ tailWord_7176761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7176775 : List Nat := [1, 1, 4, 1, 4, 1, 2, 4, 1, 2, 2]
def baseStart_7176775 : Nat := 118140960795 + 7176775 * 2 ^ 59
def prefixEnd_7176775 : Nat := 4983230072969 + 3 ^ 40 * 7176775 * 2
def baseEnd_7176775 : Nat := 3685135124171263568507119

theorem tailTrace_7176775 : CollatzResearch.WordTrace tailWord_7176775 prefixEnd_7176775 3685135124171263568507119 := by
  unfold tailWord_7176775
  simp only [CollatzResearch.WordTrace]
  refine ⟨261758488574777345432499779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174505659049851563621666519 261758488574777345432499779)
  ·
    refine ⟨392637732862166018148749669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261758488574777345432499779 392637732862166018148749669)
    ·
      refine ⟨73619574911656128402890563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 392637732862166018148749669 73619574911656128402890563)
      ·
        refine ⟨110429362367484192604335845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73619574911656128402890563 110429362367484192604335845)
        ·
          refine ⟨20705505443903286113312971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110429362367484192604335845 20705505443903286113312971)
          ·
            refine ⟨31058258165854929169969457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20705505443903286113312971 31058258165854929169969457)
            ·
              refine ⟨23293693624391196877477093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31058258165854929169969457 23293693624391196877477093)
              ·
                refine ⟨4367567554573349414526955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23293693624391196877477093 4367567554573349414526955)
                ·
                  refine ⟨6551351331860024121790433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4367567554573349414526955 6551351331860024121790433)
                  ·
                    refine ⟨4913513498895018091342825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6551351331860024121790433 4913513498895018091342825)
                    ·
                      refine ⟨3685135124171263568507119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4913513498895018091342825 3685135124171263568507119)
                      ·
                        rfl

theorem cell23_7176775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 4, 1, 2, 2].length) (baseStart_7176775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7176775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7176775 prefixEnd_7176775 := by exact prefixLift 7176775
  have htrace : WordTrace (prefixWord ++ tailWord_7176775) baseStart_7176775 baseEnd_7176775 := by
    simpa [prefixWord, tailWord_7176775, baseEnd_7176775] using wordTrace_append hprefix tailTrace_7176775
  have hstable : (prefixWord ++ tailWord_7176775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7176775).length < 2 ^ (prefixWord ++ tailWord_7176775).sum := by decide
  have hdescent : baseEnd_7176775 < baseStart_7176775 := by decide
  rcases family_descends (prefixWord ++ tailWord_7176775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7176784 : List Nat := [2, 1, 1, 1, 1, 3, 2, 1, 2, 7, 2]
def baseStart_7176784 : Nat := 118140960795 + 7176784 * 2 ^ 59
def prefixEnd_7176784 : Nat := 4983230072969 + 3 ^ 40 * 7176784 * 2
def baseEnd_7176784 : Nat := 3685139745497154033294577

theorem tailTrace_7176784 : CollatzResearch.WordTrace tailWord_7176784 prefixEnd_7176784 3685139745497154033294577 := by
  unfold tailWord_7176784
  simp only [CollatzResearch.WordTrace]
  refine ⟨130879408415872369984788703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174505877887829826646384937 130879408415872369984788703)
  ·
    refine ⟨196319112623808554977183055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130879408415872369984788703 196319112623808554977183055)
    ·
      refine ⟨294478668935712832465774583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196319112623808554977183055 294478668935712832465774583)
      ·
        refine ⟨441718003403569248698661875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294478668935712832465774583 441718003403569248698661875)
        ·
          refine ⟨662577005105353873047992813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 441718003403569248698661875 662577005105353873047992813)
          ·
            refine ⟨248466376914507702392997305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 662577005105353873047992813 248466376914507702392997305)
            ·
              refine ⟨186349782685880776794747979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 248466376914507702392997305 186349782685880776794747979)
              ·
                refine ⟨279524674028821165192121969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 186349782685880776794747979 279524674028821165192121969)
                ·
                  refine ⟨209643505521615873894091477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 279524674028821165192121969 209643505521615873894091477)
                  ·
                    refine ⟨4913519660662872044392769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 209643505521615873894091477 4913519660662872044392769)
                    ·
                      refine ⟨3685139745497154033294577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4913519660662872044392769 3685139745497154033294577)
                      ·
                        rfl

theorem cell23_7176784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 2, 7, 2].length) (baseStart_7176784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7176784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7176784 prefixEnd_7176784 := by exact prefixLift 7176784
  have htrace : WordTrace (prefixWord ++ tailWord_7176784) baseStart_7176784 baseEnd_7176784 := by
    simpa [prefixWord, tailWord_7176784, baseEnd_7176784] using wordTrace_append hprefix tailTrace_7176784
  have hstable : (prefixWord ++ tailWord_7176784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7176784).length < 2 ^ (prefixWord ++ tailWord_7176784).sum := by decide
  have hdescent : baseEnd_7176784 < baseStart_7176784 := by decide
  rcases family_descends (prefixWord ++ tailWord_7176784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7176827 : List Nat := [1, 1, 1, 1, 1, 4, 2, 1, 2, 3, 6]
def baseStart_7176827 : Nat := 118140960795 + 7176827 * 2 ^ 59
def prefixEnd_7176827 : Nat := 4983230072969 + 3 ^ 40 * 7176827 * 2
def baseEnd_7176827 : Nat := 3685161825165297365056879

theorem tailTrace_7176827 : CollatzResearch.WordTrace tailWord_7176827 prefixEnd_7176827 3685161825165297365056879 := by
  unfold tailWord_7176827
  simp only [CollatzResearch.WordTrace]
  refine ⟨261760385170588958313392735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174506923447059305542261823 261760385170588958313392735)
  ·
    refine ⟨392640577755883437470089103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261760385170588958313392735 392640577755883437470089103)
    ·
      refine ⟨588960866633825156205133655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392640577755883437470089103 588960866633825156205133655)
      ·
        refine ⟨883441299950737734307700483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 588960866633825156205133655 883441299950737734307700483)
        ·
          refine ⟨1325161949926106601461550725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 883441299950737734307700483 1325161949926106601461550725)
          ·
            refine ⟨248467865611144987774040761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1325161949926106601461550725 248467865611144987774040761)
            ·
              refine ⟨186350899208358740830530571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 248467865611144987774040761 186350899208358740830530571)
              ·
                refine ⟨279526348812538111245795857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 186350899208358740830530571 279526348812538111245795857)
                ·
                  refine ⟨209644761609403583434346893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 279526348812538111245795857 209644761609403583434346893)
                  ·
                    refine ⟨78616785603526343787880085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 209644761609403583434346893 78616785603526343787880085)
                    ·
                      refine ⟨3685161825165297365056879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78616785603526343787880085 3685161825165297365056879)
                      ·
                        rfl

theorem cell23_7176827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 3, 6].length) (baseStart_7176827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7176827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7176827 prefixEnd_7176827 := by exact prefixLift 7176827
  have htrace : WordTrace (prefixWord ++ tailWord_7176827) baseStart_7176827 baseEnd_7176827 := by
    simpa [prefixWord, tailWord_7176827, baseEnd_7176827] using wordTrace_append hprefix tailTrace_7176827
  have hstable : (prefixWord ++ tailWord_7176827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7176827).length < 2 ^ (prefixWord ++ tailWord_7176827).sum := by decide
  have hdescent : baseEnd_7176827 < baseStart_7176827 := by decide
  rcases family_descends (prefixWord ++ tailWord_7176827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7176842 : List Nat := [3, 1, 2, 3, 3, 2, 2, 1, 2, 1, 3]
def baseStart_7176842 : Nat := 118140960795 + 7176842 * 2 ^ 59
def prefixEnd_7176842 : Nat := 4983230072969 + 3 ^ 40 * 7176842 * 2
def baseEnd_7176842 : Nat := 3685169527375114806369311

theorem tailTrace_7176842 : CollatzResearch.WordTrace tailWord_7176842 prefixEnd_7176842 3685169527375114806369311 := by
  unfold tailWord_7176842
  simp only [CollatzResearch.WordTrace]
  refine ⟨65440233066383653968797195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174507288177023077250125853 65440233066383653968797195)
  ·
    refine ⟨98160349599575480953195793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65440233066383653968797195 98160349599575480953195793)
    ·
      refine ⟨73620262199681610714896845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98160349599575480953195793 73620262199681610714896845)
      ·
        refine ⟨27607598324880604018086317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73620262199681610714896845 27607598324880604018086317)
        ·
          refine ⟨10352849371830226506782369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27607598324880604018086317 10352849371830226506782369)
          ·
            refine ⟨7764637028872669880086777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10352849371830226506782369 7764637028872669880086777)
            ·
              refine ⟨5823477771654502410065083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7764637028872669880086777 5823477771654502410065083)
              ·
                refine ⟨8735216657481753615097625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5823477771654502410065083 8735216657481753615097625)
                ·
                  refine ⟨6551412493111315211323219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8735216657481753615097625 6551412493111315211323219)
                  ·
                    refine ⟨9827118739666972816984829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6551412493111315211323219 9827118739666972816984829)
                    ·
                      refine ⟨3685169527375114806369311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9827118739666972816984829 3685169527375114806369311)
                      ·
                        rfl

theorem cell23_7176842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 2, 1, 2, 1, 3].length) (baseStart_7176842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7176842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7176842 prefixEnd_7176842 := by exact prefixLift 7176842
  have htrace : WordTrace (prefixWord ++ tailWord_7176842) baseStart_7176842 baseEnd_7176842 := by
    simpa [prefixWord, tailWord_7176842, baseEnd_7176842] using wordTrace_append hprefix tailTrace_7176842
  have hstable : (prefixWord ++ tailWord_7176842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7176842).length < 2 ^ (prefixWord ++ tailWord_7176842).sum := by decide
  have hdescent : baseEnd_7176842 < baseStart_7176842 := by decide
  rcases family_descends (prefixWord ++ tailWord_7176842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7176847 : List Nat := [1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 9]
def baseStart_7176847 : Nat := 118140960795 + 7176847 * 2 ^ 59
def prefixEnd_7176847 : Nat := 4983230072969 + 3 ^ 40 * 7176847 * 2
def baseEnd_7176847 : Nat := 3685172094778387286806787

theorem tailTrace_7176847 : CollatzResearch.WordTrace tailWord_7176847 prefixEnd_7176847 3685172094778387286806787 := by
  unfold tailWord_7176847
  simp only [CollatzResearch.WordTrace]
  refine ⟨261761114630516501729120795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174507409753677667819413863 261761114630516501729120795)
  ·
    refine ⟨392641671945774752593681193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261761114630516501729120795 392641671945774752593681193)
    ·
      refine ⟨294481253959331064445260895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 392641671945774752593681193 294481253959331064445260895)
      ·
        refine ⟨441721880938996596667891343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294481253959331064445260895 441721880938996596667891343)
        ·
          refine ⟨662582821408494895001837015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 441721880938996596667891343 662582821408494895001837015)
          ·
            refine ⟨993874232112742342502755523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 662582821408494895001837015 993874232112742342502755523)
            ·
              refine ⟨1490811348169113513754133285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 993874232112742342502755523 1490811348169113513754133285)
              ·
                refine ⟨279527127781708783828899991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1490811348169113513754133285 279527127781708783828899991)
                ·
                  refine ⟨419290691672563175743349987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 279527127781708783828899991 419290691672563175743349987)
                  ·
                    refine ⟨628936037508844763615024981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 419290691672563175743349987 628936037508844763615024981)
                    ·
                      refine ⟨3685172094778387286806787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 628936037508844763615024981 3685172094778387286806787)
                      ·
                        rfl

theorem cell23_7176847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 9].length) (baseStart_7176847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7176847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7176847 prefixEnd_7176847 := by exact prefixLift 7176847
  have htrace : WordTrace (prefixWord ++ tailWord_7176847) baseStart_7176847 baseEnd_7176847 := by
    simpa [prefixWord, tailWord_7176847, baseEnd_7176847] using wordTrace_append hprefix tailTrace_7176847
  have hstable : (prefixWord ++ tailWord_7176847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7176847).length < 2 ^ (prefixWord ++ tailWord_7176847).sum := by decide
  have hdescent : baseEnd_7176847 < baseStart_7176847 := by decide
  rcases family_descends (prefixWord ++ tailWord_7176847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7176852 : List Nat := [2, 4, 2, 2, 1, 3, 1, 2, 1, 3, 2]
def baseStart_7176852 : Nat := 118140960795 + 7176852 * 2 ^ 59
def prefixEnd_7176852 : Nat := 4983230072969 + 3 ^ 40 * 7176852 * 2
def baseEnd_7176852 : Nat := 3685174662181659767244265

theorem tailTrace_7176852 : CollatzResearch.WordTrace tailWord_7176852 prefixEnd_7176852 3685174662181659767244265 := by
  unfold tailWord_7176852
  simp only [CollatzResearch.WordTrace]
  refine ⟨130880648497749193791526405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174507531330332258388701873 130880648497749193791526405)
  ·
    refine ⟨24540121593327973835911201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130880648497749193791526405 24540121593327973835911201)
    ·
      refine ⟨18405091194995980376933401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24540121593327973835911201 18405091194995980376933401)
      ·
        refine ⟨13803818396246985282700051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18405091194995980376933401 13803818396246985282700051)
        ·
          refine ⟨20705727594370477924050077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13803818396246985282700051 20705727594370477924050077)
          ·
            refine ⟨7764647847888929221518779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20705727594370477924050077 7764647847888929221518779)
            ·
              refine ⟨11646971771833393832278169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7764647847888929221518779 11646971771833393832278169)
              ·
                refine ⟨8735228828875045374208627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11646971771833393832278169 8735228828875045374208627)
                ·
                  refine ⟨13102843243312568061312941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8735228828875045374208627 13102843243312568061312941)
                  ·
                    refine ⟨4913566216242213022992353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13102843243312568061312941 4913566216242213022992353)
                    ·
                      refine ⟨3685174662181659767244265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4913566216242213022992353 3685174662181659767244265)
                      ·
                        rfl

theorem cell23_7176852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_7176852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7176852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7176852 prefixEnd_7176852 := by exact prefixLift 7176852
  have htrace : WordTrace (prefixWord ++ tailWord_7176852) baseStart_7176852 baseEnd_7176852 := by
    simpa [prefixWord, tailWord_7176852, baseEnd_7176852] using wordTrace_append hprefix tailTrace_7176852
  have hstable : (prefixWord ++ tailWord_7176852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7176852).length < 2 ^ (prefixWord ++ tailWord_7176852).sum := by decide
  have hdescent : baseEnd_7176852 < baseStart_7176852 := by decide
  rcases family_descends (prefixWord ++ tailWord_7176852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7176921 : List Nat := [1, 2, 1, 2, 3, 2, 1, 2, 1, 6, 2]
def baseStart_7176921 : Nat := 118140960795 + 7176921 * 2 ^ 59
def prefixEnd_7176921 : Nat := 4983230072969 + 3 ^ 40 * 7176921 * 2
def baseEnd_7176921 : Nat := 3685210092346819997281447

theorem tailTrace_7176921 : CollatzResearch.WordTrace tailWord_7176921 prefixEnd_7176921 3685210092346819997281447 := by
  unfold tailWord_7176921
  simp only [CollatzResearch.WordTrace]
  refine ⟨261763813632248412367314617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174509209088165608244876411 261763813632248412367314617)
  ·
    refine ⟨196322860224186309275485963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261763813632248412367314617 196322860224186309275485963)
    ·
      refine ⟨294484290336279463913228945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196322860224186309275485963 294484290336279463913228945)
      ·
        refine ⟨220863217752209597934921709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 294484290336279463913228945 220863217752209597934921709)
        ·
          refine ⟨82823706657078599225595641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 220863217752209597934921709 82823706657078599225595641)
          ·
            refine ⟨62117779992808949419196731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82823706657078599225595641 62117779992808949419196731)
            ·
              refine ⟨93176669989213424128795097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62117779992808949419196731 93176669989213424128795097)
              ·
                refine ⟨69882502491910068096596323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93176669989213424128795097 69882502491910068096596323)
                ·
                  refine ⟨104823753737865102144894485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69882502491910068096596323 104823753737865102144894485)
                  ·
                    refine ⟨4913613456462426663041929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 104823753737865102144894485 4913613456462426663041929)
                    ·
                      refine ⟨3685210092346819997281447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4913613456462426663041929 3685210092346819997281447)
                      ·
                        rfl

theorem cell23_7176921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 6, 2].length) (baseStart_7176921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7176921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7176921 prefixEnd_7176921 := by exact prefixLift 7176921
  have htrace : WordTrace (prefixWord ++ tailWord_7176921) baseStart_7176921 baseEnd_7176921 := by
    simpa [prefixWord, tailWord_7176921, baseEnd_7176921] using wordTrace_append hprefix tailTrace_7176921
  have hstable : (prefixWord ++ tailWord_7176921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7176921).length < 2 ^ (prefixWord ++ tailWord_7176921).sum := by decide
  have hdescent : baseEnd_7176921 < baseStart_7176921 := by decide
  rcases family_descends (prefixWord ++ tailWord_7176921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7176944 : List Nat := [2, 1, 1, 1, 3, 1, 5, 1, 8]
def baseStart_7176944 : Nat := 118140960795 + 7176944 * 2 ^ 59
def prefixEnd_7176944 : Nat := 4983230072969 + 3 ^ 40 * 7176944 * 2
def baseEnd_7176944 : Nat := 409469100266874823032649

theorem tailTrace_7176944 : CollatzResearch.WordTrace tailWord_7176944 prefixEnd_7176944 409469100266874823032649 := by
  unfold tailWord_7176944
  simp only [CollatzResearch.WordTrace]
  refine ⟨130882326255582543647700943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174509768340776724863601257 130882326255582543647700943)
  ·
    refine ⟨196323489383373815471551415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130882326255582543647700943 196323489383373815471551415)
    ·
      refine ⟨294485234075060723207327123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196323489383373815471551415 294485234075060723207327123)
      ·
        refine ⟨441727851112591084810990685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294485234075060723207327123 441727851112591084810990685)
        ·
          refine ⟨165647944167221656804121507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 441727851112591084810990685 165647944167221656804121507)
          ·
            refine ⟨248471916250832485206182261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165647944167221656804121507 248471916250832485206182261)
            ·
              refine ⟨23294242148515545488079587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 248471916250832485206182261 23294242148515545488079587)
              ·
                refine ⟨34941363222773318232119381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23294242148515545488079587 34941363222773318232119381)
                ·
                  refine ⟨409469100266874823032649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34941363222773318232119381 409469100266874823032649)
                  ·
                    rfl

theorem cell23_7176944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 1, 8].length) (baseStart_7176944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7176944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7176944 prefixEnd_7176944 := by exact prefixLift 7176944
  have htrace : WordTrace (prefixWord ++ tailWord_7176944) baseStart_7176944 baseEnd_7176944 := by
    simpa [prefixWord, tailWord_7176944, baseEnd_7176944] using wordTrace_append hprefix tailTrace_7176944
  have hstable : (prefixWord ++ tailWord_7176944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7176944).length < 2 ^ (prefixWord ++ tailWord_7176944).sum := by decide
  have hdescent : baseEnd_7176944 < baseStart_7176944 := by decide
  rcases family_descends (prefixWord ++ tailWord_7176944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7176958 : List Nat := [4, 2, 2, 1, 2, 1, 1, 2, 1, 4, 3]
def baseStart_7176958 : Nat := 118140960795 + 7176958 * 2 ^ 59
def prefixEnd_7176958 : Nat := 4983230072969 + 3 ^ 40 * 7176958 * 2
def baseEnd_7176958 : Nat := 3685229091131036352518777

theorem tailTrace_7176958 : CollatzResearch.WordTrace tailWord_7176958 prefixEnd_7176958 3685229091131036352518777 := by
  unfold tailWord_7176958
  simp only [CollatzResearch.WordTrace]
  refine ⟨32720645391639295960801441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174510108755409578457607685 32720645391639295960801441)
  ·
    refine ⟨24540484043729471970601081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32720645391639295960801441 24540484043729471970601081)
    ·
      refine ⟨18405363032797103977950811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24540484043729471970601081 18405363032797103977950811)
      ·
        refine ⟨27608044549195655966926217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18405363032797103977950811 27608044549195655966926217)
        ·
          refine ⟨20706033411896741975194663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27608044549195655966926217 20706033411896741975194663)
          ·
            refine ⟨31059050117845112962791995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20706033411896741975194663 31059050117845112962791995)
            ·
              refine ⟨46588575176767669444187993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31059050117845112962791995 46588575176767669444187993)
              ·
                refine ⟨34941431382575752083140995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46588575176767669444187993 34941431382575752083140995)
                ·
                  refine ⟨52412147073863628124711493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34941431382575752083140995 52412147073863628124711493)
                  ·
                    refine ⟨9827277576349430273383405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52412147073863628124711493 9827277576349430273383405)
                    ·
                      refine ⟨3685229091131036352518777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9827277576349430273383405 3685229091131036352518777)
                      ·
                        rfl

theorem cell23_7176958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_7176958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7176958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7176958 prefixEnd_7176958 := by exact prefixLift 7176958
  have htrace : WordTrace (prefixWord ++ tailWord_7176958) baseStart_7176958 baseEnd_7176958 := by
    simpa [prefixWord, tailWord_7176958, baseEnd_7176958] using wordTrace_append hprefix tailTrace_7176958
  have hstable : (prefixWord ++ tailWord_7176958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7176958).length < 2 ^ (prefixWord ++ tailWord_7176958).sum := by decide
  have hdescent : baseEnd_7176958 < baseStart_7176958 := by decide
  rcases family_descends (prefixWord ++ tailWord_7176958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7177012 : List Nat := [2, 5, 1, 1, 3, 2, 2, 1, 6]
def baseStart_7177012 : Nat := 118140960795 + 7177012 * 2 ^ 59
def prefixEnd_7177012 : Nat := 4983230072969 + 3 ^ 40 * 7177012 * 2
def baseEnd_7177012 : Nat := 409472979898486571249281

theorem tailTrace_7177012 : CollatzResearch.WordTrace tailWord_7177012 prefixEnd_7177012 409472979898486571249281 := by
  unfold tailWord_7177012
  simp only [CollatzResearch.WordTrace]
  refine ⟨130883566337459367454438645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174511421783279156605918193 130883566337459367454438645)
  ·
    refine ⟨12270334344136815698853623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 130883566337459367454438645 12270334344136815698853623)
    ·
      refine ⟨18405501516205223548280435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12270334344136815698853623 18405501516205223548280435)
      ·
        refine ⟨27608252274307835322420653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18405501516205223548280435 27608252274307835322420653)
        ·
          refine ⟨10353094602865438245907745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27608252274307835322420653 10353094602865438245907745)
          ·
            refine ⟨7764820952149078684430809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10353094602865438245907745 7764820952149078684430809)
            ·
              refine ⟨5823615714111809013323107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7764820952149078684430809 5823615714111809013323107)
              ·
                refine ⟨8735423571167713519984661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5823615714111809013323107 8735423571167713519984661)
                ·
                  refine ⟨409472979898486571249281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8735423571167713519984661 409472979898486571249281)
                  ·
                    rfl

theorem cell23_7177012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 2, 1, 6].length) (baseStart_7177012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7177012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7177012 prefixEnd_7177012 := by exact prefixLift 7177012
  have htrace : WordTrace (prefixWord ++ tailWord_7177012) baseStart_7177012 baseEnd_7177012 := by
    simpa [prefixWord, tailWord_7177012, baseEnd_7177012] using wordTrace_append hprefix tailTrace_7177012
  have hstable : (prefixWord ++ tailWord_7177012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7177012).length < 2 ^ (prefixWord ++ tailWord_7177012).sum := by decide
  have hdescent : baseEnd_7177012 < baseStart_7177012 := by decide
  rcases family_descends (prefixWord ++ tailWord_7177012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7177025 : List Nat := [1, 2, 5, 3, 1, 1, 1, 1, 3, 5]
def baseStart_7177025 : Nat := 118140960795 + 7177025 * 2 ^ 59
def prefixEnd_7177025 : Nat := 4983230072969 + 3 ^ 40 * 7177025 * 2
def baseEnd_7177025 : Nat := 1228421164778295863460323

theorem tailTrace_7177025 : CollatzResearch.WordTrace tailWord_7177025 prefixEnd_7177025 1228421164778295863460323 := by
  unfold tailWord_7177025
  simp only [CollatzResearch.WordTrace]
  refine ⟨261767606823871638129100529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174511737882581092086067019 261767606823871638129100529)
  ·
    refine ⟨196325705117903728596825397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261767606823871638129100529 196325705117903728596825397)
    ·
      refine ⟨18405534854803474555952381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 196325705117903728596825397 18405534854803474555952381)
      ·
        refine ⟨6902075570551302958482143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18405534854803474555952381 6902075570551302958482143)
        ·
          refine ⟨10353113355826954437723215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6902075570551302958482143 10353113355826954437723215)
          ·
            refine ⟨15529670033740431656584823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10353113355826954437723215 15529670033740431656584823)
            ·
              refine ⟨23294505050610647484877235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15529670033740431656584823 23294505050610647484877235)
              ·
                refine ⟨34941757575915971227315853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23294505050610647484877235 34941757575915971227315853)
                ·
                  refine ⟨13103159090968489210243445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34941757575915971227315853 13103159090968489210243445)
                  ·
                    refine ⟨1228421164778295863460323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13103159090968489210243445 1228421164778295863460323)
                    ·
                      rfl

theorem cell23_7177025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_7177025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7177025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7177025 prefixEnd_7177025 := by exact prefixLift 7177025
  have htrace : WordTrace (prefixWord ++ tailWord_7177025) baseStart_7177025 baseEnd_7177025 := by
    simpa [prefixWord, tailWord_7177025, baseEnd_7177025] using wordTrace_append hprefix tailTrace_7177025
  have hstable : (prefixWord ++ tailWord_7177025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7177025).length < 2 ^ (prefixWord ++ tailWord_7177025).sum := by decide
  have hdescent : baseEnd_7177025 < baseStart_7177025 := by decide
  rcases family_descends (prefixWord ++ tailWord_7177025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7177045 : List Nat := [1, 3, 2, 2, 2, 1, 5, 1, 1, 1, 4]
def baseStart_7177045 : Nat := 118140960795 + 7177045 * 2 ^ 59
def prefixEnd_7177045 : Nat := 4983230072969 + 3 ^ 40 * 7177045 * 2
def baseEnd_7177045 : Nat := 3685273763947977512130877

theorem tailTrace_7177045 : CollatzResearch.WordTrace tailWord_7177045 prefixEnd_7177045 3685273763947977512130877 := by
  unfold tailWord_7177045
  simp only [CollatzResearch.WordTrace]
  refine ⟨261768336283799181544828589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174512224189199454363219059 261768336283799181544828589)
  ·
    refine ⟨98163126106424693079310721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261768336283799181544828589 98163126106424693079310721)
    ·
      refine ⟨73622344579818519809483041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98163126106424693079310721 73622344579818519809483041)
      ·
        refine ⟨55216758434863889857112281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73622344579818519809483041 55216758434863889857112281)
        ·
          refine ⟨41412568826147917392834211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55216758434863889857112281 41412568826147917392834211)
          ·
            refine ⟨62118853239221876089251317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41412568826147917392834211 62118853239221876089251317)
            ·
              refine ⟨5823642491177050883367311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62118853239221876089251317 5823642491177050883367311)
              ·
                refine ⟨8735463736765576325050967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5823642491177050883367311 8735463736765576325050967)
                ·
                  refine ⟨13103195605148364487576451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8735463736765576325050967 13103195605148364487576451)
                  ·
                    refine ⟨19654793407722546731364677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13103195605148364487576451 19654793407722546731364677)
                    ·
                      refine ⟨3685273763947977512130877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19654793407722546731364677 3685273763947977512130877)
                      ·
                        rfl

theorem cell23_7177045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 5, 1, 1, 1, 4].length) (baseStart_7177045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7177045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7177045 prefixEnd_7177045 := by exact prefixLift 7177045
  have htrace : WordTrace (prefixWord ++ tailWord_7177045) baseStart_7177045 baseEnd_7177045 := by
    simpa [prefixWord, tailWord_7177045, baseEnd_7177045] using wordTrace_append hprefix tailTrace_7177045
  have hstable : (prefixWord ++ tailWord_7177045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7177045).length < 2 ^ (prefixWord ++ tailWord_7177045).sum := by decide
  have hdescent : baseEnd_7177045 < baseStart_7177045 := by decide
  rcases family_descends (prefixWord ++ tailWord_7177045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7177048 : List Nat := [2, 1, 2, 2, 1, 1, 1, 7, 1, 2, 3]
def baseStart_7177048 : Nat := 118140960795 + 7177048 * 2 ^ 59
def prefixEnd_7177048 : Nat := 4983230072969 + 3 ^ 40 * 7177048 * 2
def baseEnd_7177048 : Nat := 3685275304389941000393363

theorem tailTrace_7177048 : CollatzResearch.WordTrace tailWord_7177048 prefixEnd_7177048 3685275304389941000393363 := by
  unfold tailWord_7177048
  simp only [CollatzResearch.WordTrace]
  refine ⟨130884222851394156528593899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174512297135192208704791865 130884222851394156528593899)
  ·
    refine ⟨196326334277091234792890849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130884222851394156528593899 196326334277091234792890849)
    ·
      refine ⟨147244750707818426094668137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196326334277091234792890849 147244750707818426094668137)
      ·
        refine ⟨110433563030863819571001103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147244750707818426094668137 110433563030863819571001103)
        ·
          refine ⟨165650344546295729356501655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110433563030863819571001103 165650344546295729356501655)
          ·
            refine ⟨248475516819443594034752483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165650344546295729356501655 248475516819443594034752483)
            ·
              refine ⟨372713275229165391052128725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248475516819443594034752483 372713275229165391052128725)
              ·
                refine ⟨8735467388183563852784267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 372713275229165391052128725 8735467388183563852784267)
                ·
                  refine ⟨13103201082275345779176401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8735467388183563852784267 13103201082275345779176401)
                  ·
                    refine ⟨9827400811706509334382301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13103201082275345779176401 9827400811706509334382301)
                    ·
                      refine ⟨3685275304389941000393363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9827400811706509334382301 3685275304389941000393363)
                      ·
                        rfl

theorem cell23_7177048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 7, 1, 2, 3].length) (baseStart_7177048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7177048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7177048 prefixEnd_7177048 := by exact prefixLift 7177048
  have htrace : WordTrace (prefixWord ++ tailWord_7177048) baseStart_7177048 baseEnd_7177048 := by
    simpa [prefixWord, tailWord_7177048, baseEnd_7177048] using wordTrace_append hprefix tailTrace_7177048
  have hstable : (prefixWord ++ tailWord_7177048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7177048).length < 2 ^ (prefixWord ++ tailWord_7177048).sum := by decide
  have hdescent : baseEnd_7177048 < baseStart_7177048 := by decide
  rcases family_descends (prefixWord ++ tailWord_7177048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7177091 : List Nat := [1, 1, 1, 3, 4, 1, 2, 1, 2, 2, 5]
def baseStart_7177091 : Nat := 118140960795 + 7177091 * 2 ^ 59
def prefixEnd_7177091 : Nat := 4983230072969 + 3 ^ 40 * 7177091 * 2
def baseEnd_7177091 : Nat := 3685297384058084332155665

theorem tailTrace_7177091 : CollatzResearch.WordTrace tailWord_7177091 prefixEnd_7177091 3685297384058084332155665 := by
  unfold tailWord_7177091
  simp only [CollatzResearch.WordTrace]
  refine ⟨261770014041632531401003127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174513342694421687600668751 261770014041632531401003127)
  ·
    refine ⟨392655021062448797101504691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261770014041632531401003127 392655021062448797101504691)
    ·
      refine ⟨588982531593673195652257037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392655021062448797101504691 588982531593673195652257037)
      ·
        refine ⟨220868449347627448369596389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 588982531593673195652257037 220868449347627448369596389)
        ·
          refine ⟨41412834252680146569299323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 220868449347627448369596389 41412834252680146569299323)
          ·
            refine ⟨62119251379020219853948985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41412834252680146569299323 62119251379020219853948985)
            ·
              refine ⟨46589438534265164890461739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62119251379020219853948985 46589438534265164890461739)
              ·
                refine ⟨69884157801397747335692609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46589438534265164890461739 69884157801397747335692609)
                ·
                  refine ⟨52413118351048310501769457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69884157801397747335692609 52413118351048310501769457)
                  ·
                    refine ⟨39309838763286232876327093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52413118351048310501769457 39309838763286232876327093)
                    ·
                      refine ⟨3685297384058084332155665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39309838763286232876327093 3685297384058084332155665)
                      ·
                        rfl

theorem cell23_7177091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 2, 2, 5].length) (baseStart_7177091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7177091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7177091 prefixEnd_7177091 := by exact prefixLift 7177091
  have htrace : WordTrace (prefixWord ++ tailWord_7177091) baseStart_7177091 baseEnd_7177091 := by
    simpa [prefixWord, tailWord_7177091, baseEnd_7177091] using wordTrace_append hprefix tailTrace_7177091
  have hstable : (prefixWord ++ tailWord_7177091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7177091).length < 2 ^ (prefixWord ++ tailWord_7177091).sum := by decide
  have hdescent : baseEnd_7177091 < baseStart_7177091 := by decide
  rcases family_descends (prefixWord ++ tailWord_7177091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7177111 : List Nat := [1, 1, 3, 3, 1, 2, 1, 1, 4, 6]
def baseStart_7177111 : Nat := 118140960795 + 7177111 * 2 ^ 59
def prefixEnd_7177111 : Nat := 4983230072969 + 3 ^ 40 * 7177111 * 2
def baseEnd_7177111 : Nat := 1228435884557058084635191

theorem tailTrace_7177111 : CollatzResearch.WordTrace tailWord_7177111 prefixEnd_7177111 1228435884557058084635191 := by
  unfold tailWord_7177111
  simp only [CollatzResearch.WordTrace]
  refine ⟨261770743501560074816731187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174513829001040049877820791 261770743501560074816731187)
  ·
    refine ⟨392656115252340112225096781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261770743501560074816731187 392656115252340112225096781)
    ·
      refine ⟨147246043219627542084411293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 392656115252340112225096781 147246043219627542084411293)
      ·
        refine ⟨55217266207360328281654235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147246043219627542084411293 55217266207360328281654235)
        ·
          refine ⟨82825899311040492422481353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55217266207360328281654235 82825899311040492422481353)
          ·
            refine ⟨62119424483280369316861015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82825899311040492422481353 62119424483280369316861015)
            ·
              refine ⟨93179136724920553975291523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62119424483280369316861015 93179136724920553975291523)
              ·
                refine ⟨139768705087380830962937285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93179136724920553975291523 139768705087380830962937285)
                ·
                  refine ⟨26206632203883905805550741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 139768705087380830962937285 26206632203883905805550741)
                  ·
                    refine ⟨1228435884557058084635191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26206632203883905805550741 1228435884557058084635191)
                    ·
                      rfl

theorem cell23_7177111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 4, 6].length) (baseStart_7177111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7177111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7177111 prefixEnd_7177111 := by exact prefixLift 7177111
  have htrace : WordTrace (prefixWord ++ tailWord_7177111) baseStart_7177111 baseEnd_7177111 := by
    simpa [prefixWord, tailWord_7177111, baseEnd_7177111] using wordTrace_append hprefix tailTrace_7177111
  have hstable : (prefixWord ++ tailWord_7177111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7177111).length < 2 ^ (prefixWord ++ tailWord_7177111).sum := by decide
  have hdescent : baseEnd_7177111 < baseStart_7177111 := by decide
  rcases family_descends (prefixWord ++ tailWord_7177111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7177186 : List Nat := [3, 3, 3, 1, 1, 2, 1, 3, 2, 2, 2]
def baseStart_7177186 : Nat := 118140960795 + 7177186 * 2 ^ 59
def prefixEnd_7177186 : Nat := 4983230072969 + 3 ^ 40 * 7177186 * 2
def baseEnd_7177186 : Nat := 3685346164720261460467729

theorem tailTrace_7177186 : CollatzResearch.WordTrace tailWord_7177186 prefixEnd_7177186 3685346164720261460467729 := by
  unfold tailWord_7177186
  simp only [CollatzResearch.WordTrace]
  refine ⟨65443369744072090656427853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174515652650858908417140941 65443369744072090656427853)
  ·
    refine ⟨24541263654027033996160445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65443369744072090656427853 24541263654027033996160445)
    ·
      refine ⟨9202973870260137748560167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24541263654027033996160445 9202973870260137748560167)
      ·
        refine ⟨13804460805390206622840251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9202973870260137748560167 13804460805390206622840251)
        ·
          refine ⟨20706691208085309934260377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13804460805390206622840251 20706691208085309934260377)
          ·
            refine ⟨15530018406063982450695283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20706691208085309934260377 15530018406063982450695283)
            ·
              refine ⟨23295027609095973676042925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15530018406063982450695283 23295027609095973676042925)
              ·
                refine ⟨8735635353410990128516097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23295027609095973676042925 8735635353410990128516097)
                ·
                  refine ⟨6551726515058242596387073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8735635353410990128516097 6551726515058242596387073)
                  ·
                    refine ⟨4913794886293681947290305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6551726515058242596387073 4913794886293681947290305)
                    ·
                      refine ⟨3685346164720261460467729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4913794886293681947290305 3685346164720261460467729)
                      ·
                        rfl

theorem cell23_7177186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_7177186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7177186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7177186 prefixEnd_7177186 := by exact prefixLift 7177186
  have htrace : WordTrace (prefixWord ++ tailWord_7177186) baseStart_7177186 baseEnd_7177186 := by
    simpa [prefixWord, tailWord_7177186, baseEnd_7177186] using wordTrace_append hprefix tailTrace_7177186
  have hstable : (prefixWord ++ tailWord_7177186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7177186).length < 2 ^ (prefixWord ++ tailWord_7177186).sum := by decide
  have hdescent : baseEnd_7177186 < baseStart_7177186 := by decide
  rcases family_descends (prefixWord ++ tailWord_7177186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7177252 : List Nat := [2, 3, 1, 4, 1, 2, 1, 2, 3, 4]
def baseStart_7177252 : Nat := 118140960795 + 7177252 * 2 ^ 59
def prefixEnd_7177252 : Nat := 4983230072969 + 3 ^ 40 * 7177252 * 2
def baseEnd_7177252 : Nat := 1228460018147819400747475

theorem tailTrace_7177252 : CollatzResearch.WordTrace tailWord_7177252 prefixEnd_7177252 1228460018147819400747475 := by
  unfold tailWord_7177252
  simp only [CollatzResearch.WordTrace]
  refine ⟨130887943097024627948807005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174517257462699503931742673 130887943097024627948807005)
  ·
    refine ⟨49082978661384235480802627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130887943097024627948807005 49082978661384235480802627)
    ·
      refine ⟨73624467992076353221203941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49082978661384235480802627 73624467992076353221203941)
      ·
        refine ⟨13804587748514316228975739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73624467992076353221203941 13804587748514316228975739)
        ·
          refine ⟨20706881622771474343463609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13804587748514316228975739 20706881622771474343463609)
          ·
            refine ⟨15530161217078605757597707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20706881622771474343463609 15530161217078605757597707)
            ·
              refine ⟨23295241825617908636396561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15530161217078605757597707 23295241825617908636396561)
              ·
                refine ⟨17471431369213431477297421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23295241825617908636396561 17471431369213431477297421)
                ·
                  refine ⟨6551786763455036803986533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17471431369213431477297421 6551786763455036803986533)
                  ·
                    refine ⟨1228460018147819400747475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6551786763455036803986533 1228460018147819400747475)
                    ·
                      rfl

theorem cell23_7177252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 2, 3, 4].length) (baseStart_7177252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7177252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7177252 prefixEnd_7177252 := by exact prefixLift 7177252
  have htrace : WordTrace (prefixWord ++ tailWord_7177252) baseStart_7177252 baseEnd_7177252 := by
    simpa [prefixWord, tailWord_7177252, baseEnd_7177252] using wordTrace_append hprefix tailTrace_7177252
  have hstable : (prefixWord ++ tailWord_7177252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7177252).length < 2 ^ (prefixWord ++ tailWord_7177252).sum := by decide
  have hdescent : baseEnd_7177252 < baseStart_7177252 := by decide
  rcases family_descends (prefixWord ++ tailWord_7177252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7177286 : List Nat := [6, 1, 1, 1, 1, 2, 2, 4, 1, 4]
def baseStart_7177286 : Nat := 118140960795 + 7177286 * 2 ^ 59
def prefixEnd_7177286 : Nat := 4983230072969 + 3 ^ 40 * 7177286 * 2
def baseEnd_7177286 : Nat := 1228465837595237023072423

theorem tailTrace_7177286 : CollatzResearch.WordTrace tailWord_7177286 prefixEnd_7177286 1228465837595237023072423 := by
  unfold tailWord_7177286
  simp only [CollatzResearch.WordTrace]
  refine ⟨8180535196122689990760991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 174518084183950719802901141 8180535196122689990760991)
  ·
    refine ⟨12270802794184034986141487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8180535196122689990760991 12270802794184034986141487)
    ·
      refine ⟨18406204191276052479212231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12270802794184034986141487 18406204191276052479212231)
      ·
        refine ⟨27609306286914078718818347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18406204191276052479212231 27609306286914078718818347)
        ·
          refine ⟨41413959430371118078227521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27609306286914078718818347 41413959430371118078227521)
          ·
            refine ⟨31060469572778338558670641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41413959430371118078227521 31060469572778338558670641)
            ·
              refine ⟨23295352179583753919002981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31060469572778338558670641 23295352179583753919002981)
              ·
                refine ⟨4367878533671953859813059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23295352179583753919002981 4367878533671953859813059)
                ·
                  refine ⟨6551817800507930789719589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4367878533671953859813059 6551817800507930789719589)
                  ·
                    refine ⟨1228465837595237023072423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6551817800507930789719589 1228465837595237023072423)
                    ·
                      rfl

theorem cell23_7177286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_7177286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7177286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7177286 prefixEnd_7177286 := by exact prefixLift 7177286
  have htrace : WordTrace (prefixWord ++ tailWord_7177286) baseStart_7177286 baseEnd_7177286 := by
    simpa [prefixWord, tailWord_7177286, baseEnd_7177286] using wordTrace_append hprefix tailTrace_7177286
  have hstable : (prefixWord ++ tailWord_7177286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7177286).length < 2 ^ (prefixWord ++ tailWord_7177286).sum := by decide
  have hdescent : baseEnd_7177286 < baseStart_7177286 := by decide
  rcases family_descends (prefixWord ++ tailWord_7177286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7177315 : List Nat := [1, 1, 1, 5, 1, 1, 1, 1, 1, 8, 2]
def baseStart_7177315 : Nat := 118140960795 + 7177315 * 2 ^ 59
def prefixEnd_7177315 : Nat := 4983230072969 + 3 ^ 40 * 7177315 * 2
def baseEnd_7177315 : Nat := 3685412403724691455754635

theorem tailTrace_7177315 : CollatzResearch.WordTrace tailWord_7177315 prefixEnd_7177315 3685412403724691455754635 := by
  unfold tailWord_7177315
  simp only [CollatzResearch.WordTrace]
  refine ⟨261778183992821017657157399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174518789328547345104771599 261778183992821017657157399)
  ·
    refine ⟨392667275989231526485736099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261778183992821017657157399 392667275989231526485736099)
    ·
      refine ⟨589000913983847289728604149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392667275989231526485736099 589000913983847289728604149)
      ·
        refine ⟨55218835685985683412056639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 589000913983847289728604149 55218835685985683412056639)
        ·
          refine ⟨82828253528978525118084959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55218835685985683412056639 82828253528978525118084959)
          ·
            refine ⟨124242380293467787677127439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82828253528978525118084959 124242380293467787677127439)
            ·
              refine ⟨186363570440201681515691159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124242380293467787677127439 186363570440201681515691159)
              ·
                refine ⟨279545355660302522273536739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 186363570440201681515691159 279545355660302522273536739)
                ·
                  refine ⟨419318033490453783410305109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 279545355660302522273536739 419318033490453783410305109)
                  ·
                    refine ⟨4913883204966255274339513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 419318033490453783410305109 4913883204966255274339513)
                    ·
                      refine ⟨3685412403724691455754635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4913883204966255274339513 3685412403724691455754635)
                      ·
                        rfl

theorem cell23_7177315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 8, 2].length) (baseStart_7177315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7177315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7177315 prefixEnd_7177315 := by exact prefixLift 7177315
  have htrace : WordTrace (prefixWord ++ tailWord_7177315) baseStart_7177315 baseEnd_7177315 := by
    simpa [prefixWord, tailWord_7177315, baseEnd_7177315] using wordTrace_append hprefix tailTrace_7177315
  have hstable : (prefixWord ++ tailWord_7177315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7177315).length < 2 ^ (prefixWord ++ tailWord_7177315).sum := by decide
  have hdescent : baseEnd_7177315 < baseStart_7177315 := by decide
  rcases family_descends (prefixWord ++ tailWord_7177315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7177326 : List Nat := [4, 1, 2, 2, 1, 2, 3, 3, 1, 1, 3]
def baseStart_7177326 : Nat := 118140960795 + 7177326 * 2 ^ 59
def prefixEnd_7177326 : Nat := 4983230072969 + 3 ^ 40 * 7177326 * 2
def baseEnd_7177326 : Nat := 3685418052011890912717085

theorem tailTrace_7177326 : CollatzResearch.WordTrace tailWord_7177326 prefixEnd_7177326 3685418052011890912717085 := by
  unfold tailWord_7177326
  simp only [CollatzResearch.WordTrace]
  refine ⟨32722323149472645816975979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174519056797187444357205221 32722323149472645816975979)
  ·
    refine ⟨49083484724208968725463969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32722323149472645816975979 49083484724208968725463969)
    ·
      refine ⟨36812613543156726544097977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49083484724208968725463969 36812613543156726544097977)
      ·
        refine ⟨27609460157367544908073483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36812613543156726544097977 27609460157367544908073483)
        ·
          refine ⟨41414190236051317362110225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27609460157367544908073483 41414190236051317362110225)
          ·
            refine ⟨31060642677038488021582669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41414190236051317362110225 31060642677038488021582669)
            ·
              refine ⟨11647741003889433008093501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31060642677038488021582669 11647741003889433008093501)
              ·
                refine ⟨4367902876458537378035063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11647741003889433008093501 4367902876458537378035063)
                ·
                  refine ⟨6551854314687806067052595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4367902876458537378035063 6551854314687806067052595)
                  ·
                    refine ⟨9827781472031709100578893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6551854314687806067052595 9827781472031709100578893)
                    ·
                      refine ⟨3685418052011890912717085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9827781472031709100578893 3685418052011890912717085)
                      ·
                        rfl

theorem cell23_7177326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 3, 1, 1, 3].length) (baseStart_7177326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7177326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7177326 prefixEnd_7177326 := by exact prefixLift 7177326
  have htrace : WordTrace (prefixWord ++ tailWord_7177326) baseStart_7177326 baseEnd_7177326 := by
    simpa [prefixWord, tailWord_7177326, baseEnd_7177326] using wordTrace_append hprefix tailTrace_7177326
  have hstable : (prefixWord ++ tailWord_7177326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7177326).length < 2 ^ (prefixWord ++ tailWord_7177326).sum := by decide
  have hdescent : baseEnd_7177326 < baseStart_7177326 := by decide
  rcases family_descends (prefixWord ++ tailWord_7177326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7177335 : List Nat := [1, 1, 3, 1, 1, 4, 4, 1, 1, 1, 5]
def baseStart_7177335 : Nat := 118140960795 + 7177335 * 2 ^ 59
def prefixEnd_7177335 : Nat := 4983230072969 + 3 ^ 40 * 7177335 * 2
def baseEnd_7177335 : Nat := 3685422673337781377504543

theorem tailTrace_7177335 : CollatzResearch.WordTrace tailWord_7177335 prefixEnd_7177335 3685422673337781377504543 := by
  unfold tailWord_7177335
  simp only [CollatzResearch.WordTrace]
  refine ⟨261778913452748561072885459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174519275635165707381923639 261778913452748561072885459)
  ·
    refine ⟨392668370179122841609328189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261778913452748561072885459 392668370179122841609328189)
    ·
      refine ⟨147250638817171065603498071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 392668370179122841609328189 147250638817171065603498071)
      ·
        refine ⟨220875958225756598405247107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147250638817171065603498071 220875958225756598405247107)
        ·
          refine ⟨331313937338634897607870661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220875958225756598405247107 331313937338634897607870661)
          ·
            refine ⟨62121363250994043301475749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 331313937338634897607870661 62121363250994043301475749)
            ·
              refine ⟨11647755609561383119026703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62121363250994043301475749 11647755609561383119026703)
              ·
                refine ⟨17471633414342074678540055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11647755609561383119026703 17471633414342074678540055)
                ·
                  refine ⟨26207450121513112017810083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17471633414342074678540055 26207450121513112017810083)
                  ·
                    refine ⟨39311175182269668026715125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26207450121513112017810083 39311175182269668026715125)
                    ·
                      refine ⟨3685422673337781377504543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39311175182269668026715125 3685422673337781377504543)
                      ·
                        rfl

theorem cell23_7177335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 1, 1, 1, 5].length) (baseStart_7177335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7177335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7177335 prefixEnd_7177335 := by exact prefixLift 7177335
  have htrace : WordTrace (prefixWord ++ tailWord_7177335) baseStart_7177335 baseEnd_7177335 := by
    simpa [prefixWord, tailWord_7177335, baseEnd_7177335] using wordTrace_append hprefix tailTrace_7177335
  have hstable : (prefixWord ++ tailWord_7177335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7177335).length < 2 ^ (prefixWord ++ tailWord_7177335).sum := by decide
  have hdescent : baseEnd_7177335 < baseStart_7177335 := by decide
  rcases family_descends (prefixWord ++ tailWord_7177335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7177345 : List Nat := [1, 2, 4, 2, 2, 1, 1, 2, 1, 1, 6]
def baseStart_7177345 : Nat := 118140960795 + 7177345 * 2 ^ 59
def prefixEnd_7177345 : Nat := 4983230072969 + 3 ^ 40 * 7177345 * 2
def baseEnd_7177345 : Nat := 3685427808144326338379497

theorem tailTrace_7177345 : CollatzResearch.WordTrace tailWord_7177345 prefixEnd_7177345 3685427808144326338379497 := by
  unfold tailWord_7177345
  simp only [CollatzResearch.WordTrace]
  refine ⟨261779278182712332780749489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174519518788474888520499659 261779278182712332780749489)
  ·
    refine ⟨196334458637034249585562117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261779278182712332780749489 196334458637034249585562117)
    ·
      refine ⟨36812710994443921797292897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 196334458637034249585562117 36812710994443921797292897)
      ·
        refine ⟨27609533245832941347969673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36812710994443921797292897 27609533245832941347969673)
        ·
          refine ⟨20707149934374706010977255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27609533245832941347969673 20707149934374706010977255)
          ·
            refine ⟨31060724901562059016465883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20707149934374706010977255 31060724901562059016465883)
            ·
              refine ⟨46591087352343088524698825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31060724901562059016465883 46591087352343088524698825)
              ·
                refine ⟨34943315514257316393524119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46591087352343088524698825 34943315514257316393524119)
                ·
                  refine ⟨52414973271385974590286179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34943315514257316393524119 52414973271385974590286179)
                  ·
                    refine ⟨78622459907078961885429269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52414973271385974590286179 78622459907078961885429269)
                    ·
                      refine ⟨3685427808144326338379497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78622459907078961885429269 3685427808144326338379497)
                      ·
                        rfl

theorem cell23_7177345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_7177345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7177345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7177345 prefixEnd_7177345 := by exact prefixLift 7177345
  have htrace : WordTrace (prefixWord ++ tailWord_7177345) baseStart_7177345 baseEnd_7177345 := by
    simpa [prefixWord, tailWord_7177345, baseEnd_7177345] using wordTrace_append hprefix tailTrace_7177345
  have hstable : (prefixWord ++ tailWord_7177345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7177345).length < 2 ^ (prefixWord ++ tailWord_7177345).sum := by decide
  have hdescent : baseEnd_7177345 < baseStart_7177345 := by decide
  rcases family_descends (prefixWord ++ tailWord_7177345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7177399 : List Nat := [1, 1, 3, 1, 4, 1, 4, 2, 2, 1, 3]
def baseStart_7177399 : Nat := 118140960795 + 7177399 * 2 ^ 59
def prefixEnd_7177399 : Nat := 4983230072969 + 3 ^ 40 * 7177399 * 2
def baseEnd_7177399 : Nat := 3685455536099669127104249

theorem tailTrace_7177399 : CollatzResearch.WordTrace tailWord_7177399 prefixEnd_7177399 3685455536099669127104249 := by
  unfold tailWord_7177399
  simp only [CollatzResearch.WordTrace]
  refine ⟨261781247724516700003215251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174520831816344466668810167 261781247724516700003215251)
  ·
    refine ⟨392671871586775050004822877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261781247724516700003215251 392671871586775050004822877)
    ·
      refine ⟨147251951845040643751808579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 392671871586775050004822877 147251951845040643751808579)
      ·
        refine ⟨220877927767560965627712869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147251951845040643751808579 220877927767560965627712869)
        ·
          refine ⟨41414611456417681055196163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 220877927767560965627712869 41414611456417681055196163)
          ·
            refine ⟨62121917184626521582794245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41414611456417681055196163 62121917184626521582794245)
            ·
              refine ⟨11647859472117472796773921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62121917184626521582794245 11647859472117472796773921)
              ·
                refine ⟨8735894604088104597580441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11647859472117472796773921 8735894604088104597580441)
                ·
                  refine ⟨6551920953066078448185331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8735894604088104597580441 6551920953066078448185331)
                  ·
                    refine ⟨9827881429599117672277997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6551920953066078448185331 9827881429599117672277997)
                    ·
                      refine ⟨3685455536099669127104249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9827881429599117672277997 3685455536099669127104249)
                      ·
                        rfl

theorem cell23_7177399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 2, 2, 1, 3].length) (baseStart_7177399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7177399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7177399 prefixEnd_7177399 := by exact prefixLift 7177399
  have htrace : WordTrace (prefixWord ++ tailWord_7177399) baseStart_7177399 baseEnd_7177399 := by
    simpa [prefixWord, tailWord_7177399, baseEnd_7177399] using wordTrace_append hprefix tailTrace_7177399
  have hstable : (prefixWord ++ tailWord_7177399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7177399).length < 2 ^ (prefixWord ++ tailWord_7177399).sum := by decide
  have hdescent : baseEnd_7177399 < baseStart_7177399 := by decide
  rcases family_descends (prefixWord ++ tailWord_7177399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7177405 : List Nat := [1, 4, 1, 2, 1, 1, 3, 1, 2, 3, 4]
def baseStart_7177405 : Nat := 118140960795 + 7177405 * 2 ^ 59
def prefixEnd_7177405 : Nat := 4983230072969 + 3 ^ 40 * 7177405 * 2
def baseEnd_7177405 : Nat := 3685458616983596103629221

theorem tailTrace_7177405 : CollatzResearch.WordTrace tailWord_7177405 prefixEnd_7177405 3685458616983596103629221 := by
  unfold tailWord_7177405
  simp only [CollatzResearch.WordTrace]
  refine ⟨261781466562494963027933669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174520977708329975351955779 261781466562494963027933669)
  ·
    refine ⟨49084024980467805567737563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 261781466562494963027933669 49084024980467805567737563)
    ·
      refine ⟨73626037470701708351606345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49084024980467805567737563 73626037470701708351606345)
      ·
        refine ⟨55219528103026281263704759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73626037470701708351606345 55219528103026281263704759)
        ·
          refine ⟨82829292154539421895557139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55219528103026281263704759 82829292154539421895557139)
          ·
            refine ⟨124243938231809132843335709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82829292154539421895557139 124243938231809132843335709)
            ·
              refine ⟨46591476836928424816250891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124243938231809132843335709 46591476836928424816250891)
              ·
                refine ⟨69887215255392637224376337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46591476836928424816250891 69887215255392637224376337)
                ·
                  refine ⟨52415411441544477918282253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69887215255392637224376337 52415411441544477918282253)
                  ·
                    refine ⟨19655779290579179219355845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52415411441544477918282253 19655779290579179219355845)
                    ·
                      refine ⟨3685458616983596103629221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19655779290579179219355845 3685458616983596103629221)
                      ·
                        rfl

theorem cell23_7177405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_7177405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7177405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7177405 prefixEnd_7177405 := by exact prefixLift 7177405
  have htrace : WordTrace (prefixWord ++ tailWord_7177405) baseStart_7177405 baseEnd_7177405 := by
    simpa [prefixWord, tailWord_7177405, baseEnd_7177405] using wordTrace_append hprefix tailTrace_7177405
  have hstable : (prefixWord ++ tailWord_7177405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7177405).length < 2 ^ (prefixWord ++ tailWord_7177405).sum := by decide
  have hdescent : baseEnd_7177405 < baseStart_7177405 := by decide
  rcases family_descends (prefixWord ++ tailWord_7177405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7177425 : List Nat := [1, 2, 2, 1, 2, 2, 1, 1, 4, 4, 3]
def baseStart_7177425 : Nat := 118140960795 + 7177425 * 2 ^ 59
def prefixEnd_7177425 : Nat := 4983230072969 + 3 ^ 40 * 7177425 * 2
def baseEnd_7177425 : Nat := 3685468886596686025379129

theorem tailTrace_7177425 : CollatzResearch.WordTrace tailWord_7177425 prefixEnd_7177425 3685468886596686025379129 := by
  unfold tailWord_7177425
  simp only [CollatzResearch.WordTrace]
  refine ⟨261782196022422506443661729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174521464014948337629107819 261782196022422506443661729)
  ·
    refine ⟨196336647016816879832746297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261782196022422506443661729 196336647016816879832746297)
    ·
      refine ⟨147252485262612659874559723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196336647016816879832746297 147252485262612659874559723)
      ·
        refine ⟨220878727893918989811839585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147252485262612659874559723 220878727893918989811839585)
        ·
          refine ⟨165659045920439242358879689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220878727893918989811839585 165659045920439242358879689)
          ·
            refine ⟨124244284440329431769159767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165659045920439242358879689 124244284440329431769159767)
            ·
              refine ⟨186366426660494147653739651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124244284440329431769159767 186366426660494147653739651)
              ·
                refine ⟨279549639990741221480609477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 186366426660494147653739651 279549639990741221480609477)
                ·
                  refine ⟨52415557498263979027614277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 279549639990741221480609477 52415557498263979027614277)
                  ·
                    refine ⟨9827917030924496067677677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52415557498263979027614277 9827917030924496067677677)
                    ·
                      refine ⟨3685468886596686025379129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9827917030924496067677677 3685468886596686025379129)
                      ·
                        rfl

theorem cell23_7177425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 4, 4, 3].length) (baseStart_7177425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7177425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7177425 prefixEnd_7177425 := by exact prefixLift 7177425
  have htrace : WordTrace (prefixWord ++ tailWord_7177425) baseStart_7177425 baseEnd_7177425 := by
    simpa [prefixWord, tailWord_7177425, baseEnd_7177425] using wordTrace_append hprefix tailTrace_7177425
  have hstable : (prefixWord ++ tailWord_7177425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7177425).length < 2 ^ (prefixWord ++ tailWord_7177425).sum := by decide
  have hdescent : baseEnd_7177425 < baseStart_7177425 := by decide
  rcases family_descends (prefixWord ++ tailWord_7177425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7177473 : List Nat := [1, 2, 4, 1, 1, 4, 3, 1, 2, 2, 2]
def baseStart_7177473 : Nat := 118140960795 + 7177473 * 2 ^ 59
def prefixEnd_7177473 : Nat := 4983230072969 + 3 ^ 40 * 7177473 * 2
def baseEnd_7177473 : Nat := 3685493533668101837578909

theorem tailTrace_7177473 : CollatzResearch.WordTrace tailWord_7177473 prefixEnd_7177473 3685493533668101837578909 := by
  unfold tailWord_7177473
  simp only [CollatzResearch.WordTrace]
  refine ⟨261783946726248610641409073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174522631150832407094272715 261783946726248610641409073)
  ·
    refine ⟨196337960044686457981056805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261783946726248610641409073 196337960044686457981056805)
    ·
      refine ⟨36813367508378710871448151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 196337960044686457981056805 36813367508378710871448151)
      ·
        refine ⟨55220051262568066307172227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36813367508378710871448151 55220051262568066307172227)
        ·
          refine ⟨82830076893852099460758341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55220051262568066307172227 82830076893852099460758341)
          ·
            refine ⟨15530639417597268648892189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82830076893852099460758341 15530639417597268648892189)
            ·
              refine ⟨5823989781598975743334571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15530639417597268648892189 5823989781598975743334571)
              ·
                refine ⟨8735984672398463615001857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5823989781598975743334571 8735984672398463615001857)
                ·
                  refine ⟨6551988504298847711251393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8735984672398463615001857 6551988504298847711251393)
                  ·
                    refine ⟨4913991378224135783438545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6551988504298847711251393 4913991378224135783438545)
                    ·
                      refine ⟨3685493533668101837578909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4913991378224135783438545 3685493533668101837578909)
                      ·
                        rfl

theorem cell23_7177473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 3, 1, 2, 2, 2].length) (baseStart_7177473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7177473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7177473 prefixEnd_7177473 := by exact prefixLift 7177473
  have htrace : WordTrace (prefixWord ++ tailWord_7177473) baseStart_7177473 baseEnd_7177473 := by
    simpa [prefixWord, tailWord_7177473, baseEnd_7177473] using wordTrace_append hprefix tailTrace_7177473
  have hstable : (prefixWord ++ tailWord_7177473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7177473).length < 2 ^ (prefixWord ++ tailWord_7177473).sum := by decide
  have hdescent : baseEnd_7177473 < baseStart_7177473 := by decide
  rcases family_descends (prefixWord ++ tailWord_7177473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7177475 : List Nat := [1, 1, 1, 3, 2, 4, 1, 2, 1, 7]
def baseStart_7177475 : Nat := 118140960795 + 7177475 * 2 ^ 59
def prefixEnd_7177475 : Nat := 4983230072969 + 3 ^ 40 * 7177475 * 2
def baseEnd_7177475 : Nat := 1228498186876470276584633

theorem tailTrace_7177475 : CollatzResearch.WordTrace tailWord_7177475 prefixEnd_7177475 1228498186876470276584633 := by
  unfold tailWord_7177475
  simp only [CollatzResearch.WordTrace]
  refine ⟨261784019672241364982981879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174522679781494243321987919 261784019672241364982981879)
  ·
    refine ⟨392676029508362047474472819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261784019672241364982981879 392676029508362047474472819)
    ·
      refine ⟨589014044262543071211709229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392676029508362047474472819 589014044262543071211709229)
      ·
        refine ⟨220880266598453651704390961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 589014044262543071211709229 220880266598453651704390961)
        ·
          refine ⟨165660199948840238778293221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220880266598453651704390961 165660199948840238778293221)
          ·
            refine ⟨31061287490407544770929979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 165660199948840238778293221 31061287490407544770929979)
            ·
              refine ⟨46591931235611317156394969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31061287490407544770929979 46591931235611317156394969)
              ·
                refine ⟨34943948426708487867296227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46591931235611317156394969 34943948426708487867296227)
                ·
                  refine ⟨52415922640062731800944341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34943948426708487867296227 52415922640062731800944341)
                  ·
                    refine ⟨1228498186876470276584633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52415922640062731800944341 1228498186876470276584633)
                    ·
                      rfl

theorem cell23_7177475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 2, 1, 7].length) (baseStart_7177475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7177475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7177475 prefixEnd_7177475 := by exact prefixLift 7177475
  have htrace : WordTrace (prefixWord ++ tailWord_7177475) baseStart_7177475 baseEnd_7177475 := by
    simpa [prefixWord, tailWord_7177475, baseEnd_7177475] using wordTrace_append hprefix tailTrace_7177475
  have hstable : (prefixWord ++ tailWord_7177475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7177475).length < 2 ^ (prefixWord ++ tailWord_7177475).sum := by decide
  have hdescent : baseEnd_7177475 < baseStart_7177475 := by decide
  rcases family_descends (prefixWord ++ tailWord_7177475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7177556 : List Nat := [2, 4, 1, 1, 2, 1, 2, 5, 1, 4]
def baseStart_7177556 : Nat := 118140960795 + 7177556 * 2 ^ 59
def prefixEnd_7177556 : Nat := 4983230072969 + 3 ^ 40 * 7177556 * 2
def baseEnd_7177556 : Nat := 1228512050854141670947009

theorem tailTrace_7177556 : CollatzResearch.WordTrace tailWord_7177556 prefixEnd_7177556 1228512050854141670947009 := by
  unfold tailWord_7177556
  simp only [CollatzResearch.WordTrace]
  refine ⟨130893486992473957908340261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174524649323298610544453681 130893486992473957908340261)
  ·
    refine ⟨24542528811088867107813799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130893486992473957908340261 24542528811088867107813799)
    ·
      refine ⟨36813793216633300661720699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24542528811088867107813799 36813793216633300661720699)
      ·
        refine ⟨55220689824949950992581049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36813793216633300661720699 55220689824949950992581049)
        ·
          refine ⟨41415517368712463244435787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55220689824949950992581049 41415517368712463244435787)
          ·
            refine ⟨62123276053068694866653681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41415517368712463244435787 62123276053068694866653681)
            ·
              refine ⟨46592457039801521149990261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62123276053068694866653681 46592457039801521149990261)
              ·
                refine ⟨4368042847481392607811587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46592457039801521149990261 4368042847481392607811587)
                ·
                  refine ⟨6552064271222088911717381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4368042847481392607811587 6552064271222088911717381)
                  ·
                    refine ⟨1228512050854141670947009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6552064271222088911717381 1228512050854141670947009)
                    ·
                      rfl

theorem cell23_7177556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 5, 1, 4].length) (baseStart_7177556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7177556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7177556 prefixEnd_7177556 := by exact prefixLift 7177556
  have htrace : WordTrace (prefixWord ++ tailWord_7177556) baseStart_7177556 baseEnd_7177556 := by
    simpa [prefixWord, tailWord_7177556, baseEnd_7177556] using wordTrace_append hprefix tailTrace_7177556
  have hstable : (prefixWord ++ tailWord_7177556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7177556).length < 2 ^ (prefixWord ++ tailWord_7177556).sum := by decide
  have hdescent : baseEnd_7177556 < baseStart_7177556 := by decide
  rcases family_descends (prefixWord ++ tailWord_7177556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7177612 : List Nat := [2, 2, 1, 2, 1, 3, 1, 4, 1, 6]
def baseStart_7177612 : Nat := 118140960795 + 7177612 * 2 ^ 59
def prefixEnd_7177612 : Nat := 4983230072969 + 3 ^ 40 * 7177612 * 2
def baseEnd_7177612 : Nat := 1228521635826358931246923

theorem tailTrace_7177612 : CollatzResearch.WordTrace tailWord_7177612 prefixEnd_7177612 1228521635826358931246923 := by
  unfold tailWord_7177612
  simp only [CollatzResearch.WordTrace]
  refine ⟨130894508236372518690359545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174526010981830024920479393 130894508236372518690359545)
  ·
    refine ⟨98170881177279389017769659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130894508236372518690359545 98170881177279389017769659)
    ·
      refine ⟨147256321765919083526654489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98170881177279389017769659 147256321765919083526654489)
      ·
        refine ⟨110442241324439312644990867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147256321765919083526654489 110442241324439312644990867)
        ·
          refine ⟨165663361986658968967486301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110442241324439312644990867 165663361986658968967486301)
          ·
            refine ⟨62123760744997113362807363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165663361986658968967486301 62123760744997113362807363)
            ·
              refine ⟨93185641117495670044211045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62123760744997113362807363 93185641117495670044211045)
              ·
                refine ⟨17472307709530438133289571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93185641117495670044211045 17472307709530438133289571)
                ·
                  refine ⟨26208461564295657199934357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17472307709530438133289571 26208461564295657199934357)
                  ·
                    refine ⟨1228521635826358931246923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26208461564295657199934357 1228521635826358931246923)
                    ·
                      rfl

theorem cell23_7177612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 4, 1, 6].length) (baseStart_7177612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7177612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7177612 prefixEnd_7177612 := by exact prefixLift 7177612
  have htrace : WordTrace (prefixWord ++ tailWord_7177612) baseStart_7177612 baseEnd_7177612 := by
    simpa [prefixWord, tailWord_7177612, baseEnd_7177612] using wordTrace_append hprefix tailTrace_7177612
  have hstable : (prefixWord ++ tailWord_7177612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7177612).length < 2 ^ (prefixWord ++ tailWord_7177612).sum := by decide
  have hdescent : baseEnd_7177612 < baseStart_7177612 := by decide
  rcases family_descends (prefixWord ++ tailWord_7177612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7177630 : List Nat := [4, 3, 1, 2, 2, 1, 2, 1, 3, 1, 3]
def baseStart_7177630 : Nat := 118140960795 + 7177630 * 2 ^ 59
def prefixEnd_7177630 : Nat := 4983230072969 + 3 ^ 40 * 7177630 * 2
def baseEnd_7177630 : Nat := 3685574150130857723315687

theorem tailTrace_7177630 : CollatzResearch.WordTrace tailWord_7177630 prefixEnd_7177630 3685574150130857723315687 := by
  unfold tailWord_7177630
  simp only [CollatzResearch.WordTrace]
  refine ⟨32723709123334978306859293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174526448657786550969916229 32723709123334978306859293)
  ·
    refine ⟨12271390921250616865072235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32723709123334978306859293 12271390921250616865072235)
    ·
      refine ⟨18407086381875925297608353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12271390921250616865072235 18407086381875925297608353)
      ·
        refine ⟨13805314786406943973206265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18407086381875925297608353 13805314786406943973206265)
        ·
          refine ⟨10353986089805207979904699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13805314786406943973206265 10353986089805207979904699)
          ·
            refine ⟨15530979134707811969857049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10353986089805207979904699 15530979134707811969857049)
            ·
              refine ⟨11648234351030858977392787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15530979134707811969857049 11648234351030858977392787)
              ·
                refine ⟨17472351526546288466089181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11648234351030858977392787 17472351526546288466089181)
                ·
                  refine ⟨6552131822454858174783443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17472351526546288466089181 6552131822454858174783443)
                  ·
                    refine ⟨9828197733682287262175165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6552131822454858174783443 9828197733682287262175165)
                    ·
                      refine ⟨3685574150130857723315687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9828197733682287262175165 3685574150130857723315687)
                      ·
                        rfl

theorem cell23_7177630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_7177630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7177630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7177630 prefixEnd_7177630 := by exact prefixLift 7177630
  have htrace : WordTrace (prefixWord ++ tailWord_7177630) baseStart_7177630 baseEnd_7177630 := by
    simpa [prefixWord, tailWord_7177630, baseEnd_7177630] using wordTrace_append hprefix tailTrace_7177630
  have hstable : (prefixWord ++ tailWord_7177630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7177630).length < 2 ^ (prefixWord ++ tailWord_7177630).sum := by decide
  have hdescent : baseEnd_7177630 < baseStart_7177630 := by decide
  rcases family_descends (prefixWord ++ tailWord_7177630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7177632 : List Nat := [2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 6]
def baseStart_7177632 : Nat := 118140960795 + 7177632 * 2 ^ 59
def prefixEnd_7177632 : Nat := 4983230072969 + 3 ^ 40 * 7177632 * 2
def baseEnd_7177632 : Nat := 3685575177092166715490677

theorem tailTrace_7177632 : CollatzResearch.WordTrace tailWord_7177632 prefixEnd_7177632 3685575177092166715490677 := by
  unfold tailWord_7177632
  simp only [CollatzResearch.WordTrace]
  refine ⟨130894872966336290398223575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174526497288448387197631433 130894872966336290398223575)
  ·
    refine ⟨196342309449504435597335363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130894872966336290398223575 196342309449504435597335363)
    ·
      refine ⟨294513464174256653396003045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196342309449504435597335363 294513464174256653396003045)
      ·
        refine ⟨55221274532673122511750571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 294513464174256653396003045 55221274532673122511750571)
        ·
          refine ⟨82831911799009683767625857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55221274532673122511750571 82831911799009683767625857)
          ·
            refine ⟨62123933849257262825719393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82831911799009683767625857 62123933849257262825719393)
            ·
              refine ⟨46592950386942947119289545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62123933849257262825719393 46592950386942947119289545)
              ·
                refine ⟨34944712790207210339467159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46592950386942947119289545 34944712790207210339467159)
                ·
                  refine ⟨52417069185310815509200739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34944712790207210339467159 52417069185310815509200739)
                  ·
                    refine ⟨78625603777966223263801109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52417069185310815509200739 78625603777966223263801109)
                    ·
                      refine ⟨3685575177092166715490677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78625603777966223263801109 3685575177092166715490677)
                      ·
                        rfl

theorem cell23_7177632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_7177632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7177632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7177632 prefixEnd_7177632 := by exact prefixLift 7177632
  have htrace : WordTrace (prefixWord ++ tailWord_7177632) baseStart_7177632 baseEnd_7177632 := by
    simpa [prefixWord, tailWord_7177632, baseEnd_7177632] using wordTrace_append hprefix tailTrace_7177632
  have hstable : (prefixWord ++ tailWord_7177632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7177632).length < 2 ^ (prefixWord ++ tailWord_7177632).sum := by decide
  have hdescent : baseEnd_7177632 < baseStart_7177632 := by decide
  rcases family_descends (prefixWord ++ tailWord_7177632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7177639 : List Nat := [1, 1, 6, 1, 1, 1, 3, 2, 1, 1, 5]
def baseStart_7177639 : Nat := 118140960795 + 7177639 * 2 ^ 59
def prefixEnd_7177639 : Nat := 4983230072969 + 3 ^ 40 * 7177639 * 2
def baseEnd_7177639 : Nat := 3685578771456748188103145

theorem tailTrace_7177639 : CollatzResearch.WordTrace tailWord_7177639 prefixEnd_7177639 3685578771456748188103145 := by
  unfold tailWord_7177639
  simp only [CollatzResearch.WordTrace]
  refine ⟨261790001243647220991951971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174526667495764813994634647 261790001243647220991951971)
  ·
    refine ⟨392685001865470831487927957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261790001243647220991951971 392685001865470831487927957)
    ·
      refine ⟨18407109462443945225996623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 392685001865470831487927957 18407109462443945225996623)
      ·
        refine ⟨27610664193665917838994935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18407109462443945225996623 27610664193665917838994935)
        ·
          refine ⟨41415996290498876758492403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27610664193665917838994935 41415996290498876758492403)
          ·
            refine ⟨62123994435748315137738605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41415996290498876758492403 62123994435748315137738605)
            ·
              refine ⟨23296497913405618176651977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62123994435748315137738605 23296497913405618176651977)
              ·
                refine ⟨17472373435054213632488983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23296497913405618176651977 17472373435054213632488983)
                ·
                  refine ⟨26208560152581320448733475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17472373435054213632488983 26208560152581320448733475)
                  ·
                    refine ⟨39312840228871980673100213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26208560152581320448733475 39312840228871980673100213)
                    ·
                      refine ⟨3685578771456748188103145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39312840228871980673100213 3685578771456748188103145)
                      ·
                        rfl

theorem cell23_7177639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_7177639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7177639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7177639 prefixEnd_7177639 := by exact prefixLift 7177639
  have htrace : WordTrace (prefixWord ++ tailWord_7177639) baseStart_7177639 baseEnd_7177639 := by
    simpa [prefixWord, tailWord_7177639, baseEnd_7177639] using wordTrace_append hprefix tailTrace_7177639
  have hstable : (prefixWord ++ tailWord_7177639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7177639).length < 2 ^ (prefixWord ++ tailWord_7177639).sum := by decide
  have hdescent : baseEnd_7177639 < baseStart_7177639 := by decide
  rcases family_descends (prefixWord ++ tailWord_7177639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7177653 : List Nat := [1, 3, 3, 2, 2, 1, 2, 2, 3, 2, 2]
def baseStart_7177653 : Nat := 118140960795 + 7177653 * 2 ^ 59
def prefixEnd_7177653 : Nat := 4983230072969 + 3 ^ 40 * 7177653 * 2
def baseEnd_7177653 : Nat := 3685585960185911133328081

theorem tailTrace_7177653 : CollatzResearch.WordTrace tailWord_7177653 prefixEnd_7177653 3685585960185911133328081 := by
  unfold tailWord_7177653
  simp only [CollatzResearch.WordTrace]
  refine ⟨261790511865596501382961613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174527007910397667588641075 261790511865596501382961613)
  ·
    refine ⟨98171441949598688018610605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261790511865596501382961613 98171441949598688018610605)
    ·
      refine ⟨36814290731099508006978977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98171441949598688018610605 36814290731099508006978977)
      ·
        refine ⟨27610718048324631005234233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36814290731099508006978977 27610718048324631005234233)
        ·
          refine ⟨20708038536243473253925675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27610718048324631005234233 20708038536243473253925675)
          ·
            refine ⟨31062057804365209880888513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20708038536243473253925675 31062057804365209880888513)
            ·
              refine ⟨23296543353273907410666385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31062057804365209880888513 23296543353273907410666385)
              ·
                refine ⟨17472407514955430557999789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23296543353273907410666385 17472407514955430557999789)
                ·
                  refine ⟨6552152818108286459249921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17472407514955430557999789 6552152818108286459249921)
                  ·
                    refine ⟨4914114613581214844437441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6552152818108286459249921 4914114613581214844437441)
                    ·
                      refine ⟨3685585960185911133328081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4914114613581214844437441 3685585960185911133328081)
                      ·
                        rfl

theorem cell23_7177653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 2, 3, 2, 2].length) (baseStart_7177653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7177653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7177653 prefixEnd_7177653 := by exact prefixLift 7177653
  have htrace : WordTrace (prefixWord ++ tailWord_7177653) baseStart_7177653 baseEnd_7177653 := by
    simpa [prefixWord, tailWord_7177653, baseEnd_7177653] using wordTrace_append hprefix tailTrace_7177653
  have hstable : (prefixWord ++ tailWord_7177653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7177653).length < 2 ^ (prefixWord ++ tailWord_7177653).sum := by decide
  have hdescent : baseEnd_7177653 < baseStart_7177653 := by decide
  rcases family_descends (prefixWord ++ tailWord_7177653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7177703 : List Nat := [1, 1, 5, 2, 1, 3, 1, 3, 2, 1, 3]
def baseStart_7177703 : Nat := 118140960795 + 7177703 * 2 ^ 59
def prefixEnd_7177703 : Nat := 4983230072969 + 3 ^ 40 * 7177703 * 2
def baseEnd_7177703 : Nat := 3685611634218635937702851

theorem tailTrace_7177703 : CollatzResearch.WordTrace tailWord_7177703 prefixEnd_7177703 3685611634218635937702851 := by
  unfold tailWord_7177703
  simp only [CollatzResearch.WordTrace]
  refine ⟨261792335515415359922281763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174528223676943573281521175 261792335515415359922281763)
  ·
    refine ⟨392688503273123039883422645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261792335515415359922281763 392688503273123039883422645)
    ·
      refine ⟨36814547181855284989070873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 392688503273123039883422645 36814547181855284989070873)
      ·
        refine ⟨27610910386391463741803155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36814547181855284989070873 27610910386391463741803155)
        ·
          refine ⟨41416365579587195612704733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27610910386391463741803155 41416365579587195612704733)
          ·
            refine ⟨15531137092345198354764275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41416365579587195612704733 15531137092345198354764275)
            ·
              refine ⟨23296705638517797532146413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15531137092345198354764275 23296705638517797532146413)
              ·
                refine ⟨8736264614444174074554905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23296705638517797532146413 8736264614444174074554905)
                ·
                  refine ⟨6552198460833130555916179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8736264614444174074554905 6552198460833130555916179)
                  ·
                    refine ⟨9828297691249695833874269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6552198460833130555916179 9828297691249695833874269)
                    ·
                      refine ⟨3685611634218635937702851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9828297691249695833874269 3685611634218635937702851)
                      ·
                        rfl

theorem cell23_7177703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_7177703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7177703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7177703 prefixEnd_7177703 := by exact prefixLift 7177703
  have htrace : WordTrace (prefixWord ++ tailWord_7177703) baseStart_7177703 baseEnd_7177703 := by
    simpa [prefixWord, tailWord_7177703, baseEnd_7177703] using wordTrace_append hprefix tailTrace_7177703
  have hstable : (prefixWord ++ tailWord_7177703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7177703).length < 2 ^ (prefixWord ++ tailWord_7177703).sum := by decide
  have hdescent : baseEnd_7177703 < baseStart_7177703 := by decide
  rcases family_descends (prefixWord ++ tailWord_7177703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7177713 : List Nat := [1, 2, 2, 2, 3, 2, 3, 2, 1, 3, 2]
def baseStart_7177713 : Nat := 118140960795 + 7177713 * 2 ^ 59
def prefixEnd_7177713 : Nat := 4983230072969 + 3 ^ 40 * 7177713 * 2
def baseEnd_7177713 : Nat := 3685616769025180898577805

theorem tailTrace_7177713 : CollatzResearch.WordTrace tailWord_7177713 prefixEnd_7177713 3685616769025180898577805 := by
  unfold tailWord_7177713
  simp only [CollatzResearch.WordTrace]
  refine ⟨261792700245379131630145793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174528466830252754420097195 261792700245379131630145793)
  ·
    refine ⟨196344525184034348722609345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261792700245379131630145793 196344525184034348722609345)
    ·
      refine ⟨147258393888025761541957009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196344525184034348722609345 147258393888025761541957009)
      ·
        refine ⟨110443795416019321156467757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147258393888025761541957009 110443795416019321156467757)
        ·
          refine ⟨41416423281007245433675409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110443795416019321156467757 41416423281007245433675409)
          ·
            refine ⟨31062317460755434075256557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41416423281007245433675409 31062317460755434075256557)
            ·
              refine ⟨11648369047783287778221209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31062317460755434075256557 11648369047783287778221209)
              ·
                refine ⟨8736276785837465833665907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11648369047783287778221209 8736276785837465833665907)
                ·
                  refine ⟨13104415178756198750498861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8736276785837465833665907 13104415178756198750498861)
                  ·
                    refine ⟨4914155692033574531437073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13104415178756198750498861 4914155692033574531437073)
                    ·
                      refine ⟨3685616769025180898577805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4914155692033574531437073 3685616769025180898577805)
                      ·
                        rfl

theorem cell23_7177713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 2, 1, 3, 2].length) (baseStart_7177713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7177713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7177713 prefixEnd_7177713 := by exact prefixLift 7177713
  have htrace : WordTrace (prefixWord ++ tailWord_7177713) baseStart_7177713 baseEnd_7177713 := by
    simpa [prefixWord, tailWord_7177713, baseEnd_7177713] using wordTrace_append hprefix tailTrace_7177713
  have hstable : (prefixWord ++ tailWord_7177713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7177713).length < 2 ^ (prefixWord ++ tailWord_7177713).sum := by decide
  have hdescent : baseEnd_7177713 < baseStart_7177713 := by decide
  rcases family_descends (prefixWord ++ tailWord_7177713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7177759 : List Nat := [1, 1, 2, 4, 1, 1, 3, 1, 1, 5, 3]
def baseStart_7177759 : Nat := 118140960795 + 7177759 * 2 ^ 59
def prefixEnd_7177759 : Nat := 4983230072969 + 3 ^ 40 * 7177759 * 2
def baseEnd_7177759 : Nat := 3685640389135287718602593

theorem tailTrace_7177759 : CollatzResearch.WordTrace tailWord_7177759 prefixEnd_7177759 3685640389135287718602593 := by
  unfold tailWord_7177759
  simp only [CollatzResearch.WordTrace]
  refine ⟨261794378003212481486320331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174529585335474987657546887 261794378003212481486320331)
  ·
    refine ⟨392691567004818722229480497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261794378003212481486320331 392691567004818722229480497)
    ·
      refine ⟨294518675253614041672110373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 392691567004818722229480497 294518675253614041672110373)
      ·
        refine ⟨55222251610052632813520695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 294518675253614041672110373 55222251610052632813520695)
        ·
          refine ⟨82833377415078949220281043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55222251610052632813520695 82833377415078949220281043)
          ·
            refine ⟨124250066122618423830421565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82833377415078949220281043 124250066122618423830421565)
            ·
              refine ⟨46593774795981908936408087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124250066122618423830421565 46593774795981908936408087)
              ·
                refine ⟨69890662193972863404612131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46593774795981908936408087 69890662193972863404612131)
                ·
                  refine ⟨104835993290959295106918197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69890662193972863404612131 104835993290959295106918197)
                  ·
                    refine ⟨9828374371027433916273581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 104835993290959295106918197 9828374371027433916273581)
                    ·
                      refine ⟨3685640389135287718602593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9828374371027433916273581 3685640389135287718602593)
                      ·
                        rfl

theorem cell23_7177759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 5, 3].length) (baseStart_7177759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7177759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7177759 prefixEnd_7177759 := by exact prefixLift 7177759
  have htrace : WordTrace (prefixWord ++ tailWord_7177759) baseStart_7177759 baseEnd_7177759 := by
    simpa [prefixWord, tailWord_7177759, baseEnd_7177759] using wordTrace_append hprefix tailTrace_7177759
  have hstable : (prefixWord ++ tailWord_7177759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7177759).length < 2 ^ (prefixWord ++ tailWord_7177759).sum := by decide
  have hdescent : baseEnd_7177759 < baseStart_7177759 := by decide
  rcases family_descends (prefixWord ++ tailWord_7177759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7177760 : List Nat := [2, 1, 1, 6, 1, 1, 2, 3, 2, 2, 2]
def baseStart_7177760 : Nat := 118140960795 + 7177760 * 2 ^ 59
def prefixEnd_7177760 : Nat := 4983230072969 + 3 ^ 40 * 7177760 * 2
def baseEnd_7177760 : Nat := 3685640902615942214690089

theorem tailTrace_7177760 : CollatzResearch.WordTrace tailWord_7177760 prefixEnd_7177760 3685640902615942214690089 := by
  unfold tailWord_7177760
  simp only [CollatzResearch.WordTrace]
  refine ⟨130897207238104429328553367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174529609650805905771404489 130897207238104429328553367)
  ·
    refine ⟨196345810857156643992830051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130897207238104429328553367 196345810857156643992830051)
    ·
      refine ⟨294518716285734965989245077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196345810857156643992830051 294518716285734965989245077)
      ·
        refine ⟨13805564825893826530745863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 294518716285734965989245077 13805564825893826530745863)
        ·
          refine ⟨20708347238840739796118795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13805564825893826530745863 20708347238840739796118795)
          ·
            refine ⟨31062520858261109694178193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20708347238840739796118795 31062520858261109694178193)
            ·
              refine ⟨23296890643695832270633645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31062520858261109694178193 23296890643695832270633645)
              ·
                refine ⟨8736333991385937101487617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23296890643695832270633645 8736333991385937101487617)
                ·
                  refine ⟨6552250493539452826115713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8736333991385937101487617 6552250493539452826115713)
                  ·
                    refine ⟨4914187870154589619586785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6552250493539452826115713 4914187870154589619586785)
                    ·
                      refine ⟨3685640902615942214690089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4914187870154589619586785 3685640902615942214690089)
                      ·
                        rfl

theorem cell23_7177760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_7177760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7177760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7177760 prefixEnd_7177760 := by exact prefixLift 7177760
  have htrace : WordTrace (prefixWord ++ tailWord_7177760) baseStart_7177760 baseEnd_7177760 := by
    simpa [prefixWord, tailWord_7177760, baseEnd_7177760] using wordTrace_append hprefix tailTrace_7177760
  have hstable : (prefixWord ++ tailWord_7177760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7177760).length < 2 ^ (prefixWord ++ tailWord_7177760).sum := by decide
  have hdescent : baseEnd_7177760 < baseStart_7177760 := by decide
  rcases family_descends (prefixWord ++ tailWord_7177760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7177779 : List Nat := [1, 1, 1, 2, 4, 4, 1, 1, 1, 7]
def baseStart_7177779 : Nat := 118140960795 + 7177779 * 2 ^ 59
def prefixEnd_7177779 : Nat := 4983230072969 + 3 ^ 40 * 7177779 * 2
def baseEnd_7177779 : Nat := 1228550219582792546784167

theorem tailTrace_7177779 : CollatzResearch.WordTrace tailWord_7177779 prefixEnd_7177779 1228550219582792546784167 := by
  unfold tailWord_7177779
  simp only [CollatzResearch.WordTrace]
  refine ⟨261795107463140024902048391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174530071642093349934698927 261795107463140024902048391)
  ·
    refine ⟨392692661194710037353072587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261795107463140024902048391 392692661194710037353072587)
    ·
      refine ⟨589038991792065056029608881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392692661194710037353072587 589038991792065056029608881)
      ·
        refine ⟨441779243844048792022206661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 589038991792065056029608881 441779243844048792022206661)
        ·
          refine ⟨82833608220759148504163749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 441779243844048792022206661 82833608220759148504163749)
          ·
            refine ⟨15531301541392340344530703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82833608220759148504163749 15531301541392340344530703)
            ·
              refine ⟨23296952312088510516796055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15531301541392340344530703 23296952312088510516796055)
              ·
                refine ⟨34945428468132765775194083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23296952312088510516796055 34945428468132765775194083)
                ·
                  refine ⟨52418142702199148662791125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34945428468132765775194083 52418142702199148662791125)
                  ·
                    refine ⟨1228550219582792546784167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52418142702199148662791125 1228550219582792546784167)
                    ·
                      rfl

theorem cell23_7177779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 1, 1, 7].length) (baseStart_7177779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7177779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7177779 prefixEnd_7177779 := by exact prefixLift 7177779
  have htrace : WordTrace (prefixWord ++ tailWord_7177779) baseStart_7177779 baseEnd_7177779 := by
    simpa [prefixWord, tailWord_7177779, baseEnd_7177779] using wordTrace_append hprefix tailTrace_7177779
  have hstable : (prefixWord ++ tailWord_7177779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7177779).length < 2 ^ (prefixWord ++ tailWord_7177779).sum := by decide
  have hdescent : baseEnd_7177779 < baseStart_7177779 := by decide
  rcases family_descends (prefixWord ++ tailWord_7177779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7177836 : List Nat := [2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 3]
def baseStart_7177836 : Nat := 118140960795 + 7177836 * 2 ^ 59
def prefixEnd_7177836 : Nat := 4983230072969 + 3 ^ 40 * 7177836 * 2
def baseEnd_7177836 : Nat := 3685679927145683917339739

theorem tailTrace_7177836 : CollatzResearch.WordTrace tailWord_7177836 prefixEnd_7177836 3685679927145683917339739 := by
  unfold tailWord_7177836
  simp only [CollatzResearch.WordTrace]
  refine ⟨130898593211966761818436681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174531457615955682424582241 130898593211966761818436681)
  ·
    refine ⟨98173944908975071363827511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130898593211966761818436681 98173944908975071363827511)
    ·
      refine ⟨147260917363462607045741267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98173944908975071363827511 147260917363462607045741267)
      ·
        refine ⟨220891376045193910568611901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147260917363462607045741267 220891376045193910568611901)
        ·
          refine ⟨82834266016947716463229463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 220891376045193910568611901 82834266016947716463229463)
          ·
            refine ⟨124251399025421574694844195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82834266016947716463229463 124251399025421574694844195)
            ·
              refine ⟨186377098538132362042266293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124251399025421574694844195 186377098538132362042266293)
              ·
                refine ⟨17472852987949908941462465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 186377098538132362042266293 17472852987949908941462465)
                ·
                  refine ⟨13104639740962431706096849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17472852987949908941462465 13104639740962431706096849)
                  ·
                    refine ⟨9828479805721823779572637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13104639740962431706096849 9828479805721823779572637)
                    ·
                      refine ⟨3685679927145683917339739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9828479805721823779572637 3685679927145683917339739)
                      ·
                        rfl

theorem cell23_7177836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 3].length) (baseStart_7177836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7177836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7177836 prefixEnd_7177836 := by exact prefixLift 7177836
  have htrace : WordTrace (prefixWord ++ tailWord_7177836) baseStart_7177836 baseEnd_7177836 := by
    simpa [prefixWord, tailWord_7177836, baseEnd_7177836] using wordTrace_append hprefix tailTrace_7177836
  have hstable : (prefixWord ++ tailWord_7177836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7177836).length < 2 ^ (prefixWord ++ tailWord_7177836).sum := by decide
  have hdescent : baseEnd_7177836 < baseStart_7177836 := by decide
  rcases family_descends (prefixWord ++ tailWord_7177836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7177853 : List Nat := [1, 4, 1, 1, 4, 2, 1, 2, 2, 2, 3]
def baseStart_7177853 : Nat := 118140960795 + 7177853 * 2 ^ 59
def prefixEnd_7177853 : Nat := 4983230072969 + 3 ^ 40 * 7177853 * 2
def baseEnd_7177853 : Nat := 3685688656316810350827161

theorem tailTrace_7177853 : CollatzResearch.WordTrace tailWord_7177853 prefixEnd_7177853 3685688656316810350827161 := by
  unfold tailWord_7177853
  simp only [CollatzResearch.WordTrace]
  refine ⟨261797806464871935540242213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174531870976581290360161475 261797806464871935540242213)
  ·
    refine ⟨49087088712163487913795415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 261797806464871935540242213 49087088712163487913795415)
    ·
      refine ⟨73630633068245231870693123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49087088712163487913795415 73630633068245231870693123)
      ·
        refine ⟨110445949602367847806039685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73630633068245231870693123 110445949602367847806039685)
        ·
          refine ⟨20708615550443971463632441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110445949602367847806039685 20708615550443971463632441)
          ·
            refine ⟨15531461662832978597724331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20708615550443971463632441 15531461662832978597724331)
            ·
              refine ⟨23297192494249467896586497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15531461662832978597724331 23297192494249467896586497)
              ·
                refine ⟨17472894370687100922439873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23297192494249467896586497 17472894370687100922439873)
                ·
                  refine ⟨13104670778015325691829905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17472894370687100922439873 13104670778015325691829905)
                  ·
                    refine ⟨9828503083511494268872429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13104670778015325691829905 9828503083511494268872429)
                    ·
                      refine ⟨3685688656316810350827161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9828503083511494268872429 3685688656316810350827161)
                      ·
                        rfl

theorem cell23_7177853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 2, 2, 2, 3].length) (baseStart_7177853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7177853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7177853 prefixEnd_7177853 := by exact prefixLift 7177853
  have htrace : WordTrace (prefixWord ++ tailWord_7177853) baseStart_7177853 baseEnd_7177853 := by
    simpa [prefixWord, tailWord_7177853, baseEnd_7177853] using wordTrace_append hprefix tailTrace_7177853
  have hstable : (prefixWord ++ tailWord_7177853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7177853).length < 2 ^ (prefixWord ++ tailWord_7177853).sum := by decide
  have hdescent : baseEnd_7177853 < baseStart_7177853 := by decide
  rcases family_descends (prefixWord ++ tailWord_7177853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7177860 : List Nat := [2, 3, 2, 1, 4, 2, 1, 1, 3, 4]
def baseStart_7177860 : Nat := 118140960795 + 7177860 * 2 ^ 59
def prefixEnd_7177860 : Nat := 4983230072969 + 3 ^ 40 * 7177860 * 2
def baseEnd_7177860 : Nat := 1228564083560463941146543

theorem tailTrace_7177860 : CollatzResearch.WordTrace tailWord_7177860 prefixEnd_7177860 1228564083560463941146543 := by
  unfold tailWord_7177860
  simp only [CollatzResearch.WordTrace]
  refine ⟨130899030887923287867873517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174532041183897717157164689 130899030887923287867873517)
  ·
    refine ⟨49087136582971232950452569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130899030887923287867873517 49087136582971232950452569)
    ·
      refine ⟨36815352437228424712839427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49087136582971232950452569 36815352437228424712839427)
      ·
        refine ⟨55223028655842637069259141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36815352437228424712839427 55223028655842637069259141)
        ·
          refine ⟨10354317872970494450486089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55223028655842637069259141 10354317872970494450486089)
          ·
            refine ⟨7765738404727870837864567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10354317872970494450486089 7765738404727870837864567)
            ·
              refine ⟨11648607607091806256796851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7765738404727870837864567 11648607607091806256796851)
              ·
                refine ⟨17472911410637709385195277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11648607607091806256796851 17472911410637709385195277)
                ·
                  refine ⟨6552341778989141019448229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17472911410637709385195277 6552341778989141019448229)
                  ·
                    refine ⟨1228564083560463941146543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6552341778989141019448229 1228564083560463941146543)
                    ·
                      rfl

theorem cell23_7177860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 1, 3, 4].length) (baseStart_7177860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7177860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7177860 prefixEnd_7177860 := by exact prefixLift 7177860
  have htrace : WordTrace (prefixWord ++ tailWord_7177860) baseStart_7177860 baseEnd_7177860 := by
    simpa [prefixWord, tailWord_7177860, baseEnd_7177860] using wordTrace_append hprefix tailTrace_7177860
  have hstable : (prefixWord ++ tailWord_7177860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7177860).length < 2 ^ (prefixWord ++ tailWord_7177860).sum := by decide
  have hdescent : baseEnd_7177860 < baseStart_7177860 := by decide
  rcases family_descends (prefixWord ++ tailWord_7177860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7177893 : List Nat := [1, 3, 1, 2, 1, 2, 3, 3, 2, 3, 2]
def baseStart_7177893 : Nat := 118140960795 + 7177893 * 2 ^ 59
def prefixEnd_7177893 : Nat := 4983230072969 + 3 ^ 40 * 7177893 * 2
def baseEnd_7177893 : Nat := 3685709195542990194326977

theorem tailTrace_7177893 : CollatzResearch.WordTrace tailWord_7177893 prefixEnd_7177893 3685709195542990194326977 := by
  unfold tailWord_7177893
  simp only [CollatzResearch.WordTrace]
  refine ⟨261799265384727022371698333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174532843589818014914465555 261799265384727022371698333)
  ·
    refine ⟨98174724519272633389386875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261799265384727022371698333 98174724519272633389386875)
    ·
      refine ⟨147262086778908950084080313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98174724519272633389386875 147262086778908950084080313)
      ·
        refine ⟨110446565084181712563060235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147262086778908950084080313 110446565084181712563060235)
        ·
          refine ⟨165669847626272568844590353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110446565084181712563060235 165669847626272568844590353)
          ·
            refine ⟨124252385719704426633442765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165669847626272568844590353 124252385719704426633442765)
            ·
              refine ⟨46594644644889159987541037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124252385719704426633442765 46594644644889159987541037)
              ·
                refine ⟨17472991741833434995327889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46594644644889159987541037 17472991741833434995327889)
                ·
                  refine ⟨13104743806375076246495917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17472991741833434995327889 13104743806375076246495917)
                  ·
                    refine ⟨4914278927390653592435969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13104743806375076246495917 4914278927390653592435969)
                    ·
                      refine ⟨3685709195542990194326977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4914278927390653592435969 3685709195542990194326977)
                      ·
                        rfl

theorem cell23_7177893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 3, 2, 3, 2].length) (baseStart_7177893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7177893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7177893 prefixEnd_7177893 := by exact prefixLift 7177893
  have htrace : WordTrace (prefixWord ++ tailWord_7177893) baseStart_7177893 baseEnd_7177893 := by
    simpa [prefixWord, tailWord_7177893, baseEnd_7177893] using wordTrace_append hprefix tailTrace_7177893
  have hstable : (prefixWord ++ tailWord_7177893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7177893).length < 2 ^ (prefixWord ++ tailWord_7177893).sum := by decide
  have hdescent : baseEnd_7177893 < baseStart_7177893 := by decide
  rcases family_descends (prefixWord ++ tailWord_7177893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7177903 : List Nat := [1, 1, 2, 1, 2, 4, 5, 1, 1, 5]
def baseStart_7177903 : Nat := 118140960795 + 7177903 * 2 ^ 59
def prefixEnd_7177903 : Nat := 4983230072969 + 3 ^ 40 * 7177903 * 2
def baseEnd_7177903 : Nat := 1228571443449845051733977

theorem tailTrace_7177903 : CollatzResearch.WordTrace tailWord_7177903 prefixEnd_7177903 1228571443449845051733977 := by
  unfold tailWord_7177903
  simp only [CollatzResearch.WordTrace]
  refine ⟨261799630114690794079562363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174533086743127196053041575 261799630114690794079562363)
  ·
    refine ⟨392699445172036191119343545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261799630114690794079562363 392699445172036191119343545)
    ·
      refine ⟨294524583879027143339507659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 392699445172036191119343545 294524583879027143339507659)
      ·
        refine ⟨441786875818540715009261489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294524583879027143339507659 441786875818540715009261489)
        ·
          refine ⟨331340156863905536256946117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 441786875818540715009261489 331340156863905536256946117)
          ·
            refine ⟨62126279411982288048177397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 331340156863905536256946117 62126279411982288048177397)
            ·
              refine ⟨5824338694873339504516631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62126279411982288048177397 5824338694873339504516631)
              ·
                refine ⟨8736508042310009256774947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5824338694873339504516631 8736508042310009256774947)
                ·
                  refine ⟨13104762063465013885162421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8736508042310009256774947 13104762063465013885162421)
                  ·
                    refine ⟨1228571443449845051733977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13104762063465013885162421 1228571443449845051733977)
                    ·
                      rfl

theorem cell23_7177903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 5, 1, 1, 5].length) (baseStart_7177903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7177903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7177903 prefixEnd_7177903 := by exact prefixLift 7177903
  have htrace : WordTrace (prefixWord ++ tailWord_7177903) baseStart_7177903 baseEnd_7177903 := by
    simpa [prefixWord, tailWord_7177903, baseEnd_7177903] using wordTrace_append hprefix tailTrace_7177903
  have hstable : (prefixWord ++ tailWord_7177903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7177903).length < 2 ^ (prefixWord ++ tailWord_7177903).sum := by decide
  have hdescent : baseEnd_7177903 < baseStart_7177903 := by decide
  rcases family_descends (prefixWord ++ tailWord_7177903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7177923 : List Nat := [1, 1, 1, 3, 1, 1, 1, 1, 9, 2, 2]
def baseStart_7177923 : Nat := 118140960795 + 7177923 * 2 ^ 59
def prefixEnd_7177923 : Nat := 4983230072969 + 3 ^ 40 * 7177923 * 2
def baseEnd_7177923 : Nat := 3685724599962625076951839

theorem tailTrace_7177923 : CollatzResearch.WordTrace tailWord_7177923 prefixEnd_7177923 3685724599962625076951839 := by
  unfold tailWord_7177923
  simp only [CollatzResearch.WordTrace]
  refine ⟨261800359574618337495290423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174533573049745558330193615 261800359574618337495290423)
  ·
    refine ⟨392700539361927506242935635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261800359574618337495290423 392700539361927506242935635)
    ·
      refine ⟨589050809042891259364403453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392700539361927506242935635 589050809042891259364403453)
      ·
        refine ⟨220894053391084222261651295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 589050809042891259364403453 220894053391084222261651295)
        ·
          refine ⟨331341080086626333392476943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220894053391084222261651295 331341080086626333392476943)
          ·
            refine ⟨497011620129939500088715415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 331341080086626333392476943 497011620129939500088715415)
            ·
              refine ⟨745517430194909250133073123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 497011620129939500088715415 745517430194909250133073123)
              ·
                refine ⟨1118276145292363875199609685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 745517430194909250133073123 1118276145292363875199609685)
                ·
                  refine ⟨6552399288822444581247713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1118276145292363875199609685 6552399288822444581247713)
                  ·
                    refine ⟨4914299466616833435935785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6552399288822444581247713 4914299466616833435935785)
                    ·
                      refine ⟨3685724599962625076951839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4914299466616833435935785 3685724599962625076951839)
                      ·
                        rfl

theorem cell23_7177923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 9, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 9, 2, 2].length) (baseStart_7177923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7177923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7177923 prefixEnd_7177923 := by exact prefixLift 7177923
  have htrace : WordTrace (prefixWord ++ tailWord_7177923) baseStart_7177923 baseEnd_7177923 := by
    simpa [prefixWord, tailWord_7177923, baseEnd_7177923] using wordTrace_append hprefix tailTrace_7177923
  have hstable : (prefixWord ++ tailWord_7177923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7177923).length < 2 ^ (prefixWord ++ tailWord_7177923).sum := by decide
  have hdescent : baseEnd_7177923 < baseStart_7177923 := by decide
  rcases family_descends (prefixWord ++ tailWord_7177923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7177943 : List Nat := [1, 1, 3, 2, 1, 3, 2, 4, 1, 2, 3]
def baseStart_7177943 : Nat := 118140960795 + 7177943 * 2 ^ 59
def prefixEnd_7177943 : Nat := 4983230072969 + 3 ^ 40 * 7177943 * 2
def baseEnd_7177943 : Nat := 3685734869575714998701747

theorem tailTrace_7177943 : CollatzResearch.WordTrace tailWord_7177943 prefixEnd_7177943 3685734869575714998701747 := by
  unfold tailWord_7177943
  simp only [CollatzResearch.WordTrace]
  refine ⟨261801089034545880911018483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174534059356363920607345655 261801089034545880911018483)
  ·
    refine ⟨392701633551818821366527725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261801089034545880911018483 392701633551818821366527725)
    ·
      refine ⟨147263112581932058012447897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 392701633551818821366527725 147263112581932058012447897)
      ·
        refine ⟨110447334436449043509335923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147263112581932058012447897 110447334436449043509335923)
        ·
          refine ⟨165671001654673565264003885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110447334436449043509335923 165671001654673565264003885)
          ·
            refine ⟨62126625620502586974001457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165671001654673565264003885 62126625620502586974001457)
            ·
              refine ⟨46594969215376940230501093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62126625620502586974001457 46594969215376940230501093)
              ·
                refine ⟨8736556727883176293218955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46594969215376940230501093 8736556727883176293218955)
                ·
                  refine ⟨13104835091824764439828433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8736556727883176293218955 13104835091824764439828433)
                  ·
                    refine ⟨9828626318868573329871325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13104835091824764439828433 9828626318868573329871325)
                    ·
                      refine ⟨3685734869575714998701747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9828626318868573329871325 3685734869575714998701747)
                      ·
                        rfl

theorem cell23_7177943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 4, 1, 2, 3].length) (baseStart_7177943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7177943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7177943 prefixEnd_7177943 := by exact prefixLift 7177943
  have htrace : WordTrace (prefixWord ++ tailWord_7177943) baseStart_7177943 baseEnd_7177943 := by
    simpa [prefixWord, tailWord_7177943, baseEnd_7177943] using wordTrace_append hprefix tailTrace_7177943
  have hstable : (prefixWord ++ tailWord_7177943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7177943).length < 2 ^ (prefixWord ++ tailWord_7177943).sum := by decide
  have hdescent : baseEnd_7177943 < baseStart_7177943 := by decide
  rcases family_descends (prefixWord ++ tailWord_7177943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7177960 : List Nat := [2, 1, 4, 1, 3, 2, 1, 3, 1, 2, 3]
def baseStart_7177960 : Nat := 118140960795 + 7177960 * 2 ^ 59
def prefixEnd_7177960 : Nat := 4983230072969 + 3 ^ 40 * 7177960 * 2
def baseEnd_7177960 : Nat := 3685743598746841432189169

theorem tailTrace_7177960 : CollatzResearch.WordTrace tailWord_7177960 prefixEnd_7177960 3685743598746841432189169 := by
  unfold tailWord_7177960
  simp only [CollatzResearch.WordTrace]
  refine ⟨130900854537742146407193667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174534472716989528542924889 130900854537742146407193667)
  ·
    refine ⟨196351281806613219610790501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130900854537742146407193667 196351281806613219610790501)
    ·
      refine ⟨36815865338739978677023219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 196351281806613219610790501 36815865338739978677023219)
      ·
        refine ⟨55223798008109968015534829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36815865338739978677023219 55223798008109968015534829)
        ·
          refine ⟨20708924253041238005825561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55223798008109968015534829 20708924253041238005825561)
          ·
            refine ⟨15531693189780928504369171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20708924253041238005825561 15531693189780928504369171)
            ·
              refine ⟨23297539784671392756553757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15531693189780928504369171 23297539784671392756553757)
              ·
                refine ⟨8736577419251772283707659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23297539784671392756553757 8736577419251772283707659)
                ·
                  refine ⟨13104866128877658425561489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8736577419251772283707659 13104866128877658425561489)
                  ·
                    refine ⟨9828649596658243819171117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13104866128877658425561489 9828649596658243819171117)
                    ·
                      refine ⟨3685743598746841432189169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9828649596658243819171117 3685743598746841432189169)
                      ·
                        rfl

theorem cell23_7177960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 3, 1, 2, 3].length) (baseStart_7177960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7177960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7177960 prefixEnd_7177960 := by exact prefixLift 7177960
  have htrace : WordTrace (prefixWord ++ tailWord_7177960) baseStart_7177960 baseEnd_7177960 := by
    simpa [prefixWord, tailWord_7177960, baseEnd_7177960] using wordTrace_append hprefix tailTrace_7177960
  have hstable : (prefixWord ++ tailWord_7177960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7177960).length < 2 ^ (prefixWord ++ tailWord_7177960).sum := by decide
  have hdescent : baseEnd_7177960 < baseStart_7177960 := by decide
  rcases family_descends (prefixWord ++ tailWord_7177960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7177974 : List Nat := [5, 1, 1, 1, 1, 3, 2, 4, 1, 2, 2]
def baseStart_7177974 : Nat := 118140960795 + 7177974 * 2 ^ 59
def prefixEnd_7177974 : Nat := 4983230072969 + 3 ^ 40 * 7177974 * 2
def baseEnd_7177974 : Nat := 3685750787476004377414105

theorem tailTrace_7177974 : CollatzResearch.WordTrace tailWord_7177974 prefixEnd_7177974 3685750787476004377414105 := by
  unfold tailWord_7177974
  simp only [CollatzResearch.WordTrace]
  refine ⟨16362638731089598325337311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 174534813131622382136931317 16362638731089598325337311)
  ·
    refine ⟨24543958096634397488005967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16362638731089598325337311 24543958096634397488005967)
    ·
      refine ⟨36815937144951596232008951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24543958096634397488005967 36815937144951596232008951)
      ·
        refine ⟨55223905717427394348013427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36815937144951596232008951 55223905717427394348013427)
        ·
          refine ⟨82835858576141091522020141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55223905717427394348013427 82835858576141091522020141)
          ·
            refine ⟨31063446966052909320757553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82835858576141091522020141 31063446966052909320757553)
            ·
              refine ⟨23297585224539681990568165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31063446966052909320757553 23297585224539681990568165)
              ·
                refine ⟨4368297229601190373231531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23297585224539681990568165 4368297229601190373231531)
                ·
                  refine ⟨6552445844401785559847297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4368297229601190373231531 6552445844401785559847297)
                  ·
                    refine ⟨4914334383301339169885473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6552445844401785559847297 4914334383301339169885473)
                    ·
                      refine ⟨3685750787476004377414105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4914334383301339169885473 3685750787476004377414105)
                      ·
                        rfl

theorem cell23_7177974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 4, 1, 2, 2].length) (baseStart_7177974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7177974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7177974 prefixEnd_7177974 := by exact prefixLift 7177974
  have htrace : WordTrace (prefixWord ++ tailWord_7177974) baseStart_7177974 baseEnd_7177974 := by
    simpa [prefixWord, tailWord_7177974, baseEnd_7177974] using wordTrace_append hprefix tailTrace_7177974
  have hstable : (prefixWord ++ tailWord_7177974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7177974).length < 2 ^ (prefixWord ++ tailWord_7177974).sum := by decide
  have hdescent : baseEnd_7177974 < baseStart_7177974 := by decide
  rcases family_descends (prefixWord ++ tailWord_7177974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7177983 : List Nat := [1, 1, 2, 2, 1, 3, 2, 1, 5, 3, 2]
def baseStart_7177983 : Nat := 118140960795 + 7177983 * 2 ^ 59
def prefixEnd_7177983 : Nat := 4983230072969 + 3 ^ 40 * 7177983 * 2
def baseEnd_7177983 : Nat := 3685755408801894842201563

theorem tailTrace_7177983 : CollatzResearch.WordTrace tailWord_7177983 prefixEnd_7177983 3685755408801894842201563 := by
  unfold tailWord_7177983
  simp only [CollatzResearch.WordTrace]
  refine ⟨261802547954400967742474603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174535031969600645161649735 261802547954400967742474603)
  ·
    refine ⟨392703821931601451613711905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261802547954400967742474603 392703821931601451613711905)
    ·
      refine ⟨294527866448701088710283929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 392703821931601451613711905 294527866448701088710283929)
      ·
        refine ⟨220895899836525816532712947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 294527866448701088710283929 220895899836525816532712947)
        ·
          refine ⟨331343849754788724799069421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220895899836525816532712947 331343849754788724799069421)
          ·
            refine ⟨124253943658045771799651033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 331343849754788724799069421 124253943658045771799651033)
            ·
              refine ⟨93190457743534328849738275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124253943658045771799651033 93190457743534328849738275)
              ·
                refine ⟨139785686615301493274607413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93190457743534328849738275 139785686615301493274607413)
                ·
                  refine ⟨13104908120184514994494445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 139785686615301493274607413 13104908120184514994494445)
                  ·
                    refine ⟨4914340545069193122935417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13104908120184514994494445 4914340545069193122935417)
                    ·
                      refine ⟨3685755408801894842201563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4914340545069193122935417 3685755408801894842201563)
                      ·
                        rfl

theorem cell23_7177983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 5, 3, 2].length) (baseStart_7177983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7177983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7177983 prefixEnd_7177983 := by exact prefixLift 7177983
  have htrace : WordTrace (prefixWord ++ tailWord_7177983) baseStart_7177983 baseEnd_7177983 := by
    simpa [prefixWord, tailWord_7177983, baseEnd_7177983] using wordTrace_append hprefix tailTrace_7177983
  have hstable : (prefixWord ++ tailWord_7177983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7177983).length < 2 ^ (prefixWord ++ tailWord_7177983).sum := by decide
  have hdescent : baseEnd_7177983 < baseStart_7177983 := by decide
  rcases family_descends (prefixWord ++ tailWord_7177983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7177996 : List Nat := [2, 2, 1, 2, 2, 1, 2, 2, 2, 3, 4]
def baseStart_7177996 : Nat := 118140960795 + 7177996 * 2 ^ 59
def prefixEnd_7177996 : Nat := 4983230072969 + 3 ^ 40 * 7177996 * 2
def baseEnd_7177996 : Nat := 3685762084050403291339003

theorem tailTrace_7177996 : CollatzResearch.WordTrace tailWord_7177996 prefixEnd_7177996 3685762084050403291339003 := by
  unfold tailWord_7177996
  simp only [CollatzResearch.WordTrace]
  refine ⟨130901511051676935481348921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174535348068902580641798561 130901511051676935481348921)
  ·
    refine ⟨98176133288757701611011691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130901511051676935481348921 98176133288757701611011691)
    ·
      refine ⟨147264199933136552416517537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98176133288757701611011691 147264199933136552416517537)
      ·
        refine ⟨110448149949852414312388153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147264199933136552416517537 110448149949852414312388153)
        ·
          refine ⟨82836112462389310734291115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110448149949852414312388153 82836112462389310734291115)
          ·
            refine ⟨124254168693583966101436673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82836112462389310734291115 124254168693583966101436673)
            ·
              refine ⟨93190626520187974576077505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124254168693583966101436673 93190626520187974576077505)
              ·
                refine ⟨69892969890140980932058129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93190626520187974576077505 69892969890140980932058129)
                ·
                  refine ⟨52419727417605735699043597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69892969890140980932058129 52419727417605735699043597)
                  ·
                    refine ⟨19657397781602150887141349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52419727417605735699043597 19657397781602150887141349)
                    ·
                      refine ⟨3685762084050403291339003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19657397781602150887141349 3685762084050403291339003)
                      ·
                        rfl

theorem cell23_7177996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 2, 3, 4].length) (baseStart_7177996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7177996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7177996 prefixEnd_7177996 := by exact prefixLift 7177996
  have htrace : WordTrace (prefixWord ++ tailWord_7177996) baseStart_7177996 baseEnd_7177996 := by
    simpa [prefixWord, tailWord_7177996, baseEnd_7177996] using wordTrace_append hprefix tailTrace_7177996
  have hstable : (prefixWord ++ tailWord_7177996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7177996).length < 2 ^ (prefixWord ++ tailWord_7177996).sum := by decide
  have hdescent : baseEnd_7177996 < baseStart_7177996 := by decide
  rcases family_descends (prefixWord ++ tailWord_7177996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7178041 : List Nat := [1, 2, 1, 7, 1, 2, 2, 1, 2, 1, 3]
def baseStart_7178041 : Nat := 118140960795 + 7178041 * 2 ^ 59
def prefixEnd_7178041 : Nat := 4983230072969 + 3 ^ 40 * 7178041 * 2
def baseEnd_7178041 : Nat := 3685785190679855615276297

theorem tailTrace_7178041 : CollatzResearch.WordTrace tailWord_7178041 prefixEnd_7178041 3685785190679855615276297 := by
  unfold tailWord_7178041
  simp only [CollatzResearch.WordTrace]
  refine ⟨261804663388190843648085977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174536442258793895765390651 261804663388190843648085977)
  ·
    refine ⟨196353497541143132736064483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261804663388190843648085977 196353497541143132736064483)
    ·
      refine ⟨294530246311714699104096725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196353497541143132736064483 294530246311714699104096725)
      ·
        refine ⟨6903052647930813260252267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 294530246311714699104096725 6903052647930813260252267)
        ·
          refine ⟨10354578971896219890378401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6903052647930813260252267 10354578971896219890378401)
          ·
            refine ⟨7765934228922164917783801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10354578971896219890378401 7765934228922164917783801)
            ·
              refine ⟨5824450671691623688337851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7765934228922164917783801 5824450671691623688337851)
              ·
                refine ⟨8736676007537435532506777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5824450671691623688337851 8736676007537435532506777)
                ·
                  refine ⟨6552507005653076649380083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8736676007537435532506777 6552507005653076649380083)
                  ·
                    refine ⟨9828760508479614974070125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6552507005653076649380083 9828760508479614974070125)
                    ·
                      refine ⟨3685785190679855615276297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9828760508479614974070125 3685785190679855615276297)
                      ·
                        rfl

theorem cell23_7178041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_7178041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7178041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7178041 prefixEnd_7178041 := by exact prefixLift 7178041
  have htrace : WordTrace (prefixWord ++ tailWord_7178041) baseStart_7178041 baseEnd_7178041 := by
    simpa [prefixWord, tailWord_7178041, baseEnd_7178041] using wordTrace_append hprefix tailTrace_7178041
  have hstable : (prefixWord ++ tailWord_7178041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7178041).length < 2 ^ (prefixWord ++ tailWord_7178041).sum := by decide
  have hdescent : baseEnd_7178041 < baseStart_7178041 := by decide
  rcases family_descends (prefixWord ++ tailWord_7178041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7178093 : List Nat := [1, 5, 1, 1, 1, 1, 4, 1, 1, 2, 5]
def baseStart_7178093 : Nat := 118140960795 + 7178093 * 2 ^ 59
def prefixEnd_7178093 : Nat := 4983230072969 + 3 ^ 40 * 7178093 * 2
def baseEnd_7178093 : Nat := 3685811891673889411826057

theorem tailTrace_7178093 : CollatzResearch.WordTrace tailWord_7178093 prefixEnd_7178093 3685811891673889411826057 := by
  unfold tailWord_7178093
  simp only [CollatzResearch.WordTrace]
  refine ⟨261806559984002456528978933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174537706656001637685985955 261806559984002456528978933)
  ·
    refine ⟨24544364998500230299591775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 261806559984002456528978933 24544364998500230299591775)
    ·
      refine ⟨36816547497750345449387663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24544364998500230299591775 36816547497750345449387663)
      ·
        refine ⟨55224821246625518174081495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36816547497750345449387663 55224821246625518174081495)
        ·
          refine ⟨82837231869938277261122243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55224821246625518174081495 82837231869938277261122243)
          ·
            refine ⟨124255847804907415891683365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82837231869938277261122243 124255847804907415891683365)
            ·
              refine ⟨23297971463420140479690631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 124255847804907415891683365 23297971463420140479690631)
              ·
                refine ⟨34946957195130210719535947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23297971463420140479690631 34946957195130210719535947)
                ·
                  refine ⟨52420435792695316079303921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34946957195130210719535947 52420435792695316079303921)
                  ·
                    refine ⟨39315326844521487059477941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52420435792695316079303921 39315326844521487059477941)
                    ·
                      refine ⟨3685811891673889411826057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39315326844521487059477941 3685811891673889411826057)
                      ·
                        rfl

theorem cell23_7178093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_7178093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7178093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7178093 prefixEnd_7178093 := by exact prefixLift 7178093
  have htrace : WordTrace (prefixWord ++ tailWord_7178093) baseStart_7178093 baseEnd_7178093 := by
    simpa [prefixWord, tailWord_7178093, baseEnd_7178093] using wordTrace_append hprefix tailTrace_7178093
  have hstable : (prefixWord ++ tailWord_7178093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7178093).length < 2 ^ (prefixWord ++ tailWord_7178093).sum := by decide
  have hdescent : baseEnd_7178093 < baseStart_7178093 := by decide
  rcases family_descends (prefixWord ++ tailWord_7178093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7178096 : List Nat := [2, 1, 1, 1, 4, 1, 1, 2, 2, 8]
def baseStart_7178096 : Nat := 118140960795 + 7178096 * 2 ^ 59
def prefixEnd_7178096 : Nat := 4983230072969 + 3 ^ 40 * 7178096 * 2
def baseEnd_7178096 : Nat := 1228604477371950966696181

theorem tailTrace_7178096 : CollatzResearch.WordTrace tailWord_7178096 prefixEnd_7178096 1228604477371950966696181 := by
  unfold tailWord_7178096
  simp only [CollatzResearch.WordTrace]
  refine ⟨130903334701495794020669071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174537779601994392027558761 130903334701495794020669071)
  ·
    refine ⟨196355002052243691031003607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130903334701495794020669071 196355002052243691031003607)
    ·
      refine ⟨294532503078365536546505411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196355002052243691031003607 294532503078365536546505411)
      ·
        refine ⟨441798754617548304819758117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294532503078365536546505411 441798754617548304819758117)
        ·
          refine ⟨82837266490790307153704647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 441798754617548304819758117 82837266490790307153704647)
          ·
            refine ⟨124255899736185460730556971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82837266490790307153704647 124255899736185460730556971)
            ·
              refine ⟨186383849604278191095835457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124255899736185460730556971 186383849604278191095835457)
              ·
                refine ⟨139787887203208643321876593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 186383849604278191095835457 139787887203208643321876593)
                ·
                  refine ⟨104840915402406482491407445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139787887203208643321876593 104840915402406482491407445)
                  ·
                    refine ⟨1228604477371950966696181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 104840915402406482491407445 1228604477371950966696181)
                    ·
                      rfl

theorem cell23_7178096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 2, 8].length) (baseStart_7178096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7178096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7178096 prefixEnd_7178096 := by exact prefixLift 7178096
  have htrace : WordTrace (prefixWord ++ tailWord_7178096) baseStart_7178096 baseEnd_7178096 := by
    simpa [prefixWord, tailWord_7178096, baseEnd_7178096] using wordTrace_append hprefix tailTrace_7178096
  have hstable : (prefixWord ++ tailWord_7178096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7178096).length < 2 ^ (prefixWord ++ tailWord_7178096).sum := by decide
  have hdescent : baseEnd_7178096 < baseStart_7178096 := by decide
  rcases family_descends (prefixWord ++ tailWord_7178096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7178120 : List Nat := [2, 1, 3, 3, 3, 1, 1, 1, 1, 3, 4]
def baseStart_7178120 : Nat := 118140960795 + 7178120 * 2 ^ 59
def prefixEnd_7178120 : Nat := 4983230072969 + 3 ^ 40 * 7178120 * 2
def baseEnd_7178120 : Nat := 3685825755651560806188433

theorem tailTrace_7178120 : CollatzResearch.WordTrace tailWord_7178120 prefixEnd_7178120 3685825755651560806188433 := by
  unfold tailWord_7178120
  simp only [CollatzResearch.WordTrace]
  refine ⟨130903772377452320070105907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174538363169936426760141209 130903772377452320070105907)
  ·
    refine ⟨196355658566178480105158861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130903772377452320070105907 196355658566178480105158861)
    ·
      refine ⟨73633371962316930039434573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196355658566178480105158861 73633371962316930039434573)
      ·
        refine ⟨27612514485868848764787965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73633371962316930039434573 27612514485868848764787965)
        ·
          refine ⟨10354692932200818286795487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27612514485868848764787965 10354692932200818286795487)
          ·
            refine ⟨15532039398301227430193231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10354692932200818286795487 15532039398301227430193231)
            ·
              refine ⟨23298059097451841145289847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15532039398301227430193231 23298059097451841145289847)
              ·
                refine ⟨34947088646177761717934771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23298059097451841145289847 34947088646177761717934771)
                ·
                  refine ⟨52420632969266642576902157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34947088646177761717934771 52420632969266642576902157)
                  ·
                    refine ⟨19657737363474990966338309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52420632969266642576902157 19657737363474990966338309)
                    ·
                      refine ⟨3685825755651560806188433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19657737363474990966338309 3685825755651560806188433)
                      ·
                        rfl

theorem cell23_7178120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_7178120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7178120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7178120 prefixEnd_7178120 := by exact prefixLift 7178120
  have htrace : WordTrace (prefixWord ++ tailWord_7178120) baseStart_7178120 baseEnd_7178120 := by
    simpa [prefixWord, tailWord_7178120, baseEnd_7178120] using wordTrace_append hprefix tailTrace_7178120
  have hstable : (prefixWord ++ tailWord_7178120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7178120).length < 2 ^ (prefixWord ++ tailWord_7178120).sum := by decide
  have hdescent : baseEnd_7178120 < baseStart_7178120 := by decide
  rcases family_descends (prefixWord ++ tailWord_7178120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7178170 : List Nat := [3, 1, 1, 1, 2, 1, 2, 3, 5, 1, 3]
def baseStart_7178170 : Nat := 118140960795 + 7178170 * 2 ^ 59
def prefixEnd_7178170 : Nat := 4983230072969 + 3 ^ 40 * 7178170 * 2
def baseEnd_7178170 : Nat := 3685851429684285610563203

theorem tailTrace_7178170 : CollatzResearch.WordTrace tailWord_7178170 prefixEnd_7178170 3685851429684285610563203 := by
  unfold tailWord_7178170
  simp only [CollatzResearch.WordTrace]
  refine ⟨65452342101180874669882991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174539578936482332453021309 65452342101180874669882991)
  ·
    refine ⟨98178513151771312004824487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65452342101180874669882991 98178513151771312004824487)
    ·
      refine ⟨147267769727656968007236731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98178513151771312004824487 147267769727656968007236731)
      ·
        refine ⟨220901654591485452010855097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147267769727656968007236731 220901654591485452010855097)
        ·
          refine ⟨165676240943614089008141323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220901654591485452010855097 165676240943614089008141323)
          ·
            refine ⟨248514361415421133512211985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165676240943614089008141323 248514361415421133512211985)
            ·
              refine ⟨186385771061565850134158989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 248514361415421133512211985 186385771061565850134158989)
              ·
                refine ⟨69894664148087193800309621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 186385771061565850134158989 69894664148087193800309621)
                ·
                  refine ⟨6552624763883174418779027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69894664148087193800309621 6552624763883174418779027)
                  ·
                    refine ⟨9828937145824761628168541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6552624763883174418779027 9828937145824761628168541)
                    ·
                      refine ⟨3685851429684285610563203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9828937145824761628168541 3685851429684285610563203)
                      ·
                        rfl

theorem cell23_7178170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 5, 1, 3].length) (baseStart_7178170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7178170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7178170 prefixEnd_7178170 := by exact prefixLift 7178170
  have htrace : WordTrace (prefixWord ++ tailWord_7178170) baseStart_7178170 baseEnd_7178170 := by
    simpa [prefixWord, tailWord_7178170, baseEnd_7178170] using wordTrace_append hprefix tailTrace_7178170
  have hstable : (prefixWord ++ tailWord_7178170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7178170).length < 2 ^ (prefixWord ++ tailWord_7178170).sum := by decide
  have hdescent : baseEnd_7178170 < baseStart_7178170 := by decide
  rcases family_descends (prefixWord ++ tailWord_7178170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7178190 : List Nat := [4, 1, 1, 1, 2, 2, 1, 5, 1, 5]
def baseStart_7178190 : Nat := 118140960795 + 7178190 * 2 ^ 59
def prefixEnd_7178190 : Nat := 4983230072969 + 3 ^ 40 * 7178190 * 2
def baseEnd_7178190 : Nat := 1228620566432458510771037

theorem tailTrace_7178190 : CollatzResearch.WordTrace tailWord_7178190 prefixEnd_7178190 1228620566432458510771037 := by
  unfold tailWord_7178190
  simp only [CollatzResearch.WordTrace]
  refine ⟨32726262233081380261907503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174540065243100694730173349 32726262233081380261907503)
  ·
    refine ⟨49089393349622070392861255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32726262233081380261907503 49089393349622070392861255)
    ·
      refine ⟨73634090024433105589291883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49089393349622070392861255 73634090024433105589291883)
      ·
        refine ⟨110451135036649658383937825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73634090024433105589291883 110451135036649658383937825)
        ·
          refine ⟨82838351277487243787953369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110451135036649658383937825 82838351277487243787953369)
          ·
            refine ⟨62128763458115432840965027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82838351277487243787953369 62128763458115432840965027)
            ·
              refine ⟨93193145187173149261447541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62128763458115432840965027 93193145187173149261447541)
              ·
                refine ⟨8736857361297482743260707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 93193145187173149261447541 8736857361297482743260707)
                ·
                  refine ⟨13105286041946224114891061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8736857361297482743260707 13105286041946224114891061)
                  ·
                    refine ⟨1228620566432458510771037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13105286041946224114891061 1228620566432458510771037)
                    ·
                      rfl

theorem cell23_7178190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 5, 1, 5].length) (baseStart_7178190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7178190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7178190 prefixEnd_7178190 := by exact prefixLift 7178190
  have htrace : WordTrace (prefixWord ++ tailWord_7178190) baseStart_7178190 baseEnd_7178190 := by
    simpa [prefixWord, tailWord_7178190, baseEnd_7178190] using wordTrace_append hprefix tailTrace_7178190
  have hstable : (prefixWord ++ tailWord_7178190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7178190).length < 2 ^ (prefixWord ++ tailWord_7178190).sum := by decide
  have hdescent : baseEnd_7178190 < baseStart_7178190 := by decide
  rcases family_descends (prefixWord ++ tailWord_7178190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7178197 : List Nat := [1, 3, 2, 3, 2, 1, 1, 1, 4, 3, 2]
def baseStart_7178197 : Nat := 118140960795 + 7178197 * 2 ^ 59
def prefixEnd_7178197 : Nat := 4983230072969 + 3 ^ 40 * 7178197 * 2
def baseEnd_7178197 : Nat := 3685865293661957004925579

theorem tailTrace_7178197 : CollatzResearch.WordTrace tailWord_7178197 prefixEnd_7178197 3685865293661957004925579 := by
  unfold tailWord_7178197
  simp only [CollatzResearch.WordTrace]
  refine ⟨261810353175625682290764845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174540235450417121527176563 261810353175625682290764845)
  ·
    refine ⟨98178882440859630859036817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261810353175625682290764845 98178882440859630859036817)
    ·
      refine ⟨73634161830644723144277613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98178882440859630859036817 73634161830644723144277613)
      ·
        refine ⟨27612810686491771179104105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73634161830644723144277613 27612810686491771179104105)
        ·
          refine ⟨20709608014868828384328079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27612810686491771179104105 20709608014868828384328079)
          ·
            refine ⟨31064412022303242576492119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20709608014868828384328079 31064412022303242576492119)
            ·
              refine ⟨46596618033454863864738179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31064412022303242576492119 46596618033454863864738179)
              ·
                refine ⟨69894927050182295797107269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46596618033454863864738179 69894927050182295797107269)
                ·
                  refine ⟨13105298821909180461957613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69894927050182295797107269 13105298821909180461957613)
                  ·
                    refine ⟨4914487058215942673234105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13105298821909180461957613 4914487058215942673234105)
                    ·
                      refine ⟨3685865293661957004925579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4914487058215942673234105 3685865293661957004925579)
                      ·
                        rfl

theorem cell23_7178197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 4, 3, 2].length) (baseStart_7178197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7178197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7178197 prefixEnd_7178197 := by exact prefixLift 7178197
  have htrace : WordTrace (prefixWord ++ tailWord_7178197) baseStart_7178197 baseEnd_7178197 := by
    simpa [prefixWord, tailWord_7178197, baseEnd_7178197] using wordTrace_append hprefix tailTrace_7178197
  have hstable : (prefixWord ++ tailWord_7178197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7178197).length < 2 ^ (prefixWord ++ tailWord_7178197).sum := by decide
  have hdescent : baseEnd_7178197 < baseStart_7178197 := by decide
  rcases family_descends (prefixWord ++ tailWord_7178197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7178198 : List Nat := [5, 2, 1, 1, 3, 1, 3, 2, 1, 4]
def baseStart_7178198 : Nat := 118140960795 + 7178198 * 2 ^ 59
def prefixEnd_7178198 : Nat := 4983230072969 + 3 ^ 40 * 7178198 * 2
def baseEnd_7178198 : Nat := 1228621935714203833671025

theorem tailTrace_7178198 : CollatzResearch.WordTrace tailWord_7178198 prefixEnd_7178198 1228621935714203833671025 := by
  unfold tailWord_7178198
  simp only [CollatzResearch.WordTrace]
  refine ⟨16363149353038878716346953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 174540259765748039641034165 16363149353038878716346953)
  ·
    refine ⟨12272362014779159037260215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16363149353038878716346953 12272362014779159037260215)
    ·
      refine ⟨18408543022168738555890323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12272362014779159037260215 18408543022168738555890323)
      ·
        refine ⟨27612814533253107833835485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18408543022168738555890323 27612814533253107833835485)
        ·
          refine ⟨10354805449969915437688307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27612814533253107833835485 10354805449969915437688307)
          ·
            refine ⟨15532208174954873156532461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10354805449969915437688307 15532208174954873156532461)
            ·
              refine ⟨5824578065608077433699673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15532208174954873156532461 5824578065608077433699673)
              ·
                refine ⟨4368433549206058075274755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5824578065608077433699673 4368433549206058075274755)
                ·
                  refine ⟨6552650323809087112912133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4368433549206058075274755 6552650323809087112912133)
                  ·
                    refine ⟨1228621935714203833671025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6552650323809087112912133 1228621935714203833671025)
                    ·
                      rfl

theorem cell23_7178198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_7178198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7178198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7178198 prefixEnd_7178198 := by exact prefixLift 7178198
  have htrace : WordTrace (prefixWord ++ tailWord_7178198) baseStart_7178198 baseEnd_7178198 := by
    simpa [prefixWord, tailWord_7178198, baseEnd_7178198] using wordTrace_append hprefix tailTrace_7178198
  have hstable : (prefixWord ++ tailWord_7178198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7178198).length < 2 ^ (prefixWord ++ tailWord_7178198).sum := by decide
  have hdescent : baseEnd_7178198 < baseStart_7178198 := by decide
  rcases family_descends (prefixWord ++ tailWord_7178198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7178223 : List Nat := [1, 1, 2, 1, 4, 2, 1, 3, 1, 1, 6]
def baseStart_7178223 : Nat := 118140960795 + 7178223 * 2 ^ 59
def prefixEnd_7178223 : Nat := 4983230072969 + 3 ^ 40 * 7178223 * 2
def baseEnd_7178223 : Nat := 3685878644158973903200459

theorem tailTrace_7178223 : CollatzResearch.WordTrace tailWord_7178223 prefixEnd_7178223 3685878644158973903200459 := by
  unfold tailWord_7178223
  simp only [CollatzResearch.WordTrace]
  refine ⟨261811301473531488731211323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174540867649020992487474215 261811301473531488731211323)
  ·
    refine ⟨392716952210297233096816985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261811301473531488731211323 392716952210297233096816985)
    ·
      refine ⟨294537714157722924822612739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 392716952210297233096816985 294537714157722924822612739)
      ·
        refine ⟨441806571236584387233919109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294537714157722924822612739 441806571236584387233919109)
        ·
          refine ⟨82838732106859572606359833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 441806571236584387233919109 82838732106859572606359833)
          ·
            refine ⟨62129049080144679454769875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82838732106859572606359833 62129049080144679454769875)
            ·
              refine ⟨93193573620217019182154813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62129049080144679454769875 93193573620217019182154813)
              ·
                refine ⟨34947590107581382193308055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93193573620217019182154813 34947590107581382193308055)
                ·
                  refine ⟨52421385161372073289962083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34947590107581382193308055 52421385161372073289962083)
                  ·
                    refine ⟨78632077742058109934943125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52421385161372073289962083 78632077742058109934943125)
                    ·
                      refine ⟨3685878644158973903200459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78632077742058109934943125 3685878644158973903200459)
                      ·
                        rfl

theorem cell23_7178223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 3, 1, 1, 6].length) (baseStart_7178223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7178223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7178223 prefixEnd_7178223 := by exact prefixLift 7178223
  have htrace : WordTrace (prefixWord ++ tailWord_7178223) baseStart_7178223 baseEnd_7178223 := by
    simpa [prefixWord, tailWord_7178223, baseEnd_7178223] using wordTrace_append hprefix tailTrace_7178223
  have hstable : (prefixWord ++ tailWord_7178223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7178223).length < 2 ^ (prefixWord ++ tailWord_7178223).sum := by decide
  have hdescent : baseEnd_7178223 < baseStart_7178223 := by decide
  rcases family_descends (prefixWord ++ tailWord_7178223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7178227 : List Nat := [1, 1, 1, 2, 2, 2, 1, 6, 3, 2, 2]
def baseStart_7178227 : Nat := 118140960795 + 7178227 * 2 ^ 59
def prefixEnd_7178227 : Nat := 4983230072969 + 3 ^ 40 * 7178227 * 2
def baseEnd_7178227 : Nat := 3685880698081591887550441

theorem tailTrace_7178227 : CollatzResearch.WordTrace tailWord_7178227 prefixEnd_7178227 3685880698081591887550441 := by
  unfold tailWord_7178227
  simp only [CollatzResearch.WordTrace]
  refine ⟨261811447365516997414356935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174540964910344664942904623 261811447365516997414356935)
  ·
    refine ⟨392717171048275496121535403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261811447365516997414356935 392717171048275496121535403)
    ·
      refine ⟨589075756572413244182303105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392717171048275496121535403 589075756572413244182303105)
      ·
        refine ⟨441806817429309933136727329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 589075756572413244182303105 441806817429309933136727329)
        ·
          refine ⟨331355113071982449852545497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 441806817429309933136727329 331355113071982449852545497)
          ·
            refine ⟨248516334803986837389409123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 331355113071982449852545497 248516334803986837389409123)
            ·
              refine ⟨372774502205980256084113685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248516334803986837389409123 372774502205980256084113685)
              ·
                refine ⟨17473804790905324503942829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 372774502205980256084113685 17473804790905324503942829)
                ·
                  refine ⟨6552676796589496688978561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17473804790905324503942829 6552676796589496688978561)
                  ·
                    refine ⟨4914507597442122516733921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6552676796589496688978561 4914507597442122516733921)
                    ·
                      refine ⟨3685880698081591887550441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4914507597442122516733921 3685880698081591887550441)
                      ·
                        rfl

theorem cell23_7178227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 6, 3, 2, 2].length) (baseStart_7178227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7178227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7178227 prefixEnd_7178227 := by exact prefixLift 7178227
  have htrace : WordTrace (prefixWord ++ tailWord_7178227) baseStart_7178227 baseEnd_7178227 := by
    simpa [prefixWord, tailWord_7178227, baseEnd_7178227] using wordTrace_append hprefix tailTrace_7178227
  have hstable : (prefixWord ++ tailWord_7178227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7178227).length < 2 ^ (prefixWord ++ tailWord_7178227).sum := by decide
  have hdescent : baseEnd_7178227 < baseStart_7178227 := by decide
  rcases family_descends (prefixWord ++ tailWord_7178227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7178233 : List Nat := [1, 2, 1, 3, 1, 4, 2, 9]
def baseStart_7178233 : Nat := 118140960795 + 7178233 * 2 ^ 59
def prefixEnd_7178233 : Nat := 4983230072969 + 3 ^ 40 * 7178233 * 2
def baseEnd_7178233 : Nat := 136514214035759957928719

theorem tailTrace_7178233 : CollatzResearch.WordTrace tailWord_7178233 prefixEnd_7178233 136514214035759957928719 := by
  unfold tailWord_7178233
  simp only [CollatzResearch.WordTrace]
  refine ⟨261811666203495260439075353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174541110802330173626050235 261811666203495260439075353)
  ·
    refine ⟨196358749652621445329306515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261811666203495260439075353 196358749652621445329306515)
    ·
      refine ⟨294538124478932167993959773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196358749652621445329306515 294538124478932167993959773)
      ·
        refine ⟨110451796679599562997734915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 294538124478932167993959773 110451796679599562997734915)
        ·
          refine ⟨165677695019399344496602373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110451796679599562997734915 165677695019399344496602373)
          ·
            refine ⟨31064567816137377093112945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 165677695019399344496602373 31064567816137377093112945)
            ·
              refine ⟨23298425862103032819834709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31064567816137377093112945 23298425862103032819834709)
              ·
                refine ⟨136514214035759957928719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23298425862103032819834709 136514214035759957928719)
                ·
                  rfl

theorem cell23_7178233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 9].length) (baseStart_7178233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7178233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7178233 prefixEnd_7178233 := by exact prefixLift 7178233
  have htrace : WordTrace (prefixWord ++ tailWord_7178233) baseStart_7178233 baseEnd_7178233 := by
    simpa [prefixWord, tailWord_7178233, baseEnd_7178233] using wordTrace_append hprefix tailTrace_7178233
  have hstable : (prefixWord ++ tailWord_7178233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7178233).length < 2 ^ (prefixWord ++ tailWord_7178233).sum := by decide
  have hdescent : baseEnd_7178233 < baseStart_7178233 := by decide
  rcases family_descends (prefixWord ++ tailWord_7178233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7178247 : List Nat := [1, 1, 4, 3, 1, 4, 1, 1, 1, 1, 5]
def baseStart_7178247 : Nat := 118140960795 + 7178247 * 2 ^ 59
def prefixEnd_7178247 : Nat := 4983230072969 + 3 ^ 40 * 7178247 * 2
def baseEnd_7178247 : Nat := 3685890967694681809300349

theorem tailTrace_7178247 : CollatzResearch.WordTrace tailWord_7178247 prefixEnd_7178247 3685890967694681809300349 := by
  unfold tailWord_7178247
  simp only [CollatzResearch.WordTrace]
  refine ⟨261812176825444540830084995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174541451216963027220056663 261812176825444540830084995)
  ·
    refine ⟨392718265238166811245127493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261812176825444540830084995 392718265238166811245127493)
    ·
      refine ⟨73634674732156277108461405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 392718265238166811245127493 73634674732156277108461405)
      ·
        refine ⟨27613003024558603915673027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73634674732156277108461405 27613003024558603915673027)
        ·
          refine ⟨41419504536837905873509541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27613003024558603915673027 41419504536837905873509541)
          ·
            refine ⟨7766157100657107351283039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41419504536837905873509541 7766157100657107351283039)
            ·
              refine ⟨11649235650985661026924559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7766157100657107351283039 11649235650985661026924559)
              ·
                refine ⟨17473853476478491540386839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11649235650985661026924559 17473853476478491540386839)
                ·
                  refine ⟨26210780214717737310580259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17473853476478491540386839 26210780214717737310580259)
                  ·
                    refine ⟨39316170322076605965870389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26210780214717737310580259 39316170322076605965870389)
                    ·
                      refine ⟨3685890967694681809300349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39316170322076605965870389 3685890967694681809300349)
                      ·
                        rfl

theorem cell23_7178247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_7178247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7178247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7178247 prefixEnd_7178247 := by exact prefixLift 7178247
  have htrace : WordTrace (prefixWord ++ tailWord_7178247) baseStart_7178247 baseEnd_7178247 := by
    simpa [prefixWord, tailWord_7178247, baseEnd_7178247] using wordTrace_append hprefix tailTrace_7178247
  have hstable : (prefixWord ++ tailWord_7178247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7178247).length < 2 ^ (prefixWord ++ tailWord_7178247).sum := by decide
  have hdescent : baseEnd_7178247 < baseStart_7178247 := by decide
  rcases family_descends (prefixWord ++ tailWord_7178247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7178250 : List Nat := [3, 1, 2, 2, 5, 10]
def baseStart_7178250 : Nat := 118140960795 + 7178250 * 2 ^ 59
def prefixEnd_7178250 : Nat := 4983230072969 + 3 ^ 40 * 7178250 * 2
def baseEnd_7178250 : Nat := 15168281926488252253345

theorem tailTrace_7178250 : CollatzResearch.WordTrace tailWord_7178250 prefixEnd_7178250 15168281926488252253345 := by
  unfold tailWord_7178250
  simp only [CollatzResearch.WordTrace]
  refine ⟨65453071561108418085611051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174541524162955781561629469 65453071561108418085611051)
  ·
    refine ⟨98179607341662627128416577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65453071561108418085611051 98179607341662627128416577)
    ·
      refine ⟨73634705506246970346312433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98179607341662627128416577 73634705506246970346312433)
      ·
        refine ⟨55226029129685227759734325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73634705506246970346312433 55226029129685227759734325)
        ·
          refine ⟨5177440230907990102475093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55226029129685227759734325 5177440230907990102475093)
          ·
            refine ⟨15168281926488252253345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5177440230907990102475093 15168281926488252253345)
            ·
              rfl

theorem cell23_7178250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 10].length) (baseStart_7178250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7178250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7178250 prefixEnd_7178250 := by exact prefixLift 7178250
  have htrace : WordTrace (prefixWord ++ tailWord_7178250) baseStart_7178250 baseEnd_7178250 := by
    simpa [prefixWord, tailWord_7178250, baseEnd_7178250] using wordTrace_append hprefix tailTrace_7178250
  have hstable : (prefixWord ++ tailWord_7178250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7178250).length < 2 ^ (prefixWord ++ tailWord_7178250).sum := by decide
  have hdescent : baseEnd_7178250 < baseStart_7178250 := by decide
  rcases family_descends (prefixWord ++ tailWord_7178250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7178277 : List Nat := [1, 3, 1, 2, 2, 4, 2, 1, 1, 3, 3]
def baseStart_7178277 : Nat := 118140960795 + 7178277 * 2 ^ 59
def prefixEnd_7178277 : Nat := 4983230072969 + 3 ^ 40 * 7178277 * 2
def baseEnd_7178277 : Nat := 3685906372114316691925211

theorem tailTrace_7178277 : CollatzResearch.WordTrace tailWord_7178277 prefixEnd_7178277 3685906372114316691925211 := by
  unfold tailWord_7178277
  simp only [CollatzResearch.WordTrace]
  refine ⟨261813271015335855953677085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174542180676890570635784723 261813271015335855953677085)
  ·
    refine ⟨98179976630750945982628907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261813271015335855953677085 98179976630750945982628907)
    ·
      refine ⟨147269964946126418973943361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98179976630750945982628907 147269964946126418973943361)
      ·
        refine ⟨110452473709594814230457521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147269964946126418973943361 110452473709594814230457521)
        ·
          refine ⟨82839355282196110672843141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110452473709594814230457521 82839355282196110672843141)
          ·
            refine ⟨15532379115411770751158089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82839355282196110672843141 15532379115411770751158089)
            ·
              refine ⟨11649284336558828063368567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15532379115411770751158089 11649284336558828063368567)
              ·
                refine ⟨17473926504838242095052851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11649284336558828063368567 17473926504838242095052851)
                ·
                  refine ⟨26210889757257363142579277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17473926504838242095052851 26210889757257363142579277)
                  ·
                    refine ⟨9829083658971511178467229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26210889757257363142579277 9829083658971511178467229)
                    ·
                      refine ⟨3685906372114316691925211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9829083658971511178467229 3685906372114316691925211)
                      ·
                        rfl

theorem cell23_7178277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 1, 1, 3, 3].length) (baseStart_7178277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7178277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7178277 prefixEnd_7178277 := by exact prefixLift 7178277
  have htrace : WordTrace (prefixWord ++ tailWord_7178277) baseStart_7178277 baseEnd_7178277 := by
    simpa [prefixWord, tailWord_7178277, baseEnd_7178277] using wordTrace_append hprefix tailTrace_7178277
  have hstable : (prefixWord ++ tailWord_7178277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7178277).length < 2 ^ (prefixWord ++ tailWord_7178277).sum := by decide
  have hdescent : baseEnd_7178277 < baseStart_7178277 := by decide
  rcases family_descends (prefixWord ++ tailWord_7178277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7178294 : List Nat := [5, 1, 2, 1, 1, 1, 2, 2, 4, 1, 3]
def baseStart_7178294 : Nat := 118140960795 + 7178294 * 2 ^ 59
def prefixEnd_7178294 : Nat := 4983230072969 + 3 ^ 40 * 7178294 * 2
def baseEnd_7178294 : Nat := 3685915101285443125412633

theorem tailTrace_7178294 : CollatzResearch.WordTrace tailWord_7178294 prefixEnd_7178294 3685915101285443125412633 := by
  unfold tailWord_7178294
  simp only [CollatzResearch.WordTrace]
  refine ⟨16363368191017141741065371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 174542594037516178571363957 16363368191017141741065371)
  ·
    refine ⟨24545052286525712611598057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16363368191017141741065371 24545052286525712611598057)
    ·
      refine ⟨18408789214894284458698543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24545052286525712611598057 18408789214894284458698543)
      ·
        refine ⟨27613183822341426688047815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18408789214894284458698543 27613183822341426688047815)
        ·
          refine ⟨41419775733512140032071723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27613183822341426688047815 41419775733512140032071723)
          ·
            refine ⟨62129663600268210048107585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41419775733512140032071723 62129663600268210048107585)
            ·
              refine ⟨46597247700201157536080689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62129663600268210048107585 46597247700201157536080689)
              ·
                refine ⟨34947935775150868152060517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46597247700201157536080689 34947935775150868152060517)
                ·
                  refine ⟨6552737957840787778511347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34947935775150868152060517 6552737957840787778511347)
                  ·
                    refine ⟨9829106936761181667767021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6552737957840787778511347 9829106936761181667767021)
                    ·
                      refine ⟨3685915101285443125412633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9829106936761181667767021 3685915101285443125412633)
                      ·
                        rfl

theorem cell23_7178294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_7178294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7178294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7178294 prefixEnd_7178294 := by exact prefixLift 7178294
  have htrace : WordTrace (prefixWord ++ tailWord_7178294) baseStart_7178294 baseEnd_7178294 := by
    simpa [prefixWord, tailWord_7178294, baseEnd_7178294] using wordTrace_append hprefix tailTrace_7178294
  have hstable : (prefixWord ++ tailWord_7178294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7178294).length < 2 ^ (prefixWord ++ tailWord_7178294).sum := by decide
  have hdescent : baseEnd_7178294 < baseStart_7178294 := by decide
  rcases family_descends (prefixWord ++ tailWord_7178294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7178304 : List Nat := [2, 1, 1, 2, 2, 5, 1, 3, 1, 3, 2]
def baseStart_7178304 : Nat := 118140960795 + 7178304 * 2 ^ 59
def prefixEnd_7178304 : Nat := 4983230072969 + 3 ^ 40 * 7178304 * 2
def baseEnd_7178304 : Nat := 3685920236091988086287587

theorem tailTrace_7178304 : CollatzResearch.WordTrace tailWord_7178304 prefixEnd_7178304 3685920236091988086287587 := by
  unfold tailWord_7178304
  simp only [CollatzResearch.WordTrace]
  refine ⟨130907127893119019782454983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174542837190825359709939977 130907127893119019782454983)
  ·
    refine ⟨196360691839678529673682475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130907127893119019782454983 196360691839678529673682475)
    ·
      refine ⟨294541037759517794510523713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196360691839678529673682475 294541037759517794510523713)
      ·
        refine ⟨220905778319638345882892785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 294541037759517794510523713 220905778319638345882892785)
        ·
          refine ⟨165679333739728759412169589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220905778319638345882892785 165679333739728759412169589)
          ·
            refine ⟨15532437538099571194890899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 165679333739728759412169589 15532437538099571194890899)
            ·
              refine ⟨23298656307149356792336349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15532437538099571194890899 23298656307149356792336349)
              ·
                refine ⟨8736996115181008797126131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23298656307149356792336349 8736996115181008797126131)
                ·
                  refine ⟨13105494172771513195689197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8736996115181008797126131 13105494172771513195689197)
                  ·
                    refine ⟨4914560314789317448383449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13105494172771513195689197 4914560314789317448383449)
                    ·
                      refine ⟨3685920236091988086287587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4914560314789317448383449 3685920236091988086287587)
                      ·
                        rfl

theorem cell23_7178304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 3, 1, 3, 2].length) (baseStart_7178304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7178304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7178304 prefixEnd_7178304 := by exact prefixLift 7178304
  have htrace : WordTrace (prefixWord ++ tailWord_7178304) baseStart_7178304 baseEnd_7178304 := by
    simpa [prefixWord, tailWord_7178304, baseEnd_7178304] using wordTrace_append hprefix tailTrace_7178304
  have hstable : (prefixWord ++ tailWord_7178304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7178304).length < 2 ^ (prefixWord ++ tailWord_7178304).sum := by decide
  have hdescent : baseEnd_7178304 < baseStart_7178304 := by decide
  rcases family_descends (prefixWord ++ tailWord_7178304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7178330 : List Nat := [3, 1, 1, 2, 1, 1, 3, 3, 2, 2, 4]
def baseStart_7178330 : Nat := 118140960795 + 7178330 * 2 ^ 59
def prefixEnd_7178330 : Nat := 4983230072969 + 3 ^ 40 * 7178330 * 2
def baseEnd_7178330 : Nat := 3685933586589004984562467

theorem tailTrace_7178330 : CollatzResearch.WordTrace tailWord_7178330 prefixEnd_7178330 3685933586589004984562467 := by
  unfold tailWord_7178330
  simp only [CollatzResearch.WordTrace]
  refine ⟨65453801021035961501339111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174543469389429230670237629 65453801021035961501339111)
  ·
    refine ⟨98180701531553942252008667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65453801021035961501339111 98180701531553942252008667)
    ·
      refine ⟨147271052297330913378013001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98180701531553942252008667 147271052297330913378013001)
      ·
        refine ⟨110453289222998185033509751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147271052297330913378013001 110453289222998185033509751)
        ·
          refine ⟨165679933834497277550264627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110453289222998185033509751 165679933834497277550264627)
          ·
            refine ⟨248519900751745916325396941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165679933834497277550264627 248519900751745916325396941)
            ·
              refine ⟨93194962781904718622023853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 248519900751745916325396941 93194962781904718622023853)
              ·
                refine ⟨34948111043214269483258945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93194962781904718622023853 34948111043214269483258945)
                ·
                  refine ⟨26211083282410702112444209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34948111043214269483258945 26211083282410702112444209)
                  ·
                    refine ⟨19658312461808026584333157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26211083282410702112444209 19658312461808026584333157)
                    ·
                      refine ⟨3685933586589004984562467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19658312461808026584333157 3685933586589004984562467)
                      ·
                        rfl

theorem cell23_7178330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 3, 2, 2, 4].length) (baseStart_7178330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7178330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7178330 prefixEnd_7178330 := by exact prefixLift 7178330
  have htrace : WordTrace (prefixWord ++ tailWord_7178330) baseStart_7178330 baseEnd_7178330 := by
    simpa [prefixWord, tailWord_7178330, baseEnd_7178330] using wordTrace_append hprefix tailTrace_7178330
  have hstable : (prefixWord ++ tailWord_7178330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7178330).length < 2 ^ (prefixWord ++ tailWord_7178330).sum := by decide
  have hdescent : baseEnd_7178330 < baseStart_7178330 := by decide
  rcases family_descends (prefixWord ++ tailWord_7178330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7178338 : List Nat := [3, 3, 2, 2, 2, 1, 2, 2, 1, 3, 2]
def baseStart_7178338 : Nat := 118140960795 + 7178338 * 2 ^ 59
def prefixEnd_7178338 : Nat := 4983230072969 + 3 ^ 40 * 7178338 * 2
def baseEnd_7178338 : Nat := 3685937694434240953262431

theorem tailTrace_7178338 : CollatzResearch.WordTrace tailWord_7178338 prefixEnd_7178338 3685937694434240953262431 := by
  unfold tailWord_7178338
  simp only [CollatzResearch.WordTrace]
  refine ⟨65453873967028715842911917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174543663912076575581098445 65453873967028715842911917)
  ·
    refine ⟨24545202737635768441091969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65453873967028715842911917 24545202737635768441091969)
    ·
      refine ⟨18408902053226826330818977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24545202737635768441091969 18408902053226826330818977)
      ·
        refine ⟨13806676539920119748114233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18408902053226826330818977 13806676539920119748114233)
        ·
          refine ⟨10355007404940089811085675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13806676539920119748114233 10355007404940089811085675)
          ·
            refine ⟨15532511107410134716628513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10355007404940089811085675 15532511107410134716628513)
            ·
              refine ⟨11649383330557601037471385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15532511107410134716628513 11649383330557601037471385)
              ·
                refine ⟨8737037497918200778103539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11649383330557601037471385 8737037497918200778103539)
                ·
                  refine ⟨13105556246877301167155309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8737037497918200778103539 13105556246877301167155309)
                  ·
                    refine ⟨4914583592578987937683241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13105556246877301167155309 4914583592578987937683241)
                    ·
                      refine ⟨3685937694434240953262431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4914583592578987937683241 3685937694434240953262431)
                      ·
                        rfl

theorem cell23_7178338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_7178338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7178338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7178338 prefixEnd_7178338 := by exact prefixLift 7178338
  have htrace : WordTrace (prefixWord ++ tailWord_7178338) baseStart_7178338 baseEnd_7178338 := by
    simpa [prefixWord, tailWord_7178338, baseEnd_7178338] using wordTrace_append hprefix tailTrace_7178338
  have hstable : (prefixWord ++ tailWord_7178338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7178338).length < 2 ^ (prefixWord ++ tailWord_7178338).sum := by decide
  have hdescent : baseEnd_7178338 < baseStart_7178338 := by decide
  rcases family_descends (prefixWord ++ tailWord_7178338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7178340 : List Nat := [2, 3, 1, 1, 2, 1, 4, 2, 7]
def baseStart_7178340 : Nat := 118140960795 + 7178340 * 2 ^ 59
def prefixEnd_7178340 : Nat := 4983230072969 + 3 ^ 40 * 7178340 * 2
def baseEnd_7178340 : Nat := 409548746821727771715269

theorem tailTrace_7178340 : CollatzResearch.WordTrace tailWord_7178340 prefixEnd_7178340 409548746821727771715269 := by
  unfold tailWord_7178340
  simp only [CollatzResearch.WordTrace]
  refine ⟨130907784407053808856610237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174543712542738411808813649 130907784407053808856610237)
  ·
    refine ⟨49090419152645178321228839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130907784407053808856610237 49090419152645178321228839)
    ·
      refine ⟨73635628728967767481843259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49090419152645178321228839 73635628728967767481843259)
      ·
        refine ⟨110453443093451651222764889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73635628728967767481843259 110453443093451651222764889)
        ·
          refine ⟨82840082320088738417073667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110453443093451651222764889 82840082320088738417073667)
          ·
            refine ⟨124260123480133107625610501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82840082320088738417073667 124260123480133107625610501)
            ·
              refine ⟨23298773152524957679801969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 124260123480133107625610501 23298773152524957679801969)
              ·
                refine ⟨17474079864393718259851477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23298773152524957679801969 17474079864393718259851477)
                ·
                  refine ⟨409548746821727771715269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17474079864393718259851477 409548746821727771715269)
                  ·
                    rfl

theorem cell23_7178340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 2, 7].length) (baseStart_7178340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7178340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7178340 prefixEnd_7178340 := by exact prefixLift 7178340
  have htrace : WordTrace (prefixWord ++ tailWord_7178340) baseStart_7178340 baseEnd_7178340 := by
    simpa [prefixWord, tailWord_7178340, baseEnd_7178340] using wordTrace_append hprefix tailTrace_7178340
  have hstable : (prefixWord ++ tailWord_7178340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7178340).length < 2 ^ (prefixWord ++ tailWord_7178340).sum := by decide
  have hdescent : baseEnd_7178340 < baseStart_7178340 := by decide
  rcases family_descends (prefixWord ++ tailWord_7178340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7178377 : List Nat := [1, 2, 1, 1, 4, 2, 2, 1, 2, 5, 2]
def baseStart_7178377 : Nat := 118140960795 + 7178377 * 2 ^ 59
def prefixEnd_7178377 : Nat := 4983230072969 + 3 ^ 40 * 7178377 * 2
def baseEnd_7178377 : Nat := 3685957720179766300674751

theorem tailTrace_7178377 : CollatzResearch.WordTrace tailWord_7178377 prefixEnd_7178377 3685957720179766300674751 := by
  unfold tailWord_7178377
  simp only [CollatzResearch.WordTrace]
  refine ⟨261816918314973573032317385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174544612209982382021544923 261816918314973573032317385)
  ·
    refine ⟨196362688736230179774238039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261816918314973573032317385 196362688736230179774238039)
    ·
      refine ⟨294544033104345269661357059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196362688736230179774238039 294544033104345269661357059)
      ·
        refine ⟨441816049656517904492035589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294544033104345269661357059 441816049656517904492035589)
        ·
          refine ⟨82840509310597107092256673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 441816049656517904492035589 82840509310597107092256673)
          ·
            refine ⟨62130381982947830319192505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82840509310597107092256673 62130381982947830319192505)
            ·
              refine ⟨46597786487210872739394379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62130381982947830319192505 46597786487210872739394379)
              ·
                refine ⟨69896679730816309109091569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46597786487210872739394379 69896679730816309109091569)
                ·
                  refine ⟨52422509798112231831818677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69896679730816309109091569 52422509798112231831818677)
                  ·
                    refine ⟨4914610293573021734233001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52422509798112231831818677 4914610293573021734233001)
                    ·
                      refine ⟨3685957720179766300674751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4914610293573021734233001 3685957720179766300674751)
                      ·
                        rfl

theorem cell23_7178377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 2, 5, 2].length) (baseStart_7178377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7178377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7178377 prefixEnd_7178377 := by exact prefixLift 7178377
  have htrace : WordTrace (prefixWord ++ tailWord_7178377) baseStart_7178377 baseEnd_7178377 := by
    simpa [prefixWord, tailWord_7178377, baseEnd_7178377] using wordTrace_append hprefix tailTrace_7178377
  have hstable : (prefixWord ++ tailWord_7178377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7178377).length < 2 ^ (prefixWord ++ tailWord_7178377).sum := by decide
  have hdescent : baseEnd_7178377 < baseStart_7178377 := by decide
  rcases family_descends (prefixWord ++ tailWord_7178377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7178404 : List Nat := [2, 3, 1, 2, 4, 1, 2, 1, 2, 5]
def baseStart_7178404 : Nat := 118140960795 + 7178404 * 2 ^ 59
def prefixEnd_7178404 : Nat := 4983230072969 + 3 ^ 40 * 7178404 * 2
def baseEnd_7178404 : Nat := 1228657194719145898345709

theorem tailTrace_7178404 : CollatzResearch.WordTrace tailWord_7178404 prefixEnd_7178404 1228657194719145898345709 := by
  unfold tailWord_7178404
  simp only [CollatzResearch.WordTrace]
  refine ⟨130908951542937878321775133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174545268723917171095700177 130908951542937878321775133)
  ·
    refine ⟨49090856828601704370665675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130908951542937878321775133 49090856828601704370665675)
    ·
      refine ⟨73636285242902556555998513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49090856828601704370665675 73636285242902556555998513)
      ·
        refine ⟨55227213932176917416998885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73636285242902556555998513 55227213932176917416998885)
        ·
          refine ⟨10355102612283172015687291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55227213932176917416998885 10355102612283172015687291)
          ·
            refine ⟨15532653918424758023530937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10355102612283172015687291 15532653918424758023530937)
            ·
              refine ⟨11649490438818568517648203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15532653918424758023530937 11649490438818568517648203)
              ·
                refine ⟨17474235658227852776472305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11649490438818568517648203 17474235658227852776472305)
                ·
                  refine ⟨13105676743670889582354229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17474235658227852776472305 13105676743670889582354229)
                  ·
                    refine ⟨1228657194719145898345709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13105676743670889582354229 1228657194719145898345709)
                    ·
                      rfl

theorem cell23_7178404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 1, 2, 5].length) (baseStart_7178404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7178404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7178404 prefixEnd_7178404 := by exact prefixLift 7178404
  have htrace : WordTrace (prefixWord ++ tailWord_7178404) baseStart_7178404 baseEnd_7178404 := by
    simpa [prefixWord, tailWord_7178404, baseEnd_7178404] using wordTrace_append hprefix tailTrace_7178404
  have hstable : (prefixWord ++ tailWord_7178404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7178404).length < 2 ^ (prefixWord ++ tailWord_7178404).sum := by decide
  have hdescent : baseEnd_7178404 < baseStart_7178404 := by decide
  rcases family_descends (prefixWord ++ tailWord_7178404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7178427 : List Nat := [1, 1, 1, 1, 1, 2, 5, 4, 2, 2, 3]
def baseStart_7178427 : Nat := 118140960795 + 7178427 * 2 ^ 59
def prefixEnd_7178427 : Nat := 4983230072969 + 3 ^ 40 * 7178427 * 2
def baseEnd_7178427 : Nat := 3685983394212491105049521

theorem tailTrace_7178427 : CollatzResearch.WordTrace tailWord_7178427 prefixEnd_7178427 3685983394212491105049521 := by
  unfold tailWord_7178427
  simp only [CollatzResearch.WordTrace]
  refine ⟨261818741964792431571637535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174545827976528287714425023 261818741964792431571637535)
  ·
    refine ⟨392728112947188647357456303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261818741964792431571637535 392728112947188647357456303)
    ·
      refine ⟨589092169420782971036184455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392728112947188647357456303 589092169420782971036184455)
      ·
        refine ⟨883638254131174456554276683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 589092169420782971036184455 883638254131174456554276683)
        ·
          refine ⟨1325457381196761684831415025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 883638254131174456554276683 1325457381196761684831415025)
          ·
            refine ⟨994093035897571263623561269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1325457381196761684831415025 994093035897571263623561269)
            ·
              refine ⟨93196222115397305964708869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 994093035897571263623561269 93196222115397305964708869)
              ·
                refine ⟨17474291646636994868382913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93196222115397305964708869 17474291646636994868382913)
                ·
                  refine ⟨13105718734977746151287185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17474291646636994868382913 13105718734977746151287185)
                  ·
                    refine ⟨9829289051233309613465389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13105718734977746151287185 9829289051233309613465389)
                    ·
                      refine ⟨3685983394212491105049521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9829289051233309613465389 3685983394212491105049521)
                      ·
                        rfl

theorem cell23_7178427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 4, 2, 2, 3].length) (baseStart_7178427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7178427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7178427 prefixEnd_7178427 := by exact prefixLift 7178427
  have htrace : WordTrace (prefixWord ++ tailWord_7178427) baseStart_7178427 baseEnd_7178427 := by
    simpa [prefixWord, tailWord_7178427, baseEnd_7178427] using wordTrace_append hprefix tailTrace_7178427
  have hstable : (prefixWord ++ tailWord_7178427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7178427).length < 2 ^ (prefixWord ++ tailWord_7178427).sum := by decide
  have hdescent : baseEnd_7178427 < baseStart_7178427 := by decide
  rcases family_descends (prefixWord ++ tailWord_7178427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7178461 : List Nat := [1, 4, 3, 2, 1, 1, 3, 1, 2, 2, 3]
def baseStart_7178461 : Nat := 118140960795 + 7178461 * 2 ^ 59
def prefixEnd_7178461 : Nat := 4983230072969 + 3 ^ 40 * 7178461 * 2
def baseEnd_7178461 : Nat := 3686000852554743972024365

theorem tailTrace_7178461 : CollatzResearch.WordTrace tailWord_7178461 prefixEnd_7178461 3686000852554743972024365 := by
  unfold tailWord_7178461
  simp only [CollatzResearch.WordTrace]
  refine ⟨261819982046669255378375237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174546654697779503585583491 261819982046669255378375237)
  ·
    refine ⟨49091246633750485383445357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 261819982046669255378375237 49091246633750485383445357)
    ·
      refine ⟨18409217487656432018792009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49091246633750485383445357 18409217487656432018792009)
      ·
        refine ⟨13806913115742324014094007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18409217487656432018792009 13806913115742324014094007)
        ·
          refine ⟨20710369673613486021141011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13806913115742324014094007 20710369673613486021141011)
          ·
            refine ⟨31065554510420229031711517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20710369673613486021141011 31065554510420229031711517)
            ·
              refine ⟨11649582941407585886891819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31065554510420229031711517 11649582941407585886891819)
              ·
                refine ⟨17474374412111378830337729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11649582941407585886891819 17474374412111378830337729)
                ·
                  refine ⟨13105780809083534122753297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17474374412111378830337729 13105780809083534122753297)
                  ·
                    refine ⟨9829335606812650592064973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13105780809083534122753297 9829335606812650592064973)
                    ·
                      refine ⟨3686000852554743972024365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9829335606812650592064973 3686000852554743972024365)
                      ·
                        rfl

theorem cell23_7178461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_7178461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7178461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7178461 prefixEnd_7178461 := by exact prefixLift 7178461
  have htrace : WordTrace (prefixWord ++ tailWord_7178461) baseStart_7178461 baseEnd_7178461 := by
    simpa [prefixWord, tailWord_7178461, baseEnd_7178461] using wordTrace_append hprefix tailTrace_7178461
  have hstable : (prefixWord ++ tailWord_7178461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7178461).length < 2 ^ (prefixWord ++ tailWord_7178461).sum := by decide
  have hdescent : baseEnd_7178461 < baseStart_7178461 := by decide
  rcases family_descends (prefixWord ++ tailWord_7178461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7178474 : List Nat := [3, 1, 3, 1, 1, 2, 1, 2, 5, 1, 3]
def baseStart_7178474 : Nat := 118140960795 + 7178474 * 2 ^ 59
def prefixEnd_7178474 : Nat := 4983230072969 + 3 ^ 40 * 7178474 * 2
def baseEnd_7178474 : Nat := 3686007527803252421161805

theorem tailTrace_7178474 : CollatzResearch.WordTrace tailWord_7178474 prefixEnd_7178474 3686007527803252421161805 := by
  unfold tailWord_7178474
  simp only [CollatzResearch.WordTrace]
  refine ⟨65455114048905539649649619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174546970797081439065732317 65455114048905539649649619)
  ·
    refine ⟨98182671073358309474474429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65455114048905539649649619 98182671073358309474474429)
    ·
      refine ⟨36818501652509366052927911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98182671073358309474474429 36818501652509366052927911)
      ·
        refine ⟨55227752478764049079391867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36818501652509366052927911 55227752478764049079391867)
        ·
          refine ⟨82841628718146073619087801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55227752478764049079391867 82841628718146073619087801)
          ·
            refine ⟨62131221538609555214315851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82841628718146073619087801 62131221538609555214315851)
            ·
              refine ⟨93196832307914332821473777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62131221538609555214315851 93196832307914332821473777)
              ·
                refine ⟨69897624230935749616105333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93196832307914332821473777 69897624230935749616105333)
                ·
                  refine ⟨6552902271650226526509875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69897624230935749616105333 6552902271650226526509875)
                  ·
                    refine ⟨9829353407475339789764813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6552902271650226526509875 9829353407475339789764813)
                    ·
                      refine ⟨3686007527803252421161805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9829353407475339789764813 3686007527803252421161805)
                      ·
                        rfl

theorem cell23_7178474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 5, 1, 3].length) (baseStart_7178474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7178474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7178474 prefixEnd_7178474 := by exact prefixLift 7178474
  have htrace : WordTrace (prefixWord ++ tailWord_7178474) baseStart_7178474 baseEnd_7178474 := by
    simpa [prefixWord, tailWord_7178474, baseEnd_7178474] using wordTrace_append hprefix tailTrace_7178474
  have hstable : (prefixWord ++ tailWord_7178474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7178474).length < 2 ^ (prefixWord ++ tailWord_7178474).sum := by decide
  have hdescent : baseEnd_7178474 < baseStart_7178474 := by decide
  rcases family_descends (prefixWord ++ tailWord_7178474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7178542 : List Nat := [4, 1, 3, 3, 2, 1, 1, 1, 3, 1, 3]
def baseStart_7178542 : Nat := 118140960795 + 7178542 * 2 ^ 59
def prefixEnd_7178542 : Nat := 4983230072969 + 3 ^ 40 * 7178542 * 2
def baseEnd_7178542 : Nat := 3686042444487758155111493

theorem tailTrace_7178542 : CollatzResearch.WordTrace tailWord_7178542 prefixEnd_7178542 3686042444487758155111493 := by
  unfold tailWord_7178542
  simp only [CollatzResearch.WordTrace]
  refine ⟨32727867044921975776509235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174548624239583870808049253 32727867044921975776509235)
  ·
    refine ⟨49091800567382963664763853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32727867044921975776509235 49091800567382963664763853)
    ·
      refine ⟨18409425212768611374286445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49091800567382963664763853 18409425212768611374286445)
      ·
        refine ⟨6903534454788229265357417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18409425212768611374286445 6903534454788229265357417)
        ·
          refine ⟨5177650841091171949018063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6903534454788229265357417 5177650841091171949018063)
          ·
            refine ⟨7766476261636757923527095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5177650841091171949018063 7766476261636757923527095)
            ·
              refine ⟨11649714392455136885290643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7766476261636757923527095 11649714392455136885290643)
              ·
                refine ⟨17474571588682705327935965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11649714392455136885290643 17474571588682705327935965)
                ·
                  refine ⟨6552964345756014497975987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17474571588682705327935965 6552964345756014497975987)
                  ·
                    refine ⟨9829446518634021746963981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6552964345756014497975987 9829446518634021746963981)
                    ·
                      refine ⟨3686042444487758155111493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9829446518634021746963981 3686042444487758155111493)
                      ·
                        rfl

theorem cell23_7178542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_7178542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7178542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7178542 prefixEnd_7178542 := by exact prefixLift 7178542
  have htrace : WordTrace (prefixWord ++ tailWord_7178542) baseStart_7178542 baseEnd_7178542 := by
    simpa [prefixWord, tailWord_7178542, baseEnd_7178542] using wordTrace_append hprefix tailTrace_7178542
  have hstable : (prefixWord ++ tailWord_7178542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7178542).length < 2 ^ (prefixWord ++ tailWord_7178542).sum := by decide
  have hdescent : baseEnd_7178542 < baseStart_7178542 := by decide
  rcases family_descends (prefixWord ++ tailWord_7178542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7178558 : List Nat := [4, 2, 1, 2, 1, 2, 4, 1, 2, 4]
def baseStart_7178558 : Nat := 118140960795 + 7178558 * 2 ^ 59
def prefixEnd_7178558 : Nat := 4983230072969 + 3 ^ 40 * 7178558 * 2
def baseEnd_7178558 : Nat := 1228683553392743364170473

theorem tailTrace_7178558 : CollatzResearch.WordTrace tailWord_7178558 prefixEnd_7178558 1228683553392743364170473 := by
  unfold tailWord_7178558
  simp only [CollatzResearch.WordTrace]
  refine ⟨32727939990914730118082041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174549013284878560629770885 32727939990914730118082041)
  ·
    refine ⟨24545954993186047588561531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32727939990914730118082041 24545954993186047588561531)
    ·
      refine ⟨36818932489779071382842297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24545954993186047588561531 36818932489779071382842297)
      ·
        refine ⟨27614199367334303537131723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36818932489779071382842297 27614199367334303537131723)
        ·
          refine ⟨41421299051001455305697585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27614199367334303537131723 41421299051001455305697585)
          ·
            refine ⟨31065974288251091479273189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41421299051001455305697585 31065974288251091479273189)
            ·
              refine ⟨5824870179047079652363723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31065974288251091479273189 5824870179047079652363723)
              ·
                refine ⟨8737305268570619478545585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5824870179047079652363723 8737305268570619478545585)
                ·
                  refine ⟨6552978951427964608909189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8737305268570619478545585 6552978951427964608909189)
                  ·
                    refine ⟨1228683553392743364170473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6552978951427964608909189 1228683553392743364170473)
                    ·
                      rfl

theorem cell23_7178558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 4, 1, 2, 4].length) (baseStart_7178558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7178558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7178558 prefixEnd_7178558 := by exact prefixLift 7178558
  have htrace : WordTrace (prefixWord ++ tailWord_7178558) baseStart_7178558 baseEnd_7178558 := by
    simpa [prefixWord, tailWord_7178558, baseEnd_7178558] using wordTrace_append hprefix tailTrace_7178558
  have hstable : (prefixWord ++ tailWord_7178558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7178558).length < 2 ^ (prefixWord ++ tailWord_7178558).sum := by decide
  have hdescent : baseEnd_7178558 < baseStart_7178558 := by decide
  rcases family_descends (prefixWord ++ tailWord_7178558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7178581 : List Nat := [1, 3, 2, 2, 4, 1, 1, 2, 1, 3, 3]
def baseStart_7178581 : Nat := 118140960795 + 7178581 * 2 ^ 59
def prefixEnd_7178581 : Nat := 4983230072969 + 3 ^ 40 * 7178581 * 2
def baseEnd_7178581 : Nat := 3686062470233283502523813

theorem tailTrace_7178581 : CollatzResearch.WordTrace tailWord_7178581 prefixEnd_7178581 3686062470233283502523813 := by
  unfold tailWord_7178581
  simp only [CollatzResearch.WordTrace]
  refine ⟨261824358806234515872743597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174549572537489677248495731 261824358806234515872743597)
  ·
    refine ⟨98184134552337943452278849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261824358806234515872743597 98184134552337943452278849)
    ·
      refine ⟨73638100914253457589209137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98184134552337943452278849 73638100914253457589209137)
      ·
        refine ⟨55228575685690093191906853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73638100914253457589209137 55228575685690093191906853)
        ·
          refine ⟨10355357941066892473482535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55228575685690093191906853 10355357941066892473482535)
          ·
            refine ⟨15533036911600338710223803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10355357941066892473482535 15533036911600338710223803)
            ·
              refine ⟨23299555367400508065335705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15533036911600338710223803 23299555367400508065335705)
              ·
                refine ⟨17474666525550381049001779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23299555367400508065335705 17474666525550381049001779)
                ·
                  refine ⟨26211999788325571573502669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17474666525550381049001779 26211999788325571573502669)
                  ·
                    refine ⟨9829499920622089340063501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26211999788325571573502669 9829499920622089340063501)
                    ·
                      refine ⟨3686062470233283502523813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9829499920622089340063501 3686062470233283502523813)
                      ·
                        rfl

theorem cell23_7178581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 2, 1, 3, 3].length) (baseStart_7178581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7178581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7178581 prefixEnd_7178581 := by exact prefixLift 7178581
  have htrace : WordTrace (prefixWord ++ tailWord_7178581) baseStart_7178581 baseEnd_7178581 := by
    simpa [prefixWord, tailWord_7178581, baseEnd_7178581] using wordTrace_append hprefix tailTrace_7178581
  have hstable : (prefixWord ++ tailWord_7178581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7178581).length < 2 ^ (prefixWord ++ tailWord_7178581).sum := by decide
  have hdescent : baseEnd_7178581 < baseStart_7178581 := by decide
  rcases family_descends (prefixWord ++ tailWord_7178581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7178591 : List Nat := [1, 1, 2, 3, 1, 2, 2, 5, 1, 3, 2]
def baseStart_7178591 : Nat := 118140960795 + 7178591 * 2 ^ 59
def prefixEnd_7178591 : Nat := 4983230072969 + 3 ^ 40 * 7178591 * 2
def baseEnd_7178591 : Nat := 3686067605039828463398767

theorem tailTrace_7178591 : CollatzResearch.WordTrace tailWord_7178591 prefixEnd_7178591 3686067605039828463398767 := by
  unfold tailWord_7178591
  simp only [CollatzResearch.WordTrace]
  refine ⟨261824723536198287580607627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174549815690798858387071751 261824723536198287580607627)
  ·
    refine ⟨392737085304297431370911441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261824723536198287580607627 392737085304297431370911441)
    ·
      refine ⟨294552813978223073528183581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 392737085304297431370911441 294552813978223073528183581)
      ·
        refine ⟨110457305241833652573068843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 294552813978223073528183581 110457305241833652573068843)
        ·
          refine ⟨165685957862750478859603265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110457305241833652573068843 165685957862750478859603265)
          ·
            refine ⟨124264468397062859144702449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165685957862750478859603265 124264468397062859144702449)
            ·
              refine ⟨93198351297797144358526837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124264468397062859144702449 93198351297797144358526837)
              ·
                refine ⟨8737345434168482283611891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 93198351297797144358526837 8737345434168482283611891)
                ·
                  refine ⟨13106018151252723425417837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8737345434168482283611891 13106018151252723425417837)
                  ·
                    refine ⟨4914756806719771284531689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13106018151252723425417837 4914756806719771284531689)
                    ·
                      refine ⟨3686067605039828463398767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4914756806719771284531689 3686067605039828463398767)
                      ·
                        rfl

theorem cell23_7178591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 5, 1, 3, 2].length) (baseStart_7178591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7178591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7178591 prefixEnd_7178591 := by exact prefixLift 7178591
  have htrace : WordTrace (prefixWord ++ tailWord_7178591) baseStart_7178591 baseEnd_7178591 := by
    simpa [prefixWord, tailWord_7178591, baseEnd_7178591] using wordTrace_append hprefix tailTrace_7178591
  have hstable : (prefixWord ++ tailWord_7178591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7178591).length < 2 ^ (prefixWord ++ tailWord_7178591).sum := by decide
  have hdescent : baseEnd_7178591 < baseStart_7178591 := by decide
  rcases family_descends (prefixWord ++ tailWord_7178591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7178607 : List Nat := [1, 1, 2, 1, 3, 1, 2, 2, 4, 1, 5]
def baseStart_7178607 : Nat := 118140960795 + 7178607 * 2 ^ 59
def prefixEnd_7178607 : Nat := 4983230072969 + 3 ^ 40 * 7178607 * 2
def baseEnd_7178607 : Nat := 3686075820730300400798693

theorem tailTrace_7178607 : CollatzResearch.WordTrace tailWord_7178607 prefixEnd_7178607 3686075820730300400798693 := by
  unfold tailWord_7178607
  simp only [CollatzResearch.WordTrace]
  refine ⟨261825307104140322313190075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174550204736093548208793383 261825307104140322313190075)
  ·
    refine ⟨392737960656210483469785113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261825307104140322313190075 392737960656210483469785113)
    ·
      refine ⟨294553470492157862602338835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 392737960656210483469785113 294553470492157862602338835)
      ·
        refine ⟨441830205738236793903508253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294553470492157862602338835 441830205738236793903508253)
        ·
          refine ⟨165686327151838797713815595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 441830205738236793903508253 165686327151838797713815595)
          ·
            refine ⟨248529490727758196570723393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165686327151838797713815595 248529490727758196570723393)
            ·
              refine ⟨186397118045818647428042545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 248529490727758196570723393 186397118045818647428042545)
              ·
                refine ⟨139797838534363985571031909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 186397118045818647428042545 139797838534363985571031909)
                ·
                  refine ⟨26212094725193247294568483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 139797838534363985571031909 26212094725193247294568483)
                  ·
                    refine ⟨39318142087789870941852725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26212094725193247294568483 39318142087789870941852725)
                    ·
                      refine ⟨3686075820730300400798693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39318142087789870941852725 3686075820730300400798693)
                      ·
                        rfl

theorem cell23_7178607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 4, 1, 5].length) (baseStart_7178607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7178607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7178607 prefixEnd_7178607 := by exact prefixLift 7178607
  have htrace : WordTrace (prefixWord ++ tailWord_7178607) baseStart_7178607 baseEnd_7178607 := by
    simpa [prefixWord, tailWord_7178607, baseEnd_7178607] using wordTrace_append hprefix tailTrace_7178607
  have hstable : (prefixWord ++ tailWord_7178607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7178607).length < 2 ^ (prefixWord ++ tailWord_7178607).sum := by decide
  have hdescent : baseEnd_7178607 < baseStart_7178607 := by decide
  rcases family_descends (prefixWord ++ tailWord_7178607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7178621 : List Nat := [1, 4, 1, 1, 2, 3, 1, 3, 1, 4, 2]
def baseStart_7178621 : Nat := 118140960795 + 7178621 * 2 ^ 59
def prefixEnd_7178621 : Nat := 4983230072969 + 3 ^ 40 * 7178621 * 2
def baseEnd_7178621 : Nat := 3686083009459463346023629

theorem tailTrace_7178621 : CollatzResearch.WordTrace tailWord_7178621 prefixEnd_7178621 3686083009459463346023629 := by
  unfold tailWord_7178621
  simp only [CollatzResearch.WordTrace]
  refine ⟨261825817726089602704199717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174550545150726401802799811 261825817726089602704199717)
  ·
    refine ⟨49092340823641800507037447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 261825817726089602704199717 49092340823641800507037447)
    ·
      refine ⟨73638511235462700760556171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49092340823641800507037447 73638511235462700760556171)
      ·
        refine ⟨110457766853194051140834257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73638511235462700760556171 110457766853194051140834257)
        ·
          refine ⟨82843325139895538355625693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110457766853194051140834257 82843325139895538355625693)
          ·
            refine ⟨31066246927460826883359635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82843325139895538355625693 31066246927460826883359635)
            ·
              refine ⟨46599370391191240325039453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31066246927460826883359635 46599370391191240325039453)
              ·
                refine ⟨17474763896696715121889795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46599370391191240325039453 17474763896696715121889795)
                ·
                  refine ⟨26212145845045072682834693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17474763896696715121889795 26212145845045072682834693)
                  ·
                    refine ⟨4914777345945951128031505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26212145845045072682834693 4914777345945951128031505)
                    ·
                      refine ⟨3686083009459463346023629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4914777345945951128031505 3686083009459463346023629)
                      ·
                        rfl

theorem cell23_7178621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 3, 1, 4, 2].length) (baseStart_7178621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7178621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7178621 prefixEnd_7178621 := by exact prefixLift 7178621
  have htrace : WordTrace (prefixWord ++ tailWord_7178621) baseStart_7178621 baseEnd_7178621 := by
    simpa [prefixWord, tailWord_7178621, baseEnd_7178621] using wordTrace_append hprefix tailTrace_7178621
  have hstable : (prefixWord ++ tailWord_7178621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7178621).length < 2 ^ (prefixWord ++ tailWord_7178621).sum := by decide
  have hdescent : baseEnd_7178621 < baseStart_7178621 := by decide
  rcases family_descends (prefixWord ++ tailWord_7178621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7178638 : List Nat := [4, 1, 1, 4, 1, 1, 2, 2, 1, 4, 2]
def baseStart_7178638 : Nat := 118140960795 + 7178638 * 2 ^ 59
def prefixEnd_7178638 : Nat := 4983230072969 + 3 ^ 40 * 7178638 * 2
def baseEnd_7178638 : Nat := 3686091738630589779511051

theorem tailTrace_7178638 : CollatzResearch.WordTrace tailWord_7178638 prefixEnd_7178638 3686091738630589779511051 := by
  unfold tailWord_7178638
  simp only [CollatzResearch.WordTrace]
  refine ⟨32728304720878501825946071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174550958511352009738379045 32728304720878501825946071)
  ·
    refine ⟨49092457081317752738919107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32728304720878501825946071 49092457081317752738919107)
    ·
      refine ⟨73638685621976629108378661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49092457081317752738919107 73638685621976629108378661)
      ·
        refine ⟨13807253554120617957820999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73638685621976629108378661 13807253554120617957820999)
        ·
          refine ⟨20710880331180926936731499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13807253554120617957820999 20710880331180926936731499)
          ·
            refine ⟨31066320496771390405097249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20710880331180926936731499 31066320496771390405097249)
            ·
              refine ⟨23299740372578542803822937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31066320496771390405097249 23299740372578542803822937)
              ·
                refine ⟨17474805279433907102867203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23299740372578542803822937 17474805279433907102867203)
                ·
                  refine ⟨26212207919150860654300805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17474805279433907102867203 26212207919150860654300805)
                  ·
                    refine ⟨4914788984840786372681401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26212207919150860654300805 4914788984840786372681401)
                    ·
                      refine ⟨3686091738630589779511051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4914788984840786372681401 3686091738630589779511051)
                      ·
                        rfl

theorem cell23_7178638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_7178638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7178638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7178638 prefixEnd_7178638 := by exact prefixLift 7178638
  have htrace : WordTrace (prefixWord ++ tailWord_7178638) baseStart_7178638 baseEnd_7178638 := by
    simpa [prefixWord, tailWord_7178638, baseEnd_7178638] using wordTrace_append hprefix tailTrace_7178638
  have hstable : (prefixWord ++ tailWord_7178638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7178638).length < 2 ^ (prefixWord ++ tailWord_7178638).sum := by decide
  have hdescent : baseEnd_7178638 < baseStart_7178638 := by decide
  rcases family_descends (prefixWord ++ tailWord_7178638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7178761 : List Nat := [1, 2, 1, 1, 3, 1, 2, 1, 7, 1, 3]
def baseStart_7178761 : Nat := 118140960795 + 7178761 * 2 ^ 59
def prefixEnd_7178761 : Nat := 4983230072969 + 3 ^ 40 * 7178761 * 2
def baseEnd_7178761 : Nat := 3686154896751092798272985

theorem tailTrace_7178761 : CollatzResearch.WordTrace tailWord_7178761 prefixEnd_7178761 3686154896751092798272985 := by
  unfold tailWord_7178761
  simp only [CollatzResearch.WordTrace]
  refine ⟨261830923945582406614296137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174553949297054937742864091 261830923945582406614296137)
  ·
    refine ⟨196373192959186804960722103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261830923945582406614296137 196373192959186804960722103)
    ·
      refine ⟨294559789438780207441083155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196373192959186804960722103 294559789438780207441083155)
      ·
        refine ⟨441839684158170311161624733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294559789438780207441083155 441839684158170311161624733)
        ·
          refine ⟨165689881559313866685609275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 441839684158170311161624733 165689881559313866685609275)
          ·
            refine ⟨248534822338970800028413913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165689881559313866685609275 248534822338970800028413913)
            ·
              refine ⟨186401116754228100021310435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 248534822338970800028413913 186401116754228100021310435)
              ·
                refine ⟨279601675131342150031965653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 186401116754228100021310435 279601675131342150031965653)
                ·
                  refine ⟨6553164260890831641374195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 279601675131342150031965653 6553164260890831641374195)
                  ·
                    refine ⟨9829746391336247462061293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6553164260890831641374195 9829746391336247462061293)
                    ·
                      refine ⟨3686154896751092798272985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9829746391336247462061293 3686154896751092798272985)
                      ·
                        rfl

theorem cell23_7178761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 7, 1, 3].length) (baseStart_7178761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7178761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7178761 prefixEnd_7178761 := by exact prefixLift 7178761
  have htrace : WordTrace (prefixWord ++ tailWord_7178761) baseStart_7178761 baseEnd_7178761 := by
    simpa [prefixWord, tailWord_7178761, baseEnd_7178761] using wordTrace_append hprefix tailTrace_7178761
  have hstable : (prefixWord ++ tailWord_7178761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7178761).length < 2 ^ (prefixWord ++ tailWord_7178761).sum := by decide
  have hdescent : baseEnd_7178761 < baseStart_7178761 := by decide
  rcases family_descends (prefixWord ++ tailWord_7178761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7178772 : List Nat := [2, 4, 3, 1, 1, 2, 1, 4, 1, 4]
def baseStart_7178772 : Nat := 118140960795 + 7178772 * 2 ^ 59
def prefixEnd_7178772 : Nat := 4983230072969 + 3 ^ 40 * 7178772 * 2
def baseEnd_7178772 : Nat := 1228720181679430751745145

theorem tailTrace_7178772 : CollatzResearch.WordTrace tailWord_7178772 prefixEnd_7178772 1228720181679430751745145 := by
  unfold tailWord_7178772
  simp only [CollatzResearch.WordTrace]
  refine ⟨130915662574271277746473285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174554216765695036995297713 130915662574271277746473285)
  ·
    refine ⟨24546686732675864577463741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130915662574271277746473285 24546686732675864577463741)
    ·
      refine ⟨9205007524753449216548903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24546686732675864577463741 9205007524753449216548903)
      ·
        refine ⟨13807511287130173824823355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9205007524753449216548903 13807511287130173824823355)
        ·
          refine ⟨20711266930695260737235033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13807511287130173824823355 20711266930695260737235033)
          ·
            refine ⟨15533450198021445552926275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20711266930695260737235033 15533450198021445552926275)
            ·
              refine ⟨23300175297032168329389413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15533450198021445552926275 23300175297032168329389413)
              ·
                refine ⟨4368782868193531561760515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23300175297032168329389413 4368782868193531561760515)
                ·
                  refine ⟨6553174302290297342640773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4368782868193531561760515 6553174302290297342640773)
                  ·
                    refine ⟨1228720181679430751745145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6553174302290297342640773 1228720181679430751745145)
                    ·
                      rfl

theorem cell23_7178772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_7178772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7178772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7178772 prefixEnd_7178772 := by exact prefixLift 7178772
  have htrace : WordTrace (prefixWord ++ tailWord_7178772) baseStart_7178772 baseEnd_7178772 := by
    simpa [prefixWord, tailWord_7178772, baseEnd_7178772] using wordTrace_append hprefix tailTrace_7178772
  have hstable : (prefixWord ++ tailWord_7178772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7178772).length < 2 ^ (prefixWord ++ tailWord_7178772).sum := by decide
  have hdescent : baseEnd_7178772 < baseStart_7178772 := by decide
  rcases family_descends (prefixWord ++ tailWord_7178772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7178781 : List Nat := [1, 4, 2, 2, 1, 2, 1, 2, 3, 5]
def baseStart_7178781 : Nat := 118140960795 + 7178781 * 2 ^ 59
def prefixEnd_7178781 : Nat := 4983230072969 + 3 ^ 40 * 7178781 * 2
def baseEnd_7178781 : Nat := 1228721722121394240007631

theorem tailTrace_7178781 : CollatzResearch.WordTrace tailWord_7178781 prefixEnd_7178781 1228721722121394240007631 := by
  unfold tailWord_7178781
  simp only [CollatzResearch.WordTrace]
  refine ⟨261831653405509950030024197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174554435603673300020016131 261831653405509950030024197)
  ·
    refine ⟨49093435013533115630629537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 261831653405509950030024197 49093435013533115630629537)
    ·
      refine ⟨36820076260149836722972153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49093435013533115630629537 36820076260149836722972153)
      ·
        refine ⟨27615057195112377542229115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36820076260149836722972153 27615057195112377542229115)
        ·
          refine ⟨41422585792668566313343673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27615057195112377542229115 41422585792668566313343673)
          ·
            refine ⟨31066939344501424735007755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41422585792668566313343673 31066939344501424735007755)
            ·
              refine ⟨46600409016752137102511633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31066939344501424735007755 46600409016752137102511633)
              ·
                refine ⟨34950306762564102826883725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46600409016752137102511633 34950306762564102826883725)
                ·
                  refine ⟨13106365035961538560081397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34950306762564102826883725 13106365035961538560081397)
                  ·
                    refine ⟨1228721722121394240007631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13106365035961538560081397 1228721722121394240007631)
                    ·
                      rfl

theorem cell23_7178781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 2, 3, 5].length) (baseStart_7178781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7178781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7178781 prefixEnd_7178781 := by exact prefixLift 7178781
  have htrace : WordTrace (prefixWord ++ tailWord_7178781) baseStart_7178781 baseEnd_7178781 := by
    simpa [prefixWord, tailWord_7178781, baseEnd_7178781] using wordTrace_append hprefix tailTrace_7178781
  have hstable : (prefixWord ++ tailWord_7178781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7178781).length < 2 ^ (prefixWord ++ tailWord_7178781).sum := by decide
  have hdescent : baseEnd_7178781 < baseStart_7178781 := by decide
  rcases family_descends (prefixWord ++ tailWord_7178781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7178801 : List Nat := [1, 2, 2, 3, 1, 1, 4, 1, 3, 1, 4]
def baseStart_7178801 : Nat := 118140960795 + 7178801 * 2 ^ 59
def prefixEnd_7178801 : Nat := 4983230072969 + 3 ^ 40 * 7178801 * 2
def baseEnd_7178801 : Nat := 3686175435977272641772801

theorem tailTrace_7178801 : CollatzResearch.WordTrace tailWord_7178801 prefixEnd_7178801 3686175435977272641772801 := by
  unfold tailWord_7178801
  simp only [CollatzResearch.WordTrace]
  refine ⟨261832382865437493445752257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174554921910291662297168171 261832382865437493445752257)
  ·
    refine ⟨196374287149078120084314193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261832382865437493445752257 196374287149078120084314193)
    ·
      refine ⟨147280715361808590063235645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196374287149078120084314193 147280715361808590063235645)
      ·
        refine ⟨55230268260678221273713367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147280715361808590063235645 55230268260678221273713367)
        ·
          refine ⟨82845402391017331910570051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55230268260678221273713367 82845402391017331910570051)
          ·
            refine ⟨124268103586525997865855077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82845402391017331910570051 124268103586525997865855077)
            ·
              refine ⟨23300269422473624599847827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 124268103586525997865855077 23300269422473624599847827)
              ·
                refine ⟨34950404133710436899771741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23300269422473624599847827 34950404133710436899771741)
                ·
                  refine ⟨13106401550141413837414403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34950404133710436899771741 13106401550141413837414403)
                  ·
                    refine ⟨19659602325212120756121605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13106401550141413837414403 19659602325212120756121605)
                    ·
                      refine ⟨3686175435977272641772801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19659602325212120756121605 3686175435977272641772801)
                      ·
                        rfl

theorem cell23_7178801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_7178801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7178801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7178801 prefixEnd_7178801 := by exact prefixLift 7178801
  have htrace : WordTrace (prefixWord ++ tailWord_7178801) baseStart_7178801 baseEnd_7178801 := by
    simpa [prefixWord, tailWord_7178801, baseEnd_7178801] using wordTrace_append hprefix tailTrace_7178801
  have hstable : (prefixWord ++ tailWord_7178801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7178801).length < 2 ^ (prefixWord ++ tailWord_7178801).sum := by decide
  have hdescent : baseEnd_7178801 < baseStart_7178801 := by decide
  rcases family_descends (prefixWord ++ tailWord_7178801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7178812 : List Nat := [2, 2, 2, 2, 3, 2, 2, 3, 1, 1, 3]
def baseStart_7178812 : Nat := 118140960795 + 7178812 * 2 ^ 59
def prefixEnd_7178812 : Nat := 4983230072969 + 3 ^ 40 * 7178812 * 2
def baseEnd_7178812 : Nat := 3686181084264472098735251

theorem tailTrace_7178812 : CollatzResearch.WordTrace tailWord_7178812 prefixEnd_7178812 3686181084264472098735251 := by
  unfold tailWord_7178812
  simp only [CollatzResearch.WordTrace]
  refine ⟨130916392034198821162201345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174555189378931761549601793 130916392034198821162201345)
  ·
    refine ⟨98187294025649115871651009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130916392034198821162201345 98187294025649115871651009)
    ·
      refine ⟨73640470519236836903738257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98187294025649115871651009 73640470519236836903738257)
      ·
        refine ⟨55230352889427627677803693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73640470519236836903738257 55230352889427627677803693)
        ·
          refine ⟨20711382333535360379176385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55230352889427627677803693 20711382333535360379176385)
          ·
            refine ⟨15533536750151520284382289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20711382333535360379176385 15533536750151520284382289)
            ·
              refine ⟨11650152562613640213286717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15533536750151520284382289 11650152562613640213286717)
              ·
                refine ⟨4368807210980115079982519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11650152562613640213286717 4368807210980115079982519)
                ·
                  refine ⟨6553210816470172619973779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4368807210980115079982519 6553210816470172619973779)
                  ·
                    refine ⟨9829816224705258929960669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6553210816470172619973779 9829816224705258929960669)
                    ·
                      refine ⟨3686181084264472098735251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9829816224705258929960669 3686181084264472098735251)
                      ·
                        rfl

theorem cell23_7178812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 3, 1, 1, 3].length) (baseStart_7178812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7178812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7178812 prefixEnd_7178812 := by exact prefixLift 7178812
  have htrace : WordTrace (prefixWord ++ tailWord_7178812) baseStart_7178812 baseEnd_7178812 := by
    simpa [prefixWord, tailWord_7178812, baseEnd_7178812] using wordTrace_append hprefix tailTrace_7178812
  have hstable : (prefixWord ++ tailWord_7178812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7178812).length < 2 ^ (prefixWord ++ tailWord_7178812).sum := by decide
  have hdescent : baseEnd_7178812 < baseStart_7178812 := by decide
  rcases family_descends (prefixWord ++ tailWord_7178812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7178881 : List Nat := [1, 2, 4, 2, 1, 1, 1, 2, 2, 2, 5]
def baseStart_7178881 : Nat := 118140960795 + 7178881 * 2 ^ 59
def prefixEnd_7178881 : Nat := 4983230072969 + 3 ^ 40 * 7178881 * 2
def baseEnd_7178881 : Nat := 3686216514429632328772433

theorem tailTrace_7178881 : CollatzResearch.WordTrace tailWord_7178881 prefixEnd_7178881 3686216514429632328772433 := by
  unfold tailWord_7178881
  simp only [CollatzResearch.WordTrace]
  refine ⟨261835300705147667108664497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174556867136765111405776331 261835300705147667108664497)
  ·
    refine ⟨196376475528860750331498373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261835300705147667108664497 196376475528860750331498373)
    ·
      refine ⟨36820589161661390687155945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 196376475528860750331498373 36820589161661390687155945)
      ·
        refine ⟨27615441871246043015366959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36820589161661390687155945 27615441871246043015366959)
        ·
          refine ⟨41423162806869064523050439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27615441871246043015366959 41423162806869064523050439)
          ·
            refine ⟨62134744210303596784575659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41423162806869064523050439 62134744210303596784575659)
            ·
              refine ⟨93202116315455395176863489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62134744210303596784575659 93202116315455395176863489)
              ·
                refine ⟨69901587236591546382647617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93202116315455395176863489 69901587236591546382647617)
                ·
                  refine ⟨52426190427443659786985713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69901587236591546382647617 52426190427443659786985713)
                  ·
                    refine ⟨39319642820582744840239285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52426190427443659786985713 39319642820582744840239285)
                    ·
                      refine ⟨3686216514429632328772433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39319642820582744840239285 3686216514429632328772433)
                      ·
                        rfl

theorem cell23_7178881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_7178881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7178881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7178881 prefixEnd_7178881 := by exact prefixLift 7178881
  have htrace : WordTrace (prefixWord ++ tailWord_7178881) baseStart_7178881 baseEnd_7178881 := by
    simpa [prefixWord, tailWord_7178881, baseEnd_7178881] using wordTrace_append hprefix tailTrace_7178881
  have hstable : (prefixWord ++ tailWord_7178881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7178881).length < 2 ^ (prefixWord ++ tailWord_7178881).sum := by decide
  have hdescent : baseEnd_7178881 < baseStart_7178881 := by decide
  rcases family_descends (prefixWord ++ tailWord_7178881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7178925 : List Nat := [1, 5, 2, 1, 1, 2, 1, 1, 3, 4, 2]
def baseStart_7178925 : Nat := 118140960795 + 7178925 * 2 ^ 59
def prefixEnd_7178925 : Nat := 4983230072969 + 3 ^ 40 * 7178925 * 2
def baseEnd_7178925 : Nat := 3686239107578430156622231

theorem tailTrace_7178925 : CollatzResearch.WordTrace tailWord_7178925 prefixEnd_7178925 3686239107578430156622231 := by
  unfold tailWord_7178925
  simp only [CollatzResearch.WordTrace]
  refine ⟨261836905516988262623266229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174557937011325508415510819 261836905516988262623266229)
  ·
    refine ⟨24547209892217649620931209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 261836905516988262623266229 24547209892217649620931209)
    ·
      refine ⟨18410407419163237215698407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24547209892217649620931209 18410407419163237215698407)
      ·
        refine ⟨27615611128744855823547611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18410407419163237215698407 27615611128744855823547611)
        ·
          refine ⟨41423416693117283735321417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27615611128744855823547611 41423416693117283735321417)
          ·
            refine ⟨31067562519837962801491063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41423416693117283735321417 31067562519837962801491063)
            ·
              refine ⟨46601343779756944202236595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31067562519837962801491063 46601343779756944202236595)
              ·
                refine ⟨69902015669635416303354893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46601343779756944202236595 69902015669635416303354893)
                ·
                  refine ⟨26213255876113281113758085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69902015669635416303354893 26213255876113281113758085)
                  ·
                    refine ⟨4914985476771240208829641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26213255876113281113758085 4914985476771240208829641)
                    ·
                      refine ⟨3686239107578430156622231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4914985476771240208829641 3686239107578430156622231)
                      ·
                        rfl

theorem cell23_7178925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 1, 3, 4, 2].length) (baseStart_7178925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7178925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7178925 prefixEnd_7178925 := by exact prefixLift 7178925
  have htrace : WordTrace (prefixWord ++ tailWord_7178925) baseStart_7178925 baseEnd_7178925 := by
    simpa [prefixWord, tailWord_7178925, baseEnd_7178925] using wordTrace_append hprefix tailTrace_7178925
  have hstable : (prefixWord ++ tailWord_7178925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7178925).length < 2 ^ (prefixWord ++ tailWord_7178925).sum := by decide
  have hdescent : baseEnd_7178925 < baseStart_7178925 := by decide
  rcases family_descends (prefixWord ++ tailWord_7178925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7178958 : List Nat := [4, 1, 1, 1, 3, 2, 1, 1, 1, 5, 3]
def baseStart_7178958 : Nat := 118140960795 + 7178958 * 2 ^ 59
def prefixEnd_7178958 : Nat := 4983230072969 + 3 ^ 40 * 7178958 * 2
def baseEnd_7178958 : Nat := 3686256052440028527509579

theorem tailTrace_7178958 : CollatzResearch.WordTrace tailWord_7178958 prefixEnd_7178958 3686256052440028527509579 := by
  unfold tailWord_7178958
  simp only [CollatzResearch.WordTrace]
  refine ⟨32729763640733588657402191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174558739417245806172811685 32729763640733588657402191)
  ·
    refine ⟨49094645461100382986103287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32729763640733588657402191 49094645461100382986103287)
    ·
      refine ⟨73641968191650574479154931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49094645461100382986103287 73641968191650574479154931)
      ·
        refine ⟨110462952287475861718732397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73641968191650574479154931 110462952287475861718732397)
        ·
          refine ⟨41423607107803448144524649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110462952287475861718732397 41423607107803448144524649)
          ·
            refine ⟨31067705330852586108393487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41423607107803448144524649 31067705330852586108393487)
            ·
              refine ⟨46601557996278879162590231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31067705330852586108393487 46601557996278879162590231)
              ·
                refine ⟨69902336994418318743885347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46601557996278879162590231 69902336994418318743885347)
                ·
                  refine ⟨104853505491627478115828021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69902336994418318743885347 104853505491627478115828021)
                  ·
                    refine ⟨9830016139840076073358877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 104853505491627478115828021 9830016139840076073358877)
                    ·
                      refine ⟨3686256052440028527509579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9830016139840076073358877 3686256052440028527509579)
                      ·
                        rfl

theorem cell23_7178958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 1, 5, 3].length) (baseStart_7178958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7178958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7178958 prefixEnd_7178958 := by exact prefixLift 7178958
  have htrace : WordTrace (prefixWord ++ tailWord_7178958) baseStart_7178958 baseEnd_7178958 := by
    simpa [prefixWord, tailWord_7178958, baseEnd_7178958] using wordTrace_append hprefix tailTrace_7178958
  have hstable : (prefixWord ++ tailWord_7178958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7178958).length < 2 ^ (prefixWord ++ tailWord_7178958).sum := by decide
  have hdescent : baseEnd_7178958 < baseStart_7178958 := by decide
  rcases family_descends (prefixWord ++ tailWord_7178958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7178961 : List Nat := [1, 2, 2, 1, 2, 3, 2, 2, 1, 7]
def baseStart_7178961 : Nat := 118140960795 + 7178961 * 2 ^ 59
def prefixEnd_7178961 : Nat := 4983230072969 + 3 ^ 40 * 7178961 * 2
def baseEnd_7178961 : Nat := 1228752530960664005257355

theorem tailTrace_7178961 : CollatzResearch.WordTrace tailWord_7178961 prefixEnd_7178961 1228752530960664005257355 := by
  unfold tailWord_7178961
  simp only [CollatzResearch.WordTrace]
  refine ⟨261838218544857840771576737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174558812363238560514384491 261838218544857840771576737)
  ·
    refine ⟨196378663908643380578682553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261838218544857840771576737 196378663908643380578682553)
    ·
      refine ⟨147283997931482535434011915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196378663908643380578682553 147283997931482535434011915)
      ·
        refine ⟨220925996897223803151017873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147283997931482535434011915 220925996897223803151017873)
        ·
          refine ⟨165694497672917852363263405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220925996897223803151017873 165694497672917852363263405)
          ·
            refine ⟨62135436627344194636223777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165694497672917852363263405 62135436627344194636223777)
            ·
              refine ⟨46601577470508145977167833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62135436627344194636223777 46601577470508145977167833)
              ·
                refine ⟨34951183102881109482875875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46601577470508145977167833 34951183102881109482875875)
                ·
                  refine ⟨52426774654321664224313813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34951183102881109482875875 52426774654321664224313813)
                  ·
                    refine ⟨1228752530960664005257355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52426774654321664224313813 1228752530960664005257355)
                    ·
                      rfl

theorem cell23_7178961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 2, 1, 7].length) (baseStart_7178961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7178961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7178961 prefixEnd_7178961 := by exact prefixLift 7178961
  have htrace : WordTrace (prefixWord ++ tailWord_7178961) baseStart_7178961 baseEnd_7178961 := by
    simpa [prefixWord, tailWord_7178961, baseEnd_7178961] using wordTrace_append hprefix tailTrace_7178961
  have hstable : (prefixWord ++ tailWord_7178961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7178961).length < 2 ^ (prefixWord ++ tailWord_7178961).sum := by decide
  have hdescent : baseEnd_7178961 < baseStart_7178961 := by decide
  rcases family_descends (prefixWord ++ tailWord_7178961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7178965 : List Nat := [1, 3, 2, 5, 1, 1, 1, 2, 7]
def baseStart_7178965 : Nat := 118140960795 + 7178965 * 2 ^ 59
def prefixEnd_7178965 : Nat := 4983230072969 + 3 ^ 40 * 7178965 * 2
def baseEnd_7178965 : Nat := 409584405200512222235783

theorem tailTrace_7178965 : CollatzResearch.WordTrace tailWord_7178965 prefixEnd_7178965 409584405200512222235783 := by
  unfold tailWord_7178965
  simp only [CollatzResearch.WordTrace]
  refine ⟨261838364436843349454722349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174558909624562232969814899 261838364436843349454722349)
  ·
    refine ⟨98189386663816256045520881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261838364436843349454722349 98189386663816256045520881)
    ·
      refine ⟨73642039997862192034140661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98189386663816256045520881 73642039997862192034140661)
      ·
        refine ⟨6903941249799580503200687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73642039997862192034140661 6903941249799580503200687)
        ·
          refine ⟨10355911874699370754801031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6903941249799580503200687 10355911874699370754801031)
          ·
            refine ⟨15533867812049056132201547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10355911874699370754801031 15533867812049056132201547)
            ·
              refine ⟨23300801718073584198302321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15533867812049056132201547 23300801718073584198302321)
              ·
                refine ⟨17475601288555188148726741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23300801718073584198302321 17475601288555188148726741)
                ·
                  refine ⟨409584405200512222235783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17475601288555188148726741 409584405200512222235783)
                  ·
                    rfl

theorem cell23_7178965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 2, 7].length) (baseStart_7178965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7178965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7178965 prefixEnd_7178965 := by exact prefixLift 7178965
  have htrace : WordTrace (prefixWord ++ tailWord_7178965) baseStart_7178965 baseEnd_7178965 := by
    simpa [prefixWord, tailWord_7178965, baseEnd_7178965] using wordTrace_append hprefix tailTrace_7178965
  have hstable : (prefixWord ++ tailWord_7178965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7178965).length < 2 ^ (prefixWord ++ tailWord_7178965).sum := by decide
  have hdescent : baseEnd_7178965 < baseStart_7178965 := by decide
  rcases family_descends (prefixWord ++ tailWord_7178965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7179001 : List Nat := [1, 2, 1, 3, 1, 1, 1, 3, 2, 3, 5]
def baseStart_7179001 : Nat := 118140960795 + 7179001 * 2 ^ 59
def prefixEnd_7179001 : Nat := 4983230072969 + 3 ^ 40 * 7179001 * 2
def baseEnd_7179001 : Nat := 3686278132108171859271881

theorem tailTrace_7179001 : CollatzResearch.WordTrace tailWord_7179001 prefixEnd_7179001 3686278132108171859271881 := by
  unfold tailWord_7179001
  simp only [CollatzResearch.WordTrace]
  refine ⟨261839677464712927603032857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174559784976475285068688571 261839677464712927603032857)
  ·
    refine ⟨196379758098534695702274643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261839677464712927603032857 196379758098534695702274643)
    ·
      refine ⟨294569637147802043553411965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196379758098534695702274643 294569637147802043553411965)
      ·
        refine ⟨110463613930425766332529487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 294569637147802043553411965 110463613930425766332529487)
        ·
          refine ⟨165695420895638649498794231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110463613930425766332529487 165695420895638649498794231)
          ·
            refine ⟨248543131343457974248191347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165695420895638649498794231 248543131343457974248191347)
            ·
              refine ⟨372814697015186961372287021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248543131343457974248191347 372814697015186961372287021)
              ·
                refine ⟨139805511380695110514607633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 372814697015186961372287021 139805511380695110514607633)
                ·
                  refine ⟨104854133535521332885955725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139805511380695110514607633 104854133535521332885955725)
                  ·
                    refine ⟨39320300075820499832233397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 104854133535521332885955725 39320300075820499832233397)
                    ·
                      refine ⟨3686278132108171859271881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39320300075820499832233397 3686278132108171859271881)
                      ·
                        rfl

theorem cell23_7179001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 3, 5].length) (baseStart_7179001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7179001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7179001 prefixEnd_7179001 := by exact prefixLift 7179001
  have htrace : WordTrace (prefixWord ++ tailWord_7179001) baseStart_7179001 baseEnd_7179001 := by
    simpa [prefixWord, tailWord_7179001, baseEnd_7179001] using wordTrace_append hprefix tailTrace_7179001
  have hstable : (prefixWord ++ tailWord_7179001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7179001).length < 2 ^ (prefixWord ++ tailWord_7179001).sum := by decide
  have hdescent : baseEnd_7179001 < baseStart_7179001 := by decide
  rcases family_descends (prefixWord ++ tailWord_7179001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7179011 : List Nat := [1, 1, 1, 3, 2, 2, 1, 1, 4, 1, 6]
def baseStart_7179011 : Nat := 118140960795 + 7179011 * 2 ^ 59
def prefixEnd_7179011 : Nat := 4983230072969 + 3 ^ 40 * 7179011 * 2
def baseEnd_7179011 : Nat := 3686283266914716820146835

theorem tailTrace_7179011 : CollatzResearch.WordTrace tailWord_7179011 prefixEnd_7179011 3686283266914716820146835 := by
  unfold tailWord_7179011
  simp only [CollatzResearch.WordTrace]
  refine ⟨261840042194676699310896887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174560028129784466207264591 261840042194676699310896887)
  ·
    refine ⟨392760063292015048966345331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261840042194676699310896887 392760063292015048966345331)
    ·
      refine ⟨589140094938022573449517997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392760063292015048966345331 589140094938022573449517997)
      ·
        refine ⟨220927535601758465043569249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 589140094938022573449517997 220927535601758465043569249)
        ·
          refine ⟨165695651701318848782676937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220927535601758465043569249 165695651701318848782676937)
          ·
            refine ⟨124271738775989136587007703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165695651701318848782676937 124271738775989136587007703)
            ·
              refine ⟨186407608163983704880511555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124271738775989136587007703 186407608163983704880511555)
              ·
                refine ⟨279611412245975557320767333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 186407608163983704880511555 279611412245975557320767333)
                ·
                  refine ⟨52427139796120416997643875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 279611412245975557320767333 52427139796120416997643875)
                  ·
                    refine ⟨78640709694180625496465813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52427139796120416997643875 78640709694180625496465813)
                    ·
                      refine ⟨3686283266914716820146835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78640709694180625496465813 3686283266914716820146835)
                      ·
                        rfl

theorem cell23_7179011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 4, 1, 6].length) (baseStart_7179011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7179011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7179011 prefixEnd_7179011 := by exact prefixLift 7179011
  have htrace : WordTrace (prefixWord ++ tailWord_7179011) baseStart_7179011 baseEnd_7179011 := by
    simpa [prefixWord, tailWord_7179011, baseEnd_7179011] using wordTrace_append hprefix tailTrace_7179011
  have hstable : (prefixWord ++ tailWord_7179011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7179011).length < 2 ^ (prefixWord ++ tailWord_7179011).sum := by decide
  have hdescent : baseEnd_7179011 < baseStart_7179011 := by decide
  rcases family_descends (prefixWord ++ tailWord_7179011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7179018 : List Nat := [3, 1, 2, 2, 1, 2, 1, 1, 3, 4, 3]
def baseStart_7179018 : Nat := 118140960795 + 7179018 * 2 ^ 59
def prefixEnd_7179018 : Nat := 4983230072969 + 3 ^ 40 * 7179018 * 2
def baseEnd_7179018 : Nat := 3686286861279298292759303

theorem tailTrace_7179018 : CollatzResearch.WordTrace tailWord_7179018 prefixEnd_7179018 3686286861279298292759303 := by
  unfold tailWord_7179018
  simp only [CollatzResearch.WordTrace]
  refine ⟨65460074376412834876600427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174560198337100893004267805 65460074376412834876600427)
  ·
    refine ⟨98190111564619252314900641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65460074376412834876600427 98190111564619252314900641)
    ·
      refine ⟨73642583673464439236175481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98190111564619252314900641 73642583673464439236175481)
      ·
        refine ⟨55231937755098329427131611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73642583673464439236175481 55231937755098329427131611)
        ·
          refine ⟨82847906632647494140697417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55231937755098329427131611 82847906632647494140697417)
          ·
            refine ⟨62135929974485620605523063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82847906632647494140697417 62135929974485620605523063)
            ·
              refine ⟨93203894961728430908284595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62135929974485620605523063 93203894961728430908284595)
              ·
                refine ⟨139805842442592646362426893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93203894961728430908284595 139805842442592646362426893)
                ·
                  refine ⟨52427190915972242385910085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 139805842442592646362426893 52427190915972242385910085)
                  ·
                    refine ⟨9830098296744795447358141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52427190915972242385910085 9830098296744795447358141)
                    ·
                      refine ⟨3686286861279298292759303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9830098296744795447358141 3686286861279298292759303)
                      ·
                        rfl

theorem cell23_7179018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 3, 4, 3].length) (baseStart_7179018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7179018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7179018 prefixEnd_7179018 := by exact prefixLift 7179018
  have htrace : WordTrace (prefixWord ++ tailWord_7179018) baseStart_7179018 baseEnd_7179018 := by
    simpa [prefixWord, tailWord_7179018, baseEnd_7179018] using wordTrace_append hprefix tailTrace_7179018
  have hstable : (prefixWord ++ tailWord_7179018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7179018).length < 2 ^ (prefixWord ++ tailWord_7179018).sum := by decide
  have hdescent : baseEnd_7179018 < baseStart_7179018 := by decide
  rcases family_descends (prefixWord ++ tailWord_7179018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7179059 : List Nat := [1, 1, 1, 2, 6, 2, 3, 2, 1, 4]
def baseStart_7179059 : Nat := 118140960795 + 7179059 * 2 ^ 59
def prefixEnd_7179059 : Nat := 4983230072969 + 3 ^ 40 * 7179059 * 2
def baseEnd_7179059 : Nat := 1228769304662044210782205

theorem tailTrace_7179059 : CollatzResearch.WordTrace tailWord_7179059 prefixEnd_7179059 1228769304662044210782205 := by
  unfold tailWord_7179059
  simp only [CollatzResearch.WordTrace]
  refine ⟨261841792898502803508644231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174561195265668535672429487 261841792898502803508644231)
  ·
    refine ⟨392762689347754205262966347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261841792898502803508644231 392762689347754205262966347)
    ·
      refine ⟨589144034021631307894449521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392762689347754205262966347 589144034021631307894449521)
      ·
        refine ⟨441858025516223480920837141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 589144034021631307894449521 441858025516223480920837141)
        ·
          refine ⟨20712094946072975668164241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 441858025516223480920837141 20712094946072975668164241)
          ·
            refine ⟨15534071209554731751123181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20712094946072975668164241 15534071209554731751123181)
            ·
              refine ⟨5825276703583024406671193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15534071209554731751123181 5825276703583024406671193)
              ·
                refine ⟨4368957527687268305003395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5825276703583024406671193 4368957527687268305003395)
                ·
                  refine ⟨6553436291530902457505093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4368957527687268305003395 6553436291530902457505093)
                  ·
                    refine ⟨1228769304662044210782205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6553436291530902457505093 1228769304662044210782205)
                    ·
                      rfl

theorem cell23_7179059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 3, 2, 1, 4].length) (baseStart_7179059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7179059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7179059 prefixEnd_7179059 := by exact prefixLift 7179059
  have htrace : WordTrace (prefixWord ++ tailWord_7179059) baseStart_7179059 baseEnd_7179059 := by
    simpa [prefixWord, tailWord_7179059, baseEnd_7179059] using wordTrace_append hprefix tailTrace_7179059
  have hstable : (prefixWord ++ tailWord_7179059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7179059).length < 2 ^ (prefixWord ++ tailWord_7179059).sum := by decide
  have hdescent : baseEnd_7179059 < baseStart_7179059 := by decide
  rcases family_descends (prefixWord ++ tailWord_7179059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7179068 : List Nat := [2, 2, 2, 2, 1, 1, 1, 4, 3, 5]
def baseStart_7179068 : Nat := 118140960795 + 7179068 * 2 ^ 59
def prefixEnd_7179068 : Nat := 4983230072969 + 3 ^ 40 * 7179068 * 2
def baseEnd_7179068 : Nat := 1228770845104007699044691

theorem tailTrace_7179068 : CollatzResearch.WordTrace tailWord_7179068 prefixEnd_7179068 1228770845104007699044691 := by
  unfold tailWord_7179068
  simp only [CollatzResearch.WordTrace]
  refine ⟨130921060577735099022860929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174561414103646798697147905 130921060577735099022860929)
  ·
    refine ⟨98190795433301324267145697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130921060577735099022860929 98190795433301324267145697)
    ·
      refine ⟨73643096574975993200359273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98190795433301324267145697 73643096574975993200359273)
      ·
        refine ⟨55232322431231994900269455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73643096574975993200359273 55232322431231994900269455)
        ·
          refine ⟨82848483646847992350404183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55232322431231994900269455 82848483646847992350404183)
          ·
            refine ⟨124272725470271988525606275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82848483646847992350404183 124272725470271988525606275)
            ·
              refine ⟨186409088205407982788409413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124272725470271988525606275 186409088205407982788409413)
              ·
                refine ⟨34951704038513996772826765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 186409088205407982788409413 34951704038513996772826765)
                ·
                  refine ⟨13106889014442748789810037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34951704038513996772826765 13106889014442748789810037)
                  ·
                    refine ⟨1228770845104007699044691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13106889014442748789810037 1228770845104007699044691)
                    ·
                      rfl

theorem cell23_7179068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 4, 3, 5].length) (baseStart_7179068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7179068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7179068 prefixEnd_7179068 := by exact prefixLift 7179068
  have htrace : WordTrace (prefixWord ++ tailWord_7179068) baseStart_7179068 baseEnd_7179068 := by
    simpa [prefixWord, tailWord_7179068, baseEnd_7179068] using wordTrace_append hprefix tailTrace_7179068
  have hstable : (prefixWord ++ tailWord_7179068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7179068).length < 2 ^ (prefixWord ++ tailWord_7179068).sum := by decide
  have hdescent : baseEnd_7179068 < baseStart_7179068 := by decide
  rcases family_descends (prefixWord ++ tailWord_7179068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7179075 : List Nat := [1, 1, 1, 3, 1, 4, 1, 2, 4, 3, 2]
def baseStart_7179075 : Nat := 118140960795 + 7179075 * 2 ^ 59
def prefixEnd_7179075 : Nat := 4983230072969 + 3 ^ 40 * 7179075 * 2
def baseEnd_7179075 : Nat := 3686316129676604569746541

theorem tailTrace_7179075 : CollatzResearch.WordTrace tailWord_7179075 prefixEnd_7179075 3686316129676604569746541 := by
  unfold tailWord_7179075
  simp only [CollatzResearch.WordTrace]
  refine ⟨261842376466444838241226679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174561584310963225494151119 261842376466444838241226679)
  ·
    refine ⟨392763564699667257361840019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261842376466444838241226679 392763564699667257361840019)
    ·
      refine ⟨589145347049500886042760029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392763564699667257361840019 589145347049500886042760029)
      ·
        refine ⟨220929505143562832266035011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 589145347049500886042760029 220929505143562832266035011)
        ·
          refine ⟨331394257715344248399052517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220929505143562832266035011 331394257715344248399052517)
          ·
            refine ⟨62136423321627046574822347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 331394257715344248399052517 62136423321627046574822347)
            ·
              refine ⟨93204634982440569862233521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62136423321627046574822347 93204634982440569862233521)
              ·
                refine ⟨69903476236830427396675141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93204634982440569862233521 69903476236830427396675141)
                ·
                  refine ⟨13106901794405705136876589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69903476236830427396675141 13106901794405705136876589)
                  ·
                    refine ⟨4915088172902139426328721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13106901794405705136876589 4915088172902139426328721)
                    ·
                      refine ⟨3686316129676604569746541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4915088172902139426328721 3686316129676604569746541)
                      ·
                        rfl

theorem cell23_7179075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 4, 3, 2].length) (baseStart_7179075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7179075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7179075 prefixEnd_7179075 := by exact prefixLift 7179075
  have htrace : WordTrace (prefixWord ++ tailWord_7179075) baseStart_7179075 baseEnd_7179075 := by
    simpa [prefixWord, tailWord_7179075, baseEnd_7179075] using wordTrace_append hprefix tailTrace_7179075
  have hstable : (prefixWord ++ tailWord_7179075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7179075).length < 2 ^ (prefixWord ++ tailWord_7179075).sum := by decide
  have hdescent : baseEnd_7179075 < baseStart_7179075 := by decide
  rcases family_descends (prefixWord ++ tailWord_7179075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7179098 : List Nat := [3, 1, 1, 2, 1, 4, 1, 1, 3, 6]
def baseStart_7179098 : Nat := 118140960795 + 7179098 * 2 ^ 59
def prefixEnd_7179098 : Nat := 4983230072969 + 3 ^ 40 * 7179098 * 2
def baseEnd_7179098 : Nat := 1228775979910552659919645

theorem tailTrace_7179098 : CollatzResearch.WordTrace tailWord_7179098 prefixEnd_7179098 1228775979910552659919645 := by
  unfold tailWord_7179098
  simp only [CollatzResearch.WordTrace]
  refine ⟨65460803836340378292328487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174562143563574342112875965 65460803836340378292328487)
  ·
    refine ⟨98191205754510567438492731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65460803836340378292328487 98191205754510567438492731)
    ·
      refine ⟨147286808631765851157739097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98191205754510567438492731 147286808631765851157739097)
      ·
        refine ⟨110465106473824388368304323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147286808631765851157739097 110465106473824388368304323)
        ·
          refine ⟨165697659710736582552456485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110465106473824388368304323 165697659710736582552456485)
          ·
            refine ⟨31068311195763109228585591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 165697659710736582552456485 31068311195763109228585591)
            ·
              refine ⟨46602466793644663842878387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31068311195763109228585591 46602466793644663842878387)
              ·
                refine ⟨69903700190466995764317581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46602466793644663842878387 69903700190466995764317581)
                ·
                  refine ⟨26213887571425123411619093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69903700190466995764317581 26213887571425123411619093)
                  ·
                    refine ⟨1228775979910552659919645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26213887571425123411619093 1228775979910552659919645)
                    ·
                      rfl

theorem cell23_7179098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 3, 6].length) (baseStart_7179098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7179098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7179098 prefixEnd_7179098 := by exact prefixLift 7179098
  have htrace : WordTrace (prefixWord ++ tailWord_7179098) baseStart_7179098 baseEnd_7179098 := by
    simpa [prefixWord, tailWord_7179098, baseEnd_7179098] using wordTrace_append hprefix tailTrace_7179098
  have hstable : (prefixWord ++ tailWord_7179098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7179098).length < 2 ^ (prefixWord ++ tailWord_7179098).sum := by decide
  have hdescent : baseEnd_7179098 < baseStart_7179098 := by decide
  rcases family_descends (prefixWord ++ tailWord_7179098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7179115 : List Nat := [1, 1, 1, 1, 2, 2, 5, 4, 2, 4]
def baseStart_7179115 : Nat := 118140960795 + 7179115 * 2 ^ 59
def prefixEnd_7179115 : Nat := 4983230072969 + 3 ^ 40 * 7179115 * 2
def baseEnd_7179115 : Nat := 1228778889634261471082119

theorem tailTrace_7179115 : CollatzResearch.WordTrace tailWord_7179115 prefixEnd_7179115 1228778889634261471082119 := by
  unfold tailWord_7179115
  simp only [CollatzResearch.WordTrace]
  refine ⟨261843835386299925072682799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174562556924199950048455199 261843835386299925072682799)
  ·
    refine ⟨392765753079449887609024199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261843835386299925072682799 392765753079449887609024199)
    ·
      refine ⟨589148629619174831413536299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392765753079449887609024199 589148629619174831413536299)
      ·
        refine ⟨883722944428762247120304449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 589148629619174831413536299 883722944428762247120304449)
        ·
          refine ⟨662792208321571685340228337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 883722944428762247120304449 662792208321571685340228337)
          ·
            refine ⟨497094156241178764005171253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 662792208321571685340228337 497094156241178764005171253)
            ·
              refine ⟨46602577147610509125484805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 497094156241178764005171253 46602577147610509125484805)
              ·
                refine ⟨8737983215176970461028401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46602577147610509125484805 8737983215176970461028401)
                ·
                  refine ⟨6553487411382727845771301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8737983215176970461028401 6553487411382727845771301)
                  ·
                    refine ⟨1228778889634261471082119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6553487411382727845771301 1228778889634261471082119)
                    ·
                      rfl

theorem cell23_7179115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 4, 2, 4].length) (baseStart_7179115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7179115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7179115 prefixEnd_7179115 := by exact prefixLift 7179115
  have htrace : WordTrace (prefixWord ++ tailWord_7179115) baseStart_7179115 baseEnd_7179115 := by
    simpa [prefixWord, tailWord_7179115, baseEnd_7179115] using wordTrace_append hprefix tailTrace_7179115
  have hstable : (prefixWord ++ tailWord_7179115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7179115).length < 2 ^ (prefixWord ++ tailWord_7179115).sum := by decide
  have hdescent : baseEnd_7179115 < baseStart_7179115 := by decide
  rcases family_descends (prefixWord ++ tailWord_7179115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7179145 : List Nat := [1, 2, 1, 1, 5, 3, 3, 7]
def baseStart_7179145 : Nat := 118140960795 + 7179145 * 2 ^ 59
def prefixEnd_7179145 : Nat := 4983230072969 + 3 ^ 40 * 7179145 * 2
def baseEnd_7179145 : Nat := 136531558271200714661897

theorem tailTrace_7179145 : CollatzResearch.WordTrace tailWord_7179145 prefixEnd_7179145 136531558271200714661897 := by
  unfold tailWord_7179145
  simp only [CollatzResearch.WordTrace]
  refine ⟨261844929576191240196274889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174563286384127493464183259 261844929576191240196274889)
  ·
    refine ⟨196383697182143430147206167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261844929576191240196274889 196383697182143430147206167)
    ·
      refine ⟨294575545773215145220809251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196383697182143430147206167 294575545773215145220809251)
      ·
        refine ⟨441863318659822717831213877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294575545773215145220809251 441863318659822717831213877)
        ·
          refine ⟨41424686124358379796676301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 441863318659822717831213877 41424686124358379796676301)
          ·
            refine ⟨15534257296634392423753613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41424686124358379796676301 15534257296634392423753613)
            ·
              refine ⟨5825346486237897158907605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15534257296634392423753613 5825346486237897158907605)
              ·
                refine ⟨136531558271200714661897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5825346486237897158907605 136531558271200714661897)
                ·
                  rfl

theorem cell23_7179145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 3, 7].length) (baseStart_7179145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7179145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7179145 prefixEnd_7179145 := by exact prefixLift 7179145
  have htrace : WordTrace (prefixWord ++ tailWord_7179145) baseStart_7179145 baseEnd_7179145 := by
    simpa [prefixWord, tailWord_7179145, baseEnd_7179145] using wordTrace_append hprefix tailTrace_7179145
  have hstable : (prefixWord ++ tailWord_7179145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7179145).length < 2 ^ (prefixWord ++ tailWord_7179145).sum := by decide
  have hdescent : baseEnd_7179145 < baseStart_7179145 := by decide
  rcases family_descends (prefixWord ++ tailWord_7179145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7179172 : List Nat := [2, 3, 1, 2, 1, 2, 3, 1, 4, 1, 3]
def baseStart_7179172 : Nat := 118140960795 + 7179172 * 2 ^ 59
def prefixEnd_7179172 : Nat := 4983230072969 + 3 ^ 40 * 7179172 * 2
def baseEnd_7179172 : Nat := 3686365937300090690233595

theorem tailTrace_7179172 : CollatzResearch.WordTrace tailWord_7179172 prefixEnd_7179172 3686365937300090690233595 := by
  unfold tailWord_7179172
  simp only [CollatzResearch.WordTrace]
  refine ⟨130922957173546711903753885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174563942898062282538338513 130922957173546711903753885)
  ·
    refine ⟨49096108940080016963907707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130922957173546711903753885 49096108940080016963907707)
    ·
      refine ⟨73644163410120025445861561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49096108940080016963907707 73644163410120025445861561)
      ·
        refine ⟨55233122557590019084396171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73644163410120025445861561 55233122557590019084396171)
        ·
          refine ⟨82849683836385028626594257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55233122557590019084396171 82849683836385028626594257)
          ·
            refine ⟨62137262877288771469945693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82849683836385028626594257 62137262877288771469945693)
            ·
              refine ⟨23301473578983289301229635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62137262877288771469945693 23301473578983289301229635)
              ·
                refine ⟨34952210368474933951844453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23301473578983289301229635 34952210368474933951844453)
                ·
                  refine ⟨6553539444089050115970835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34952210368474933951844453 6553539444089050115970835)
                  ·
                    refine ⟨9830309166133575173956253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6553539444089050115970835 9830309166133575173956253)
                    ·
                      refine ⟨3686365937300090690233595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9830309166133575173956253 3686365937300090690233595)
                      ·
                        rfl

theorem cell23_7179172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 1, 4, 1, 3].length) (baseStart_7179172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7179172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7179172 prefixEnd_7179172 := by exact prefixLift 7179172
  have htrace : WordTrace (prefixWord ++ tailWord_7179172) baseStart_7179172 baseEnd_7179172 := by
    simpa [prefixWord, tailWord_7179172, baseEnd_7179172] using wordTrace_append hprefix tailTrace_7179172
  have hstable : (prefixWord ++ tailWord_7179172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7179172).length < 2 ^ (prefixWord ++ tailWord_7179172).sum := by decide
  have hdescent : baseEnd_7179172 < baseStart_7179172 := by decide
  rcases family_descends (prefixWord ++ tailWord_7179172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7179212 : List Nat := [2, 2, 1, 4, 1, 1, 2, 1, 3, 4, 2]
def baseStart_7179212 : Nat := 118140960795 + 7179212 * 2 ^ 59
def prefixEnd_7179212 : Nat := 4983230072969 + 3 ^ 40 * 7179212 * 2
def baseEnd_7179212 : Nat := 3686386476526270533733411

theorem tailTrace_7179212 : CollatzResearch.WordTrace tailWord_7179212 prefixEnd_7179212 3686386476526270533733411 := by
  unfold tailWord_7179212
  simp only [CollatzResearch.WordTrace]
  refine ⟨130923686633474255319481945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174564915511299007092642593 130923686633474255319481945)
  ·
    refine ⟨98192764975105691489611459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130923686633474255319481945 98192764975105691489611459)
    ·
      refine ⟨147289147462658537234417189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98192764975105691489611459 147289147462658537234417189)
      ·
        refine ⟨27616715149248475731453223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 147289147462658537234417189 27616715149248475731453223)
        ·
          refine ⟨41425072723872713597179835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27616715149248475731453223 41425072723872713597179835)
          ·
            refine ⟨62137609085809070395769753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41425072723872713597179835 62137609085809070395769753)
            ·
              refine ⟨46603206814356802796827315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62137609085809070395769753 46603206814356802796827315)
              ·
                refine ⟨69904810221535204195240973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46603206814356802796827315 69904810221535204195240973)
                ·
                  refine ⟨26214303833075701573215365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69904810221535204195240973 26214303833075701573215365)
                  ·
                    refine ⟨4915181968701694044977881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26214303833075701573215365 4915181968701694044977881)
                    ·
                      refine ⟨3686386476526270533733411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4915181968701694044977881 3686386476526270533733411)
                      ·
                        rfl

theorem cell23_7179212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 1, 3, 4, 2].length) (baseStart_7179212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7179212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7179212 prefixEnd_7179212 := by exact prefixLift 7179212
  have htrace : WordTrace (prefixWord ++ tailWord_7179212) baseStart_7179212 baseEnd_7179212 := by
    simpa [prefixWord, tailWord_7179212, baseEnd_7179212] using wordTrace_append hprefix tailTrace_7179212
  have hstable : (prefixWord ++ tailWord_7179212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7179212).length < 2 ^ (prefixWord ++ tailWord_7179212).sum := by decide
  have hdescent : baseEnd_7179212 < baseStart_7179212 := by decide
  rcases family_descends (prefixWord ++ tailWord_7179212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7179215 : List Nat := [1, 1, 2, 1, 1, 7, 1, 1, 2, 1, 5]
def baseStart_7179215 : Nat := 118140960795 + 7179215 * 2 ^ 59
def prefixEnd_7179215 : Nat := 4983230072969 + 3 ^ 40 * 7179215 * 2
def baseEnd_7179215 : Nat := 3686388016968234021995897

theorem tailTrace_7179215 : CollatzResearch.WordTrace tailWord_7179215 prefixEnd_7179215 3686388016968234021995897 := by
  unfold tailWord_7179215
  simp only [CollatzResearch.WordTrace]
  refine ⟨261847482685937642151323099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174564988457291761434215399 261847482685937642151323099)
  ·
    refine ⟨392771224028906463226984649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261847482685937642151323099 392771224028906463226984649)
    ·
      refine ⟨294578418021679847420238487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 392771224028906463226984649 294578418021679847420238487)
      ·
        refine ⟨441867627032519771130357731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294578418021679847420238487 441867627032519771130357731)
        ·
          refine ⟨662801440548779656695536597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 441867627032519771130357731 662801440548779656695536597)
          ·
            refine ⟨15534408762862023203801639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 662801440548779656695536597 15534408762862023203801639)
            ·
              refine ⟨23301613144293034805702459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15534408762862023203801639 23301613144293034805702459)
              ·
                refine ⟨34952419716439552208553689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23301613144293034805702459 34952419716439552208553689)
                ·
                  refine ⟨26214314787329664156415267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34952419716439552208553689 26214314787329664156415267)
                  ·
                    refine ⟨39321472180994496234622901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26214314787329664156415267 39321472180994496234622901)
                    ·
                      refine ⟨3686388016968234021995897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39321472180994496234622901 3686388016968234021995897)
                      ·
                        rfl

theorem cell23_7179215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 1, 2, 1, 5].length) (baseStart_7179215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7179215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7179215 prefixEnd_7179215 := by exact prefixLift 7179215
  have htrace : WordTrace (prefixWord ++ tailWord_7179215) baseStart_7179215 baseEnd_7179215 := by
    simpa [prefixWord, tailWord_7179215, baseEnd_7179215] using wordTrace_append hprefix tailTrace_7179215
  have hstable : (prefixWord ++ tailWord_7179215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7179215).length < 2 ^ (prefixWord ++ tailWord_7179215).sum := by decide
  have hdescent : baseEnd_7179215 < baseStart_7179215 := by decide
  rcases family_descends (prefixWord ++ tailWord_7179215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7179250 : List Nat := [3, 2, 1, 5, 2, 1, 1, 2, 1, 3, 2]
def baseStart_7179250 : Nat := 118140960795 + 7179250 * 2 ^ 59
def prefixEnd_7179250 : Nat := 4983230072969 + 3 ^ 40 * 7179250 * 2
def baseEnd_7179250 : Nat := 3686405988791141385058237

theorem tailTrace_7179250 : CollatzResearch.WordTrace tailWord_7179250 prefixEnd_7179250 3686405988791141385058237 := by
  unfold tailWord_7179250
  simp only [CollatzResearch.WordTrace]
  refine ⟨65462189810202710782211801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174565839493873895419231469 65462189810202710782211801)
  ·
    refine ⟨49096642357652033086658851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65462189810202710782211801 49096642357652033086658851)
    ·
      refine ⟨73644963536478049629988277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49096642357652033086658851 73644963536478049629988277)
      ·
        refine ⟨6904215331544817152811401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73644963536478049629988277 6904215331544817152811401)
        ·
          refine ⟨5178161498658612864608551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6904215331544817152811401 5178161498658612864608551)
          ·
            refine ⟨7767242247987919296912827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5178161498658612864608551 7767242247987919296912827)
            ·
              refine ⟨11650863371981878945369241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7767242247987919296912827 11650863371981878945369241)
              ·
                refine ⟨8738147528986409209026931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11650863371981878945369241 8738147528986409209026931)
                ·
                  refine ⟨13107221293479613813540397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8738147528986409209026931 13107221293479613813540397)
                  ·
                    refine ⟨4915207985054855180077649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13107221293479613813540397 4915207985054855180077649)
                    ·
                      refine ⟨3686405988791141385058237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4915207985054855180077649 3686405988791141385058237)
                      ·
                        rfl

theorem cell23_7179250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_7179250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7179250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7179250 prefixEnd_7179250 := by exact prefixLift 7179250
  have htrace : WordTrace (prefixWord ++ tailWord_7179250) baseStart_7179250 baseEnd_7179250 := by
    simpa [prefixWord, tailWord_7179250, baseEnd_7179250] using wordTrace_append hprefix tailTrace_7179250
  have hstable : (prefixWord ++ tailWord_7179250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7179250).length < 2 ^ (prefixWord ++ tailWord_7179250).sum := by decide
  have hdescent : baseEnd_7179250 < baseStart_7179250 := by decide
  rcases family_descends (prefixWord ++ tailWord_7179250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7179275 : List Nat := [1, 1, 1, 1, 6, 2, 1, 2, 1, 2, 5]
def baseStart_7179275 : Nat := 118140960795 + 7179275 * 2 ^ 59
def prefixEnd_7179275 : Nat := 4983230072969 + 3 ^ 40 * 7179275 * 2
def baseEnd_7179275 : Nat := 3686418825807503787245621

theorem tailTrace_7179275 : CollatzResearch.WordTrace tailWord_7179275 prefixEnd_7179275 3686418825807503787245621 := by
  unfold tailWord_7179275
  simp only [CollatzResearch.WordTrace]
  refine ⟨261849671065720272398507279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174566447377146848265671519 261849671065720272398507279)
  ·
    refine ⟨392774506598580408597760919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261849671065720272398507279 392774506598580408597760919)
    ·
      refine ⟨589161759897870612896641379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392774506598580408597760919 589161759897870612896641379)
      ·
        refine ⟨883742639846805919344962069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 589161759897870612896641379 883742639846805919344962069)
        ·
          refine ⟨41425436242819027469295097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 883742639846805919344962069 41425436242819027469295097)
          ·
            refine ⟨31069077182114270601971323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41425436242819027469295097 31069077182114270601971323)
            ·
              refine ⟨46603615773171405902956985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31069077182114270601971323 46603615773171405902956985)
              ·
                refine ⟨34952711829878554427217739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46603615773171405902956985 34952711829878554427217739)
                ·
                  refine ⟨52429067744817831640826609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34952711829878554427217739 52429067744817831640826609)
                  ·
                    refine ⟨39321800808613373730619957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52429067744817831640826609 39321800808613373730619957)
                    ·
                      refine ⟨3686418825807503787245621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39321800808613373730619957 3686418825807503787245621)
                      ·
                        rfl

theorem cell23_7179275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 2, 1, 2, 5].length) (baseStart_7179275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7179275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7179275 prefixEnd_7179275 := by exact prefixLift 7179275
  have htrace : WordTrace (prefixWord ++ tailWord_7179275) baseStart_7179275 baseEnd_7179275 := by
    simpa [prefixWord, tailWord_7179275, baseEnd_7179275] using wordTrace_append hprefix tailTrace_7179275
  have hstable : (prefixWord ++ tailWord_7179275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7179275).length < 2 ^ (prefixWord ++ tailWord_7179275).sum := by decide
  have hdescent : baseEnd_7179275 < baseStart_7179275 := by decide
  rcases family_descends (prefixWord ++ tailWord_7179275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7179312 : List Nat := [2, 1, 1, 1, 2, 4, 3, 2, 3, 4]
def baseStart_7179312 : Nat := 118140960795 + 7179312 * 2 ^ 59
def prefixEnd_7179312 : Nat := 4983230072969 + 3 ^ 40 * 7179312 * 2
def baseEnd_7179312 : Nat := 1228812608197240047494317

theorem tailTrace_7179312 : CollatzResearch.WordTrace tailWord_7179312 prefixEnd_7179312 1228812608197240047494317 := by
  unfold tailWord_7179312
  simp only [CollatzResearch.WordTrace]
  refine ⟨130925510283293113858802095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174567347044390818478402793 130925510283293113858802095)
  ·
    refine ⟨196388265424939670788203143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130925510283293113858802095 196388265424939670788203143)
    ·
      refine ⟨294582398137409506182304715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196388265424939670788203143 294582398137409506182304715)
      ·
        refine ⟨441873597206114259273457073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294582398137409506182304715 441873597206114259273457073)
        ·
          refine ⟨331405197904585694455092805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 441873597206114259273457073 331405197904585694455092805)
          ·
            refine ⟨62138474607109817710329901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 331405197904585694455092805 62138474607109817710329901)
            ·
              refine ⟨23301927977666181641373713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62138474607109817710329901 23301927977666181641373713)
              ·
                refine ⟨17476445983249636231030285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23301927977666181641373713 17476445983249636231030285)
                ·
                  refine ⟨6553667243718613586636357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17476445983249636231030285 6553667243718613586636357)
                  ·
                    refine ⟨1228812608197240047494317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6553667243718613586636357 1228812608197240047494317)
                    ·
                      rfl

theorem cell23_7179312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 2, 3, 4].length) (baseStart_7179312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7179312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7179312 prefixEnd_7179312 := by exact prefixLift 7179312
  have htrace : WordTrace (prefixWord ++ tailWord_7179312) baseStart_7179312 baseEnd_7179312 := by
    simpa [prefixWord, tailWord_7179312, baseEnd_7179312] using wordTrace_append hprefix tailTrace_7179312
  have hstable : (prefixWord ++ tailWord_7179312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7179312).length < 2 ^ (prefixWord ++ tailWord_7179312).sum := by decide
  have hdescent : baseEnd_7179312 < baseStart_7179312 := by decide
  rcases family_descends (prefixWord ++ tailWord_7179312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7179316 : List Nat := [2, 5, 1, 2, 1, 3, 1, 1, 2, 5]
def baseStart_7179316 : Nat := 118140960795 + 7179316 * 2 ^ 59
def prefixEnd_7179316 : Nat := 4983230072969 + 3 ^ 40 * 7179316 * 2
def baseEnd_7179316 : Nat := 1228813292838112708944311

theorem tailTrace_7179316 : CollatzResearch.WordTrace tailWord_7179316 prefixEnd_7179316 1228813292838112708944311 := by
  unfold tailWord_7179316
  simp only [CollatzResearch.WordTrace]
  refine ⟨130925583229285868200374901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174567444305714490933833201 130925583229285868200374901)
  ·
    refine ⟨12274273427745550143785147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 130925583229285868200374901 12274273427745550143785147)
    ·
      refine ⟨18411410141618325215677721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12274273427745550143785147 18411410141618325215677721)
      ·
        refine ⟨13808557606213743911758291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18411410141618325215677721 13808557606213743911758291)
        ·
          refine ⟨20712836409320615867637437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13808557606213743911758291 20712836409320615867637437)
          ·
            refine ⟨7767313653495230950364039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20712836409320615867637437 7767313653495230950364039)
            ·
              refine ⟨11650970480242846425546059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7767313653495230950364039 11650970480242846425546059)
              ·
                refine ⟨17476455720364269638319089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11650970480242846425546059 17476455720364269638319089)
                ·
                  refine ⟨13107341790273202228739317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17476455720364269638319089 13107341790273202228739317)
                  ·
                    refine ⟨1228813292838112708944311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13107341790273202228739317 1228813292838112708944311)
                    ·
                      rfl

theorem cell23_7179316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_7179316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7179316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7179316 prefixEnd_7179316 := by exact prefixLift 7179316
  have htrace : WordTrace (prefixWord ++ tailWord_7179316) baseStart_7179316 baseEnd_7179316 := by
    simpa [prefixWord, tailWord_7179316, baseEnd_7179316] using wordTrace_append hprefix tailTrace_7179316
  have hstable : (prefixWord ++ tailWord_7179316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7179316).length < 2 ^ (prefixWord ++ tailWord_7179316).sum := by decide
  have hdescent : baseEnd_7179316 < baseStart_7179316 := by decide
  rcases family_descends (prefixWord ++ tailWord_7179316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7179345 : List Nat := [1, 2, 2, 1, 3, 1, 3, 1, 1, 2, 6]
def baseStart_7179345 : Nat := 118140960795 + 7179345 * 2 ^ 59
def prefixEnd_7179345 : Nat := 4983230072969 + 3 ^ 40 * 7179345 * 2
def baseEnd_7179345 : Nat := 3686454769453318513370299

theorem tailTrace_7179345 : CollatzResearch.WordTrace tailWord_7179345 prefixEnd_7179345 3686454769453318513370299 := by
  unfold tailWord_7179345
  simp only [CollatzResearch.WordTrace]
  refine ⟨261852224175466674353555489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174568149450311116235703659 261852224175466674353555489)
  ·
    refine ⟨196389168131600005765166617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261852224175466674353555489 196389168131600005765166617)
    ·
      refine ⟨147291876098700004323874963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196389168131600005765166617 147291876098700004323874963)
      ·
        refine ⟨220937814148050006485812445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147291876098700004323874963 220937814148050006485812445)
        ·
          refine ⟨82851680305518752432179667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 220937814148050006485812445 82851680305518752432179667)
          ·
            refine ⟨124277520458278128648269501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82851680305518752432179667 124277520458278128648269501)
            ·
              refine ⟨46604070171854298243101063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124277520458278128648269501 46604070171854298243101063)
              ·
                refine ⟨69906105257781447364651595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46604070171854298243101063 69906105257781447364651595)
                ·
                  refine ⟨104859157886672171046977393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69906105257781447364651595 104859157886672171046977393)
                  ·
                    refine ⟨78644368415004128285233045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 104859157886672171046977393 78644368415004128285233045)
                    ·
                      refine ⟨3686454769453318513370299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78644368415004128285233045 3686454769453318513370299)
                      ·
                        rfl

theorem cell23_7179345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 2, 6].length) (baseStart_7179345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7179345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7179345 prefixEnd_7179345 := by exact prefixLift 7179345
  have htrace : WordTrace (prefixWord ++ tailWord_7179345) baseStart_7179345 baseEnd_7179345 := by
    simpa [prefixWord, tailWord_7179345, baseEnd_7179345] using wordTrace_append hprefix tailTrace_7179345
  have hstable : (prefixWord ++ tailWord_7179345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7179345).length < 2 ^ (prefixWord ++ tailWord_7179345).sum := by decide
  have hdescent : baseEnd_7179345 < baseStart_7179345 := by decide
  rcases family_descends (prefixWord ++ tailWord_7179345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7179346 : List Nat := [3, 2, 2, 1, 3, 1, 2, 4, 1, 4]
def baseStart_7179346 : Nat := 118140960795 + 7179346 * 2 ^ 59
def prefixEnd_7179346 : Nat := 4983230072969 + 3 ^ 40 * 7179346 * 2
def baseEnd_7179346 : Nat := 1228818427644657669819265

theorem tailTrace_7179346 : CollatzResearch.WordTrace tailWord_7179346 prefixEnd_7179346 1228818427644657669819265 := by
  unfold tailWord_7179346
  simp only [CollatzResearch.WordTrace]
  refine ⟨65463065162115762881085473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174568173765642034349561261 65463065162115762881085473)
  ·
    refine ⟨49097298871586822160814105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65463065162115762881085473 49097298871586822160814105)
    ·
      refine ⟨36822974153690116620610579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49097298871586822160814105 36822974153690116620610579)
      ·
        refine ⟨55234461230535174930915869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36822974153690116620610579 55234461230535174930915869)
        ·
          refine ⟨20712922961450690599093451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55234461230535174930915869 20712922961450690599093451)
          ·
            refine ⟨31069384442176035898640177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20712922961450690599093451 31069384442176035898640177)
            ·
              refine ⟨23302038331632026923980133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31069384442176035898640177 23302038331632026923980133)
              ·
                refine ⟨4369132187181005048246275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23302038331632026923980133 4369132187181005048246275)
                ·
                  refine ⟨6553698280771507572369413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4369132187181005048246275 6553698280771507572369413)
                  ·
                    refine ⟨1228818427644657669819265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6553698280771507572369413 1228818427644657669819265)
                    ·
                      rfl

theorem cell23_7179346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 4, 1, 4].length) (baseStart_7179346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7179346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7179346 prefixEnd_7179346 := by exact prefixLift 7179346
  have htrace : WordTrace (prefixWord ++ tailWord_7179346) baseStart_7179346 baseEnd_7179346 := by
    simpa [prefixWord, tailWord_7179346, baseEnd_7179346] using wordTrace_append hprefix tailTrace_7179346
  have hstable : (prefixWord ++ tailWord_7179346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7179346).length < 2 ^ (prefixWord ++ tailWord_7179346).sum := by decide
  have hdescent : baseEnd_7179346 < baseStart_7179346 := by decide
  rcases family_descends (prefixWord ++ tailWord_7179346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7179369 : List Nat := [1, 2, 1, 1, 1, 6, 2, 2, 3, 1, 3]
def baseStart_7179369 : Nat := 118140960795 + 7179369 * 2 ^ 59
def prefixEnd_7179369 : Nat := 4983230072969 + 3 ^ 40 * 7179369 * 2
def baseEnd_7179369 : Nat := 3686467092989026419470189

theorem tailTrace_7179369 : CollatzResearch.WordTrace tailWord_7179369 prefixEnd_7179369 3686467092989026419470189 := by
  unfold tailWord_7179369
  simp only [CollatzResearch.WordTrace]
  refine ⟨261853099527379726452429161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174568733018253150968286107 261853099527379726452429161)
  ·
    refine ⟨196389824645534794839321871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261853099527379726452429161 196389824645534794839321871)
    ·
      refine ⟨294584736968302192258982807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196389824645534794839321871 294584736968302192258982807)
      ·
        refine ⟨441877105452453288388474211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294584736968302192258982807 441877105452453288388474211)
        ·
          refine ⟨662815658178679932582711317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 441877105452453288388474211 662815658178679932582711317)
          ·
            refine ⟨31069483977125621839814593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 662815658178679932582711317 31069483977125621839814593)
            ·
              refine ⟨23302112982844216379860945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31069483977125621839814593 23302112982844216379860945)
              ·
                refine ⟨17476584737133162284895709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23302112982844216379860945 17476584737133162284895709)
                ·
                  refine ⟨6553719276424935856835891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17476584737133162284895709 6553719276424935856835891)
                  ·
                    refine ⟨9830578914637403785253837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6553719276424935856835891 9830578914637403785253837)
                    ·
                      refine ⟨3686467092989026419470189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9830578914637403785253837 3686467092989026419470189)
                      ·
                        rfl

theorem cell23_7179369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 2, 3, 1, 3].length) (baseStart_7179369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7179369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7179369 prefixEnd_7179369 := by exact prefixLift 7179369
  have htrace : WordTrace (prefixWord ++ tailWord_7179369) baseStart_7179369 baseEnd_7179369 := by
    simpa [prefixWord, tailWord_7179369, baseEnd_7179369] using wordTrace_append hprefix tailTrace_7179369
  have hstable : (prefixWord ++ tailWord_7179369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7179369).length < 2 ^ (prefixWord ++ tailWord_7179369).sum := by decide
  have hdescent : baseEnd_7179369 < baseStart_7179369 := by decide
  rcases family_descends (prefixWord ++ tailWord_7179369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7179390 : List Nat := [4, 2, 4, 1, 1, 1, 1, 2, 2, 2, 3]
def baseStart_7179390 : Nat := 118140960795 + 7179390 * 2 ^ 59
def prefixEnd_7179390 : Nat := 4983230072969 + 3 ^ 40 * 7179390 * 2
def baseEnd_7179390 : Nat := 3686477876082770837307593

theorem tailTrace_7179390 : CollatzResearch.WordTrace tailWord_7179390 prefixEnd_7179390 3686477876082770837307593 := by
  unfold tailWord_7179390
  simp only [CollatzResearch.WordTrace]
  refine ⟨32731733182537955879867953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174569243640202431359295749 32731733182537955879867953)
  ·
    refine ⟨24548799886903466909900965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32731733182537955879867953 24548799886903466909900965)
    ·
      refine ⟨4602899978794400045606431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24548799886903466909900965 4602899978794400045606431)
      ·
        refine ⟨6904349968191600068409647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4602899978794400045606431 6904349968191600068409647)
        ·
          refine ⟨10356524952287400102614471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6904349968191600068409647 10356524952287400102614471)
          ·
            refine ⟨15534787428431100153921707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10356524952287400102614471 15534787428431100153921707)
            ·
              refine ⟨23302181142646650230882561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15534787428431100153921707 23302181142646650230882561)
              ·
                refine ⟨17476635856984987673161921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23302181142646650230882561 17476635856984987673161921)
                ·
                  refine ⟨13107476892738740754871441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17476635856984987673161921 13107476892738740754871441)
                  ·
                    refine ⟨9830607669554055566153581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13107476892738740754871441 9830607669554055566153581)
                    ·
                      refine ⟨3686477876082770837307593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9830607669554055566153581 3686477876082770837307593)
                      ·
                        rfl

theorem cell23_7179390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_7179390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7179390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7179390 prefixEnd_7179390 := by exact prefixLift 7179390
  have htrace : WordTrace (prefixWord ++ tailWord_7179390) baseStart_7179390 baseEnd_7179390 := by
    simpa [prefixWord, tailWord_7179390, baseEnd_7179390] using wordTrace_append hprefix tailTrace_7179390
  have hstable : (prefixWord ++ tailWord_7179390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7179390).length < 2 ^ (prefixWord ++ tailWord_7179390).sum := by decide
  have hdescent : baseEnd_7179390 < baseStart_7179390 := by decide
  rcases family_descends (prefixWord ++ tailWord_7179390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7179396 : List Nat := [2, 3, 2, 1, 2, 3, 1, 2, 2, 3, 2]
def baseStart_7179396 : Nat := 118140960795 + 7179396 * 2 ^ 59
def prefixEnd_7179396 : Nat := 4983230072969 + 3 ^ 40 * 7179396 * 2
def baseEnd_7179396 : Nat := 3686480956966697813832565

theorem tailTrace_7179396 : CollatzResearch.WordTrace tailWord_7179396 prefixEnd_7179396 3686480956966697813832565 := by
  unfold tailWord_7179396
  simp only [CollatzResearch.WordTrace]
  refine ⟨130927042149140955031831021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174569389532187940042441361 130927042149140955031831021)
  ·
    refine ⟨49097640805927858136936633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130927042149140955031831021 49097640805927858136936633)
    ·
      refine ⟨36823230604445893602702475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49097640805927858136936633 36823230604445893602702475)
      ·
        refine ⟨55234845906668840404053713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36823230604445893602702475 55234845906668840404053713)
        ·
          refine ⟨41426134430001630303040285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55234845906668840404053713 41426134430001630303040285)
          ·
            refine ⟨15534800411250611363640107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41426134430001630303040285 15534800411250611363640107)
            ·
              refine ⟨23302200616875917045460161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15534800411250611363640107 23302200616875917045460161)
              ·
                refine ⟨17476650462656937784095121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23302200616875917045460161 17476650462656937784095121)
                ·
                  refine ⟨13107487846992703338071341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17476650462656937784095121 13107487846992703338071341)
                  ·
                    refine ⟨4915307942622263751776753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13107487846992703338071341 4915307942622263751776753)
                    ·
                      refine ⟨3686480956966697813832565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4915307942622263751776753 3686480956966697813832565)
                      ·
                        rfl

theorem cell23_7179396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 2, 2, 3, 2].length) (baseStart_7179396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7179396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7179396 prefixEnd_7179396 := by exact prefixLift 7179396
  have htrace : WordTrace (prefixWord ++ tailWord_7179396) baseStart_7179396 baseEnd_7179396 := by
    simpa [prefixWord, tailWord_7179396, baseEnd_7179396] using wordTrace_append hprefix tailTrace_7179396
  have hstable : (prefixWord ++ tailWord_7179396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7179396).length < 2 ^ (prefixWord ++ tailWord_7179396).sum := by decide
  have hdescent : baseEnd_7179396 < baseStart_7179396 := by decide
  rcases family_descends (prefixWord ++ tailWord_7179396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7179423 : List Nat := [1, 1, 2, 6, 3, 1, 1, 2, 1, 5]
def baseStart_7179423 : Nat := 118140960795 + 7179423 * 2 ^ 59
def prefixEnd_7179423 : Nat := 4983230072969 + 3 ^ 40 * 7179423 * 2
def baseEnd_7179423 : Nat := 1228831606981456402731647

theorem tailTrace_7179423 : CollatzResearch.WordTrace tailWord_7179423 prefixEnd_7179423 1228831606981456402731647 := by
  unfold tailWord_7179423
  simp only [CollatzResearch.WordTrace]
  refine ⟨261855069069184093674894923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174570046046122729116596615 261855069069184093674894923)
  ·
    refine ⟨392782603603776140512342385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261855069069184093674894923 392782603603776140512342385)
    ·
      refine ⟨294586952702832105384256789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 392782603603776140512342385 294586952702832105384256789)
      ·
        refine ⟨13808763407945254939887037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 294586952702832105384256789 13808763407945254939887037)
        ·
          refine ⟨5178286277979470602457639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13808763407945254939887037 5178286277979470602457639)
          ·
            refine ⟨7767429416969205903686459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5178286277979470602457639 7767429416969205903686459)
            ·
              refine ⟨11651144125453808855529689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7767429416969205903686459 11651144125453808855529689)
              ·
                refine ⟨8738358094090356641647267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11651144125453808855529689 8738358094090356641647267)
                ·
                  refine ⟨13107537141135534962470901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8738358094090356641647267 13107537141135534962470901)
                  ·
                    refine ⟨1228831606981456402731647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13107537141135534962470901 1228831606981456402731647)
                    ·
                      rfl

theorem cell23_7179423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 2, 1, 5].length) (baseStart_7179423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7179423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7179423 prefixEnd_7179423 := by exact prefixLift 7179423
  have htrace : WordTrace (prefixWord ++ tailWord_7179423) baseStart_7179423 baseEnd_7179423 := by
    simpa [prefixWord, tailWord_7179423, baseEnd_7179423] using wordTrace_append hprefix tailTrace_7179423
  have hstable : (prefixWord ++ tailWord_7179423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7179423).length < 2 ^ (prefixWord ++ tailWord_7179423).sum := by decide
  have hdescent : baseEnd_7179423 < baseStart_7179423 := by decide
  rcases family_descends (prefixWord ++ tailWord_7179423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7179426 : List Nat := [3, 3, 1, 3, 2, 1, 1, 1, 3, 1, 4]
def baseStart_7179426 : Nat := 118140960795 + 7179426 * 2 ^ 59
def prefixEnd_7179426 : Nat := 4983230072969 + 3 ^ 40 * 7179426 * 2
def baseEnd_7179426 : Nat := 3686496361386332696457427

theorem tailTrace_7179426 : CollatzResearch.WordTrace tailWord_7179426 prefixEnd_7179426 3686496361386332696457427 := by
  unfold tailWord_7179426
  simp only [CollatzResearch.WordTrace]
  refine ⟨65463794622043306296813533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174570118992115483458169421 65463794622043306296813533)
  ·
    refine ⟨24548922983266239861305075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65463794622043306296813533 24548922983266239861305075)
    ·
      refine ⟨36823384474899359791957613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24548922983266239861305075 36823384474899359791957613)
      ·
        refine ⟨13808769178087259921984105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36823384474899359791957613 13808769178087259921984105)
        ·
          refine ⟨10356576883565444941488079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13808769178087259921984105 10356576883565444941488079)
          ·
            refine ⟨15534865325348167412232119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10356576883565444941488079 15534865325348167412232119)
            ·
              refine ⟨23302297988022251118348179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15534865325348167412232119 23302297988022251118348179)
              ·
                refine ⟨34953446982033376677522269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23302297988022251118348179 34953446982033376677522269)
                ·
                  refine ⟨13107542618262516254070851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34953446982033376677522269 13107542618262516254070851)
                  ·
                    refine ⟨19661313927393774381106277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13107542618262516254070851 19661313927393774381106277)
                    ·
                      refine ⟨3686496361386332696457427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19661313927393774381106277 3686496361386332696457427)
                      ·
                        rfl

theorem cell23_7179426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_7179426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7179426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7179426 prefixEnd_7179426 := by exact prefixLift 7179426
  have htrace : WordTrace (prefixWord ++ tailWord_7179426) baseStart_7179426 baseEnd_7179426 := by
    simpa [prefixWord, tailWord_7179426, baseEnd_7179426] using wordTrace_append hprefix tailTrace_7179426
  have hstable : (prefixWord ++ tailWord_7179426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7179426).length < 2 ^ (prefixWord ++ tailWord_7179426).sum := by decide
  have hdescent : baseEnd_7179426 < baseStart_7179426 := by decide
  rcases family_descends (prefixWord ++ tailWord_7179426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7179429 : List Nat := [1, 3, 1, 2, 1, 5, 1, 1, 3, 2, 3]
def baseStart_7179429 : Nat := 118140960795 + 7179429 * 2 ^ 59
def prefixEnd_7179429 : Nat := 4983230072969 + 3 ^ 40 * 7179429 * 2
def baseEnd_7179429 : Nat := 3686497901828296184719913

theorem tailTrace_7179429 : CollatzResearch.WordTrace tailWord_7179429 prefixEnd_7179429 3686497901828296184719913 := by
  unfold tailWord_7179429
  simp only [CollatzResearch.WordTrace]
  refine ⟨261855287907162356699613341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174570191938108237799742227 261855287907162356699613341)
  ·
    refine ⟨98195732965185883762355003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261855287907162356699613341 98195732965185883762355003)
    ·
      refine ⟨147293599447778825643532505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98195732965185883762355003 147293599447778825643532505)
      ·
        refine ⟨110470199585834119232649379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147293599447778825643532505 110470199585834119232649379)
        ·
          refine ⟨165705299378751178848974069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110470199585834119232649379 165705299378751178848974069)
          ·
            refine ⟨15534871816757923017091319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 165705299378751178848974069 15534871816757923017091319)
            ·
              refine ⟨23302307725136884525636979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15534871816757923017091319 23302307725136884525636979)
              ·
                refine ⟨34953461587705326788455469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23302307725136884525636979 34953461587705326788455469)
                ·
                  refine ⟨13107548095389497545670801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34953461587705326788455469 13107548095389497545670801)
                  ·
                    refine ⟨9830661071542123159253101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13107548095389497545670801 9830661071542123159253101)
                    ·
                      refine ⟨3686497901828296184719913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9830661071542123159253101 3686497901828296184719913)
                      ·
                        rfl

theorem cell23_7179429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 1, 3, 2, 3].length) (baseStart_7179429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7179429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7179429 prefixEnd_7179429 := by exact prefixLift 7179429
  have htrace : WordTrace (prefixWord ++ tailWord_7179429) baseStart_7179429 baseEnd_7179429 := by
    simpa [prefixWord, tailWord_7179429, baseEnd_7179429] using wordTrace_append hprefix tailTrace_7179429
  have hstable : (prefixWord ++ tailWord_7179429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7179429).length < 2 ^ (prefixWord ++ tailWord_7179429).sum := by decide
  have hdescent : baseEnd_7179429 < baseStart_7179429 := by decide
  rcases family_descends (prefixWord ++ tailWord_7179429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7179482 : List Nat := [3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 4]
def baseStart_7179482 : Nat := 118140960795 + 7179482 * 2 ^ 59
def prefixEnd_7179482 : Nat := 4983230072969 + 3 ^ 40 * 7179482 * 2
def baseEnd_7179482 : Nat := 3686525116302984477357169

theorem tailTrace_7179482 : CollatzResearch.WordTrace tailWord_7179482 prefixEnd_7179482 3686525116302984477357169 := by
  unfold tailWord_7179482
  simp only [CollatzResearch.WordTrace]
  refine ⟨65464305243992586687823175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174571480650646897834195133 65464305243992586687823175)
  ·
    refine ⟨98196457865988880031734763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65464305243992586687823175 98196457865988880031734763)
    ·
      refine ⟨147294686798983320047602145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98196457865988880031734763 147294686798983320047602145)
      ·
        refine ⟨110471015099237490035701609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147294686798983320047602145 110471015099237490035701609)
        ·
          refine ⟨82853261324428117526776207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110471015099237490035701609 82853261324428117526776207)
          ·
            refine ⟨124279891986642176290164311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82853261324428117526776207 124279891986642176290164311)
            ·
              refine ⟨186419837979963264435246467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124279891986642176290164311 186419837979963264435246467)
              ·
                refine ⟨279629756969944896652869701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 186419837979963264435246467 279629756969944896652869701)
                ·
                  refine ⟨52430579431864668122413069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 279629756969944896652869701 52430579431864668122413069)
                  ·
                    refine ⟨19661467286949250545904901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52430579431864668122413069 19661467286949250545904901)
                    ·
                      refine ⟨3686525116302984477357169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19661467286949250545904901 3686525116302984477357169)
                      ·
                        rfl

theorem cell23_7179482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 4].length) (baseStart_7179482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7179482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7179482 prefixEnd_7179482 := by exact prefixLift 7179482
  have htrace : WordTrace (prefixWord ++ tailWord_7179482) baseStart_7179482 baseEnd_7179482 := by
    simpa [prefixWord, tailWord_7179482, baseEnd_7179482] using wordTrace_append hprefix tailTrace_7179482
  have hstable : (prefixWord ++ tailWord_7179482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7179482).length < 2 ^ (prefixWord ++ tailWord_7179482).sum := by decide
  have hdescent : baseEnd_7179482 < baseStart_7179482 := by decide
  rcases family_descends (prefixWord ++ tailWord_7179482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7179503 : List Nat := [1, 1, 2, 1, 7, 1, 1, 3, 1, 3, 2]
def baseStart_7179503 : Nat := 118140960795 + 7179503 * 2 ^ 59
def prefixEnd_7179503 : Nat := 4983230072969 + 3 ^ 40 * 7179503 * 2
def baseEnd_7179503 : Nat := 3686535899396728895194573

theorem tailTrace_7179503 : CollatzResearch.WordTrace tailWord_7179503 prefixEnd_7179503 3686535899396728895194573 := by
  unfold tailWord_7179503
  simp only [CollatzResearch.WordTrace]
  refine ⟨261857986908894267337807163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174571991272596178225204775 261857986908894267337807163)
  ·
    refine ⟨392786980363341401006710745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261857986908894267337807163 392786980363341401006710745)
    ·
      refine ⟨294590235272506050755033059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 392786980363341401006710745 294590235272506050755033059)
      ·
        refine ⟨441885352908759076132549589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294590235272506050755033059 441885352908759076132549589)
        ·
          refine ⟨10356687958799040846856631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 441885352908759076132549589 10356687958799040846856631)
          ·
            refine ⟨15535031938198561270284947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10356687958799040846856631 15535031938198561270284947)
            ·
              refine ⟨23302547907297841905427421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15535031938198561270284947 23302547907297841905427421)
              ·
                refine ⟨8738455465236690714535283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23302547907297841905427421 8738455465236690714535283)
                ·
                  refine ⟨13107683197855036071802925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8738455465236690714535283 13107683197855036071802925)
                  ·
                    refine ⟨4915381199195638526926097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13107683197855036071802925 4915381199195638526926097)
                    ·
                      refine ⟨3686535899396728895194573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4915381199195638526926097 3686535899396728895194573)
                      ·
                        rfl

theorem cell23_7179503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 3, 1, 3, 2].length) (baseStart_7179503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7179503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7179503 prefixEnd_7179503 := by exact prefixLift 7179503
  have htrace : WordTrace (prefixWord ++ tailWord_7179503) baseStart_7179503 baseEnd_7179503 := by
    simpa [prefixWord, tailWord_7179503, baseEnd_7179503] using wordTrace_append hprefix tailTrace_7179503
  have hstable : (prefixWord ++ tailWord_7179503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7179503).length < 2 ^ (prefixWord ++ tailWord_7179503).sum := by decide
  have hdescent : baseEnd_7179503 < baseStart_7179503 := by decide
  rcases family_descends (prefixWord ++ tailWord_7179503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7179569 : List Nat := [1, 2, 2, 3, 3, 1, 1, 1, 4, 5]
def baseStart_7179569 : Nat := 118140960795 + 7179569 * 2 ^ 59
def prefixEnd_7179569 : Nat := 4983230072969 + 3 ^ 40 * 7179569 * 2
def baseEnd_7179569 : Nat := 1228856596373308545656423

theorem tailTrace_7179569 : CollatzResearch.WordTrace tailWord_7179569 prefixEnd_7179569 1228856596373308545656423 := by
  unfold tailWord_7179569
  simp only [CollatzResearch.WordTrace]
  refine ⟨261860394126655160609709761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174573596084436773739806507 261860394126655160609709761)
  ·
    refine ⟨196395295594991370457282321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261860394126655160609709761 196395295594991370457282321)
    ·
      refine ⟨147296471696243527842961741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196395295594991370457282321 147296471696243527842961741)
      ·
        refine ⟨55236176886091322941110653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147296471696243527842961741 55236176886091322941110653)
        ·
          refine ⟨20713566332284246102916495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55236176886091322941110653 20713566332284246102916495)
          ·
            refine ⟨31070349498426369154374743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20713566332284246102916495 31070349498426369154374743)
            ·
              refine ⟨46605524247639553731562115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31070349498426369154374743 46605524247639553731562115)
              ·
                refine ⟨69908286371459330597343173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46605524247639553731562115 69908286371459330597343173)
                ·
                  refine ⟨13107803694648624487001845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69908286371459330597343173 13107803694648624487001845)
                  ·
                    refine ⟨1228856596373308545656423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13107803694648624487001845 1228856596373308545656423)
                    ·
                      rfl

theorem cell23_7179569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 4, 5].length) (baseStart_7179569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7179569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7179569 prefixEnd_7179569 := by exact prefixLift 7179569
  have htrace : WordTrace (prefixWord ++ tailWord_7179569) baseStart_7179569 baseEnd_7179569 := by
    simpa [prefixWord, tailWord_7179569, baseEnd_7179569] using wordTrace_append hprefix tailTrace_7179569
  have hstable : (prefixWord ++ tailWord_7179569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7179569).length < 2 ^ (prefixWord ++ tailWord_7179569).sum := by decide
  have hdescent : baseEnd_7179569 < baseStart_7179569 := by decide
  rcases family_descends (prefixWord ++ tailWord_7179569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7179573 : List Nat := [1, 3, 3, 1, 2, 3, 3, 2, 5]
def baseStart_7179573 : Nat := 118140960795 + 7179573 * 2 ^ 59
def prefixEnd_7179573 : Nat := 4983230072969 + 3 ^ 40 * 7179573 * 2
def baseEnd_7179573 : Nat := 409619093671393735702139

theorem tailTrace_7179573 : CollatzResearch.WordTrace tailWord_7179573 prefixEnd_7179573 409619093671393735702139 := by
  unfold tailWord_7179573
  simp only [CollatzResearch.WordTrace]
  refine ⟨261860540018640669292855373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174573693345760446195236915 261860540018640669292855373)
  ·
    refine ⟨98197702506990250984820765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261860540018640669292855373 98197702506990250984820765)
    ·
      refine ⟨36824138440121344119307787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98197702506990250984820765 36824138440121344119307787)
      ·
        refine ⟨55236207660182016178961681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36824138440121344119307787 55236207660182016178961681)
        ·
          refine ⟨41427155745136512134221261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55236207660182016178961681 41427155745136512134221261)
          ·
            refine ⟨15535183404426192050332973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41427155745136512134221261 15535183404426192050332973)
            ·
              refine ⟨5825693776659822018874865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15535183404426192050332973 5825693776659822018874865)
              ·
                refine ⟨4369270332494866514156149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5825693776659822018874865 4369270332494866514156149)
                ·
                  refine ⟨409619093671393735702139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4369270332494866514156149 409619093671393735702139)
                  ·
                    rfl

theorem cell23_7179573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 3, 2, 5].length) (baseStart_7179573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7179573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7179573 prefixEnd_7179573 := by exact prefixLift 7179573
  have htrace : WordTrace (prefixWord ++ tailWord_7179573) baseStart_7179573 baseEnd_7179573 := by
    simpa [prefixWord, tailWord_7179573, baseEnd_7179573] using wordTrace_append hprefix tailTrace_7179573
  have hstable : (prefixWord ++ tailWord_7179573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7179573).length < 2 ^ (prefixWord ++ tailWord_7179573).sum := by decide
  have hdescent : baseEnd_7179573 < baseStart_7179573 := by decide
  rcases family_descends (prefixWord ++ tailWord_7179573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7179609 : List Nat := [1, 2, 1, 2, 2, 2, 2, 3, 1, 4, 3]
def baseStart_7179609 : Nat := 118140960795 + 7179609 * 2 ^ 59
def prefixEnd_7179609 : Nat := 4983230072969 + 3 ^ 40 * 7179609 * 2
def baseEnd_7179609 : Nat := 3686590328346105480469085

theorem tailTrace_7179609 : CollatzResearch.WordTrace tailWord_7179609 prefixEnd_7179609 3686590328346105480469085 := by
  unfold tailWord_7179609
  simp only [CollatzResearch.WordTrace]
  refine ⟨261861853046510247441165881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174574568697673498294110587 261861853046510247441165881)
  ·
    refine ⟨196396389784882685580874411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261861853046510247441165881 196396389784882685580874411)
    ·
      refine ⟨294594584677324028371311617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196396389784882685580874411 294594584677324028371311617)
      ·
        refine ⟨220945938507993021278483713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 294594584677324028371311617 220945938507993021278483713)
        ·
          refine ⟨165709453880994765958862785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220945938507993021278483713 165709453880994765958862785)
          ·
            refine ⟨124282090410746074469147089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165709453880994765958862785 124282090410746074469147089)
            ·
              refine ⟨93211567808059555851860317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124282090410746074469147089 93211567808059555851860317)
              ·
                refine ⟨34954337928022333444447619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93211567808059555851860317 34954337928022333444447619)
                ·
                  refine ⟨52431506892033500166671429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34954337928022333444447619 52431506892033500166671429)
                  ·
                    refine ⟨9830907542256281281250893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52431506892033500166671429 9830907542256281281250893)
                    ·
                      refine ⟨3686590328346105480469085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9830907542256281281250893 3686590328346105480469085)
                      ·
                        rfl

theorem cell23_7179609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 3, 1, 4, 3].length) (baseStart_7179609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7179609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7179609 prefixEnd_7179609 := by exact prefixLift 7179609
  have htrace : WordTrace (prefixWord ++ tailWord_7179609) baseStart_7179609 baseEnd_7179609 := by
    simpa [prefixWord, tailWord_7179609, baseEnd_7179609] using wordTrace_append hprefix tailTrace_7179609
  have hstable : (prefixWord ++ tailWord_7179609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7179609).length < 2 ^ (prefixWord ++ tailWord_7179609).sum := by decide
  have hdescent : baseEnd_7179609 < baseStart_7179609 := by decide
  rcases family_descends (prefixWord ++ tailWord_7179609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7179650 : List Nat := [3, 4, 2, 1, 1, 2, 1, 2, 3, 4]
def baseStart_7179650 : Nat := 118140960795 + 7179650 * 2 ^ 59
def prefixEnd_7179650 : Nat := 4983230072969 + 3 ^ 40 * 7179650 * 2
def baseEnd_7179650 : Nat := 1228870460350979940018799

theorem tailTrace_7179650 : CollatzResearch.WordTrace tailWord_7179650 prefixEnd_7179650 1228870460350979940018799 := by
  unfold tailWord_7179650
  simp only [CollatzResearch.WordTrace]
  refine ⟨65465837109840427860852101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174575565626241140962272269 65465837109840427860852101)
  ·
    refine ⟨12274844458095080223909769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65465837109840427860852101 12274844458095080223909769)
    ·
      refine ⟨9206133343571310167932327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12274844458095080223909769 9206133343571310167932327)
      ·
        refine ⟨13809200015356965251898491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9206133343571310167932327 13809200015356965251898491)
        ·
          refine ⟨20713800023035447877847737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13809200015356965251898491 20713800023035447877847737)
          ·
            refine ⟨15535350017276585908385803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20713800023035447877847737 15535350017276585908385803)
            ·
              refine ⟨23303025025914878862578705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15535350017276585908385803 23303025025914878862578705)
              ·
                refine ⟨17477268769436159146934029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23303025025914878862578705 17477268769436159146934029)
                ·
                  refine ⟨6553975788538559680100261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17477268769436159146934029 6553975788538559680100261)
                  ·
                    refine ⟨1228870460350979940018799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6553975788538559680100261 1228870460350979940018799)
                    ·
                      rfl

theorem cell23_7179650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_7179650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7179650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7179650 prefixEnd_7179650 := by exact prefixLift 7179650
  have htrace : WordTrace (prefixWord ++ tailWord_7179650) baseStart_7179650 baseEnd_7179650 := by
    simpa [prefixWord, tailWord_7179650, baseEnd_7179650] using wordTrace_append hprefix tailTrace_7179650
  have hstable : (prefixWord ++ tailWord_7179650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7179650).length < 2 ^ (prefixWord ++ tailWord_7179650).sum := by decide
  have hdescent : baseEnd_7179650 < baseStart_7179650 := by decide
  rcases family_descends (prefixWord ++ tailWord_7179650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7179659 : List Nat := [1, 1, 1, 1, 4, 3, 1, 3, 3, 5]
def baseStart_7179659 : Nat := 118140960795 + 7179659 * 2 ^ 59
def prefixEnd_7179659 : Nat := 4983230072969 + 3 ^ 40 * 7179659 * 2
def baseEnd_7179659 : Nat := 1228872000792943428281285

theorem tailTrace_7179659 : CollatzResearch.WordTrace tailWord_7179659 prefixEnd_7179659 1228872000792943428281285 := by
  unfold tailWord_7179659
  simp only [CollatzResearch.WordTrace]
  refine ⟨261863676696329105980486031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174575784464219403986990687 261863676696329105980486031)
  ·
    refine ⟨392795515044493658970729047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261863676696329105980486031 392795515044493658970729047)
    ·
      refine ⟨589193272566740488456093571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392795515044493658970729047 589193272566740488456093571)
      ·
        refine ⟨883789908850110732684140357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 589193272566740488456093571 883789908850110732684140357)
        ·
          refine ⟨165710607909395762378276317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 883789908850110732684140357 165710607909395762378276317)
          ·
            refine ⟨62141477966023410891853619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165710607909395762378276317 62141477966023410891853619)
            ·
              refine ⟨93212216949035116337780429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62141477966023410891853619 93212216949035116337780429)
              ·
                refine ⟨34954581355888168626667661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93212216949035116337780429 34954581355888168626667661)
                ·
                  refine ⟨13107968008458063235000373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34954581355888168626667661 13107968008458063235000373)
                  ·
                    refine ⟨1228872000792943428281285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13107968008458063235000373 1228872000792943428281285)
                    ·
                      rfl

theorem cell23_7179659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 3, 3, 5].length) (baseStart_7179659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7179659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7179659 prefixEnd_7179659 := by exact prefixLift 7179659
  have htrace : WordTrace (prefixWord ++ tailWord_7179659) baseStart_7179659 baseEnd_7179659 := by
    simpa [prefixWord, tailWord_7179659, baseEnd_7179659] using wordTrace_append hprefix tailTrace_7179659
  have hstable : (prefixWord ++ tailWord_7179659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7179659).length < 2 ^ (prefixWord ++ tailWord_7179659).sum := by decide
  have hdescent : baseEnd_7179659 < baseStart_7179659 := by decide
  rcases family_descends (prefixWord ++ tailWord_7179659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7179719 : List Nat := [1, 1, 4, 1, 1, 3, 3, 9]
def baseStart_7179719 : Nat := 118140960795 + 7179719 * 2 ^ 59
def prefixEnd_7179719 : Nat := 4983230072969 + 3 ^ 40 * 7179719 * 2
def baseEnd_7179719 : Nat := 136542474489559261114577

theorem tailTrace_7179719 : CollatzResearch.WordTrace tailWord_7179719 prefixEnd_7179719 136542474489559261114577 := by
  unfold tailWord_7179719
  simp only [CollatzResearch.WordTrace]
  refine ⟨261865865076111736227670211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174577243384074490818446807 261865865076111736227670211)
  ·
    refine ⟨392798797614167604341505317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261865865076111736227670211 392798797614167604341505317)
    ·
      refine ⟨73649774552656425814032247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 392798797614167604341505317 73649774552656425814032247)
      ·
        refine ⟨110474661828984638721048371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73649774552656425814032247 110474661828984638721048371)
        ·
          refine ⟨165711992743476958081572557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110474661828984638721048371 165711992743476958081572557)
          ·
            refine ⟨62141997278803859280589709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165711992743476958081572557 62141997278803859280589709)
            ·
              refine ⟨23303248979551447230221141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62141997278803859280589709 23303248979551447230221141)
              ·
                refine ⟨136542474489559261114577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23303248979551447230221141 136542474489559261114577)
                ·
                  rfl

theorem cell23_7179719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 9].length) (baseStart_7179719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7179719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7179719 prefixEnd_7179719 := by exact prefixLift 7179719
  have htrace : WordTrace (prefixWord ++ tailWord_7179719) baseStart_7179719 baseEnd_7179719 := by
    simpa [prefixWord, tailWord_7179719, baseEnd_7179719] using wordTrace_append hprefix tailTrace_7179719
  have hstable : (prefixWord ++ tailWord_7179719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7179719).length < 2 ^ (prefixWord ++ tailWord_7179719).sum := by decide
  have hdescent : baseEnd_7179719 < baseStart_7179719 := by decide
  rcases family_descends (prefixWord ++ tailWord_7179719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7179726 : List Nat := [4, 1, 1, 1, 2, 1, 2, 4, 1, 2, 4]
def baseStart_7179726 : Nat := 118140960795 + 7179726 * 2 ^ 59
def prefixEnd_7179726 : Nat := 4983230072969 + 3 ^ 40 * 7179726 * 2
def baseEnd_7179726 : Nat := 3686650405582681522706047

theorem tailTrace_7179726 : CollatzResearch.WordTrace tailWord_7179726 prefixEnd_7179726 3686650405582681522706047 := by
  unfold tailWord_7179726
  simp only [CollatzResearch.WordTrace]
  refine ⟨32733265048385797052896879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174577413591390917615450021 32733265048385797052896879)
  ·
    refine ⟨49099897572578695579345319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32733265048385797052896879 49099897572578695579345319)
    ·
      refine ⟨73649846358868043369017979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49099897572578695579345319 73649846358868043369017979)
      ·
        refine ⟨110474769538302065053526969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73649846358868043369017979 110474769538302065053526969)
        ·
          refine ⟨82856077153726548790145227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110474769538302065053526969 82856077153726548790145227)
          ·
            refine ⟨124284115730589823185217841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82856077153726548790145227 124284115730589823185217841)
            ·
              refine ⟨93213086797942367388913381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124284115730589823185217841 93213086797942367388913381)
              ·
                refine ⟨17477453774614193885421259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93213086797942367388913381 17477453774614193885421259)
                ·
                  refine ⟨26216180661921290828131889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17477453774614193885421259 26216180661921290828131889)
                  ·
                    refine ⟨19662135496440968121098917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26216180661921290828131889 19662135496440968121098917)
                    ·
                      refine ⟨3686650405582681522706047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19662135496440968121098917 3686650405582681522706047)
                      ·
                        rfl

theorem cell23_7179726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 4, 1, 2, 4].length) (baseStart_7179726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7179726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7179726 prefixEnd_7179726 := by exact prefixLift 7179726
  have htrace : WordTrace (prefixWord ++ tailWord_7179726) baseStart_7179726 baseEnd_7179726 := by
    simpa [prefixWord, tailWord_7179726, baseEnd_7179726] using wordTrace_append hprefix tailTrace_7179726
  have hstable : (prefixWord ++ tailWord_7179726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7179726).length < 2 ^ (prefixWord ++ tailWord_7179726).sum := by decide
  have hdescent : baseEnd_7179726 < baseStart_7179726 := by decide
  rcases family_descends (prefixWord ++ tailWord_7179726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7179733 : List Nat := [1, 3, 2, 3, 1, 1, 1, 5, 1, 2, 3]
def baseStart_7179733 : Nat := 118140960795 + 7179733 * 2 ^ 59
def prefixEnd_7179733 : Nat := 4983230072969 + 3 ^ 40 * 7179733 * 2
def baseEnd_7179733 : Nat := 3686653999947262995318515

theorem tailTrace_7179733 : CollatzResearch.WordTrace tailWord_7179733 prefixEnd_7179733 3686653999947262995318515 := by
  unfold tailWord_7179733
  simp only [CollatzResearch.WordTrace]
  refine ⟨261866375698061016618679853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174577583798707344412453235 261866375698061016618679853)
  ·
    refine ⟨98199890886772881232004945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261866375698061016618679853 98199890886772881232004945)
    ·
      refine ⟨73649918165079660924003709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98199890886772881232004945 73649918165079660924003709)
      ·
        refine ⟨27618719311904872846501391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73649918165079660924003709 27618719311904872846501391)
        ·
          refine ⟨41428078967857309269752087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27618719311904872846501391 41428078967857309269752087)
          ·
            refine ⟨62142118451785963904628131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41428078967857309269752087 62142118451785963904628131)
            ·
              refine ⟨93213177677678945856942197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62142118451785963904628131 93213177677678945856942197)
              ·
                refine ⟨8738735407282401174088331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 93213177677678945856942197 8738735407282401174088331)
                ·
                  refine ⟨13108103110923601761132497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8738735407282401174088331 13108103110923601761132497)
                  ·
                    refine ⟨9831077333192701320849373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13108103110923601761132497 9831077333192701320849373)
                    ·
                      refine ⟨3686653999947262995318515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9831077333192701320849373 3686653999947262995318515)
                      ·
                        rfl

theorem cell23_7179733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_7179733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7179733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7179733 prefixEnd_7179733 := by exact prefixLift 7179733
  have htrace : WordTrace (prefixWord ++ tailWord_7179733) baseStart_7179733 baseEnd_7179733 := by
    simpa [prefixWord, tailWord_7179733, baseEnd_7179733] using wordTrace_append hprefix tailTrace_7179733
  have hstable : (prefixWord ++ tailWord_7179733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7179733).length < 2 ^ (prefixWord ++ tailWord_7179733).sum := by decide
  have hdescent : baseEnd_7179733 < baseStart_7179733 := by decide
  rcases family_descends (prefixWord ++ tailWord_7179733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7179747 : List Nat := [1, 1, 1, 6, 2, 3, 1, 1, 3, 2, 2]
def baseStart_7179747 : Nat := 118140960795 + 7179747 * 2 ^ 59
def prefixEnd_7179747 : Nat := 4983230072969 + 3 ^ 40 * 7179747 * 2
def baseEnd_7179747 : Nat := 3686661188676425940543451

theorem tailTrace_7179747 : CollatzResearch.WordTrace tailWord_7179747 prefixEnd_7179747 3686661188676425940543451 := by
  unfold tailWord_7179747
  simp only [CollatzResearch.WordTrace]
  refine ⟨261866886320010297009689495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174577924213340198006459663 261866886320010297009689495)
  ·
    refine ⟨392800329480015445514534243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261866886320010297009689495 392800329480015445514534243)
    ·
      refine ⟨589200494220023168271801365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392800329480015445514534243 589200494220023168271801365)
      ·
        refine ⟨27618773166563586012740689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 589200494220023168271801365 27618773166563586012740689)
        ·
          refine ⟨20714079874922689509555517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27618773166563586012740689 20714079874922689509555517)
          ·
            refine ⟨7767779953096008566083319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20714079874922689509555517 7767779953096008566083319)
            ·
              refine ⟨11651669929644012849124979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7767779953096008566083319 11651669929644012849124979)
              ·
                refine ⟨17477504894466019273687469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11651669929644012849124979 17477504894466019273687469)
                ·
                  refine ⟨6554064335424757227632801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17477504894466019273687469 6554064335424757227632801)
                  ·
                    refine ⟨4915548251568567920724601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6554064335424757227632801 4915548251568567920724601)
                    ·
                      refine ⟨3686661188676425940543451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4915548251568567920724601 3686661188676425940543451)
                      ·
                        rfl

theorem cell23_7179747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 1, 3, 2, 2].length) (baseStart_7179747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7179747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7179747 prefixEnd_7179747 := by exact prefixLift 7179747
  have htrace : WordTrace (prefixWord ++ tailWord_7179747) baseStart_7179747 baseEnd_7179747 := by
    simpa [prefixWord, tailWord_7179747, baseEnd_7179747] using wordTrace_append hprefix tailTrace_7179747
  have hstable : (prefixWord ++ tailWord_7179747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7179747).length < 2 ^ (prefixWord ++ tailWord_7179747).sum := by decide
  have hdescent : baseEnd_7179747 < baseStart_7179747 := by decide
  rcases family_descends (prefixWord ++ tailWord_7179747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7179769 : List Nat := [1, 2, 1, 3, 1, 2, 1, 1, 1, 2, 8]
def baseStart_7179769 : Nat := 118140960795 + 7179769 * 2 ^ 59
def prefixEnd_7179769 : Nat := 4983230072969 + 3 ^ 40 * 7179769 * 2
def baseEnd_7179769 : Nat := 3686672485250824854468349

theorem tailTrace_7179769 : CollatzResearch.WordTrace tailWord_7179769 prefixEnd_7179769 3686672485250824854468349 := by
  unfold tailWord_7179769
  simp only [CollatzResearch.WordTrace]
  refine ⟨261867688725930594766990361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174578459150620396511326907 261867688725930594766990361)
  ·
    refine ⟨196400766544447946075242771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261867688725930594766990361 196400766544447946075242771)
    ·
      refine ⟨294601149816671919112864157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196400766544447946075242771 294601149816671919112864157)
      ·
        refine ⟨110475431181251969667324059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 294601149816671919112864157 110475431181251969667324059)
        ·
          refine ⟨165713146771877954500986089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110475431181251969667324059 165713146771877954500986089)
          ·
            refine ⟨124284860078908465875739567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165713146771877954500986089 124284860078908465875739567)
            ·
              refine ⟨186427290118362698813609351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124284860078908465875739567 186427290118362698813609351)
              ·
                refine ⟨279640935177544048220414027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 186427290118362698813609351 279640935177544048220414027)
                ·
                  refine ⟨419461402766316072330621041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 279640935177544048220414027 419461402766316072330621041)
                  ·
                    refine ⟨314596052074737054247965781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 419461402766316072330621041 314596052074737054247965781)
                    ·
                      refine ⟨3686672485250824854468349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 314596052074737054247965781 3686672485250824854468349)
                      ·
                        rfl

theorem cell23_7179769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 2, 8].length) (baseStart_7179769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7179769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7179769 prefixEnd_7179769 := by exact prefixLift 7179769
  have htrace : WordTrace (prefixWord ++ tailWord_7179769) baseStart_7179769 baseEnd_7179769 := by
    simpa [prefixWord, tailWord_7179769, baseEnd_7179769] using wordTrace_append hprefix tailTrace_7179769
  have hstable : (prefixWord ++ tailWord_7179769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7179769).length < 2 ^ (prefixWord ++ tailWord_7179769).sum := by decide
  have hdescent : baseEnd_7179769 < baseStart_7179769 := by decide
  rcases family_descends (prefixWord ++ tailWord_7179769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7179779 : List Nat := [1, 1, 1, 3, 2, 1, 2, 1, 3, 8]
def baseStart_7179779 : Nat := 118140960795 + 7179779 * 2 ^ 59
def prefixEnd_7179779 : Nat := 4983230072969 + 3 ^ 40 * 7179779 * 2
def baseEnd_7179779 : Nat := 1228892540019123271781101

theorem tailTrace_7179779 : CollatzResearch.WordTrace tailWord_7179779 prefixEnd_7179779 1228892540019123271781101 := by
  unfold tailWord_7179779
  simp only [CollatzResearch.WordTrace]
  refine ⟨261868053455894366474854391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174578702303929577649902927 261868053455894366474854391)
  ·
    refine ⟨392802080183841549712281587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261868053455894366474854391 392802080183841549712281587)
    ·
      refine ⟨589203120275762324568422381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392802080183841549712281587 589203120275762324568422381)
      ·
        refine ⟨220951170103410871713158393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 589203120275762324568422381 220951170103410871713158393)
        ·
          refine ⟨165713377577558153784868795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220951170103410871713158393 165713377577558153784868795)
          ·
            refine ⟨248570066366337230677303193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165713377577558153784868795 248570066366337230677303193)
            ·
              refine ⟨186427549774752923007977395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 248570066366337230677303193 186427549774752923007977395)
              ·
                refine ⟨279641324662129384511966093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 186427549774752923007977395 279641324662129384511966093)
                ·
                  refine ⟨104865496748298519191987285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 279641324662129384511966093 104865496748298519191987285)
                  ·
                    refine ⟨1228892540019123271781101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 104865496748298519191987285 1228892540019123271781101)
                    ·
                      rfl

theorem cell23_7179779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 8].length) (baseStart_7179779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7179779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7179779 prefixEnd_7179779 := by exact prefixLift 7179779
  have htrace : WordTrace (prefixWord ++ tailWord_7179779) baseStart_7179779 baseEnd_7179779 := by
    simpa [prefixWord, tailWord_7179779, baseEnd_7179779] using wordTrace_append hprefix tailTrace_7179779
  have hstable : (prefixWord ++ tailWord_7179779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7179779).length < 2 ^ (prefixWord ++ tailWord_7179779).sum := by decide
  have hdescent : baseEnd_7179779 < baseStart_7179779 := by decide
  rcases family_descends (prefixWord ++ tailWord_7179779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7179780 : List Nat := [2, 3, 2, 3, 2, 1, 1, 2, 1, 3, 3]
def baseStart_7179780 : Nat := 118140960795 + 7179780 * 2 ^ 59
def prefixEnd_7179780 : Nat := 4983230072969 + 3 ^ 40 * 7179780 * 2
def baseEnd_7179780 : Nat := 3686678133538024311430799

theorem tailTrace_7179780 : CollatzResearch.WordTrace tailWord_7179780 prefixEnd_7179780 3686678133538024311430799 := by
  unfold tailWord_7179780
  simp only [CollatzResearch.WordTrace]
  refine ⟨130934044964445371822820397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174578726619260495763760529 130934044964445371822820397)
  ·
    refine ⟨49100266861667014433557649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130934044964445371822820397 49100266861667014433557649)
    ·
      refine ⟨36825200146250260825168237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49100266861667014433557649 36825200146250260825168237)
      ·
        refine ⟨13809450054843847809438089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36825200146250260825168237 13809450054843847809438089)
        ·
          refine ⟨10357087541132885857078567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13809450054843847809438089 10357087541132885857078567)
          ·
            refine ⟨15535631311699328785617851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10357087541132885857078567 15535631311699328785617851)
            ·
              refine ⟨23303446967548993178426777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15535631311699328785617851 23303446967548993178426777)
              ·
                refine ⟨17477585225661744883820083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23303446967548993178426777 17477585225661744883820083)
                ·
                  refine ⟨26216377838492617325730125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17477585225661744883820083 26216377838492617325730125)
                  ·
                    refine ⟨9831141689434731497148797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26216377838492617325730125 9831141689434731497148797)
                    ·
                      refine ⟨3686678133538024311430799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9831141689434731497148797 3686678133538024311430799)
                      ·
                        rfl

theorem cell23_7179780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_7179780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7179780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7179780 prefixEnd_7179780 := by exact prefixLift 7179780
  have htrace : WordTrace (prefixWord ++ tailWord_7179780) baseStart_7179780 baseEnd_7179780 := by
    simpa [prefixWord, tailWord_7179780, baseEnd_7179780] using wordTrace_append hprefix tailTrace_7179780
  have hstable : (prefixWord ++ tailWord_7179780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7179780).length < 2 ^ (prefixWord ++ tailWord_7179780).sum := by decide
  have hdescent : baseEnd_7179780 < baseStart_7179780 := by decide
  rcases family_descends (prefixWord ++ tailWord_7179780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7179856 : List Nat := [2, 1, 1, 1, 1, 3, 4, 1, 4, 5]
def baseStart_7179856 : Nat := 118140960795 + 7179856 * 2 ^ 59
def prefixEnd_7179856 : Nat := 4983230072969 + 3 ^ 40 * 7179856 * 2
def baseEnd_7179856 : Nat := 1228905719355922004693483

theorem tailTrace_7179856 : CollatzResearch.WordTrace tailWord_7179856 prefixEnd_7179856 1228905719355922004693483 := by
  unfold tailWord_7179856
  simp only [CollatzResearch.WordTrace]
  refine ⟨130935430938307704312703711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174580574584410272416938281 130935430938307704312703711)
  ·
    refine ⟨196403146407461556469055567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130935430938307704312703711 196403146407461556469055567)
    ·
      refine ⟨294604719611192334703583351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196403146407461556469055567 294604719611192334703583351)
      ·
        refine ⟨441907079416788502055375027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294604719611192334703583351 441907079416788502055375027)
        ·
          refine ⟨662860619125182753083062541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 441907079416788502055375027 662860619125182753083062541)
          ·
            refine ⟨248572732171943532406148453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 662860619125182753083062541 248572732171943532406148453)
            ·
              refine ⟨46607387282239412326152835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 248572732171943532406148453 46607387282239412326152835)
              ·
                refine ⟨69911080923359118489229253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46607387282239412326152835 69911080923359118489229253)
                ·
                  refine ⟨13108327673129834716730485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69911080923359118489229253 13108327673129834716730485)
                  ·
                    refine ⟨1228905719355922004693483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13108327673129834716730485 1228905719355922004693483)
                    ·
                      rfl

theorem cell23_7179856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 4, 5].length) (baseStart_7179856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7179856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7179856 prefixEnd_7179856 := by exact prefixLift 7179856
  have htrace : WordTrace (prefixWord ++ tailWord_7179856) baseStart_7179856 baseEnd_7179856 := by
    simpa [prefixWord, tailWord_7179856, baseEnd_7179856] using wordTrace_append hprefix tailTrace_7179856
  have hstable : (prefixWord ++ tailWord_7179856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7179856).length < 2 ^ (prefixWord ++ tailWord_7179856).sum := by decide
  have hdescent : baseEnd_7179856 < baseStart_7179856 := by decide
  rcases family_descends (prefixWord ++ tailWord_7179856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7179866 : List Nat := [3, 1, 1, 2, 1, 1, 1, 5, 1, 2, 5]
def baseStart_7179866 : Nat := 118140960795 + 7179866 * 2 ^ 59
def prefixEnd_7179866 : Nat := 4983230072969 + 3 ^ 40 * 7179866 * 2
def baseEnd_7179866 : Nat := 3686722292874310974955403

theorem tailTrace_7179866 : CollatzResearch.WordTrace tailWord_7179866 prefixEnd_7179866 3686722292874310974955403 := by
  unfold tailWord_7179866
  simp only [CollatzResearch.WordTrace]
  refine ⟨65467806651644795083317863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174580817737719453555514301 65467806651644795083317863)
  ·
    refine ⟨98201709977467192624976795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65467806651644795083317863 98201709977467192624976795)
    ·
      refine ⟨147302564966200788937465193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98201709977467192624976795 147302564966200788937465193)
      ·
        refine ⟨110476923724650591703098895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147302564966200788937465193 110476923724650591703098895)
        ·
          refine ⟨165715385586975887554648343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110476923724650591703098895 165715385586975887554648343)
          ·
            refine ⟨248573078380463831331972515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165715385586975887554648343 248573078380463831331972515)
            ·
              refine ⟨372859617570695746997958773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248573078380463831331972515 372859617570695746997958773)
              ·
                refine ⟨34955589147252726281058635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 372859617570695746997958773 34955589147252726281058635)
                ·
                  refine ⟨52433383720879089421587953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34955589147252726281058635 52433383720879089421587953)
                  ·
                    refine ⟨39325037790659317066190965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52433383720879089421587953 39325037790659317066190965)
                    ·
                      refine ⟨3686722292874310974955403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39325037790659317066190965 3686722292874310974955403)
                      ·
                        rfl

theorem cell23_7179866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 5, 1, 2, 5].length) (baseStart_7179866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7179866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7179866 prefixEnd_7179866 := by exact prefixLift 7179866
  have htrace : WordTrace (prefixWord ++ tailWord_7179866) baseStart_7179866 baseEnd_7179866 := by
    simpa [prefixWord, tailWord_7179866, baseEnd_7179866] using wordTrace_append hprefix tailTrace_7179866
  have hstable : (prefixWord ++ tailWord_7179866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7179866).length < 2 ^ (prefixWord ++ tailWord_7179866).sum := by decide
  have hdescent : baseEnd_7179866 < baseStart_7179866 := by decide
  rcases family_descends (prefixWord ++ tailWord_7179866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7179913 : List Nat := [1, 2, 1, 1, 4, 1, 3, 1, 4, 2, 3]
def baseStart_7179913 : Nat := 118140960795 + 7179913 * 2 ^ 59
def prefixEnd_7179913 : Nat := 4983230072969 + 3 ^ 40 * 7179913 * 2
def baseEnd_7179913 : Nat := 3686746426465072291067687

theorem tailTrace_7179913 : CollatzResearch.WordTrace tailWord_7179913 prefixEnd_7179913 3686746426465072291067687 := by
  unfold tailWord_7179913
  simp only [CollatzResearch.WordTrace]
  refine ⟨261872940837408907360232393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174581960558272604906821595 261872940837408907360232393)
  ·
    refine ⟨196404705628056680520174295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261872940837408907360232393 196404705628056680520174295)
    ·
      refine ⟨294607058442085020780261443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196404705628056680520174295 294607058442085020780261443)
      ·
        refine ⟨441910587663127531170392165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294607058442085020780261443 441910587663127531170392165)
        ·
          refine ⟨82858235186836412094448531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 441910587663127531170392165 82858235186836412094448531)
          ·
            refine ⟨124287352780254618141672797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82858235186836412094448531 124287352780254618141672797)
            ·
              refine ⟨46607757292595481803127299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124287352780254618141672797 46607757292595481803127299)
              ·
                refine ⟨69911635938893222704690949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46607757292595481803127299 69911635938893222704690949)
                ·
                  refine ⟨13108431738542479257129553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69911635938893222704690949 13108431738542479257129553)
                  ·
                    refine ⟨9831323803906859442847165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13108431738542479257129553 9831323803906859442847165)
                    ·
                      refine ⟨3686746426465072291067687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9831323803906859442847165 3686746426465072291067687)
                      ·
                        rfl

theorem cell23_7179913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 4, 2, 3].length) (baseStart_7179913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7179913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7179913 prefixEnd_7179913 := by exact prefixLift 7179913
  have htrace : WordTrace (prefixWord ++ tailWord_7179913) baseStart_7179913 baseEnd_7179913 := by
    simpa [prefixWord, tailWord_7179913, baseEnd_7179913] using wordTrace_append hprefix tailTrace_7179913
  have hstable : (prefixWord ++ tailWord_7179913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7179913).length < 2 ^ (prefixWord ++ tailWord_7179913).sum := by decide
  have hdescent : baseEnd_7179913 < baseStart_7179913 := by decide
  rcases family_descends (prefixWord ++ tailWord_7179913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7179916 : List Nat := [2, 2, 1, 2, 1, 1, 3, 3, 8]
def baseStart_7179916 : Nat := 118140960795 + 7179916 * 2 ^ 59
def prefixEnd_7179916 : Nat := 4983230072969 + 3 ^ 40 * 7179916 * 2
def baseEnd_7179916 : Nat := 409638662989670642147797

theorem tailTrace_7179916 : CollatzResearch.WordTrace tailWord_7179916 prefixEnd_7179916 409638662989670642147797 := by
  unfold tailWord_7179916
  simp only [CollatzResearch.WordTrace]
  refine ⟨130936525128199019436295801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174582033504265359248394401 130936525128199019436295801)
  ·
    refine ⟨98202393846149264577221851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130936525128199019436295801 98202393846149264577221851)
    ·
      refine ⟨147303590769223896865832777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98202393846149264577221851 147303590769223896865832777)
      ·
        refine ⟨110477693076917922649374583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147303590769223896865832777 110477693076917922649374583)
        ·
          refine ⟨165716539615376883974061875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110477693076917922649374583 165716539615376883974061875)
          ·
            refine ⟨248574809423065325961092813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165716539615376883974061875 248574809423065325961092813)
            ·
              refine ⟨93215553533649497235409805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 248574809423065325961092813 93215553533649497235409805)
              ·
                refine ⟨34955832575118561463278677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93215553533649497235409805 34955832575118561463278677)
                ·
                  refine ⟨409638662989670642147797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34955832575118561463278677 409638662989670642147797)
                  ·
                    rfl

theorem cell23_7179916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 8].length) (baseStart_7179916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7179916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7179916 prefixEnd_7179916 := by exact prefixLift 7179916
  have htrace : WordTrace (prefixWord ++ tailWord_7179916) baseStart_7179916 baseEnd_7179916 := by
    simpa [prefixWord, tailWord_7179916, baseEnd_7179916] using wordTrace_append hprefix tailTrace_7179916
  have hstable : (prefixWord ++ tailWord_7179916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7179916).length < 2 ^ (prefixWord ++ tailWord_7179916).sum := by decide
  have hdescent : baseEnd_7179916 < baseStart_7179916 := by decide
  rcases family_descends (prefixWord ++ tailWord_7179916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7179920 : List Nat := [2, 1, 1, 1, 1, 1, 3, 8, 1, 4]
def baseStart_7179920 : Nat := 118140960795 + 7179920 * 2 ^ 59
def prefixEnd_7179920 : Nat := 4983230072969 + 3 ^ 40 * 7179920 * 2
def baseEnd_7179920 : Nat := 1228916673609884587893385

theorem tailTrace_7179920 : CollatzResearch.WordTrace tailWord_7179920 prefixEnd_7179920 1228916673609884587893385 := by
  unfold tailWord_7179920
  simp only [CollatzResearch.WordTrace]
  refine ⟨130936598074191773777868607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174582130765589031703824809 130936598074191773777868607)
  ·
    refine ⟨196404897111287660666802911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130936598074191773777868607 196404897111287660666802911)
    ·
      refine ⟨294607345666931491000204367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196404897111287660666802911 294607345666931491000204367)
      ·
        refine ⟨441911018500397236500306551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294607345666931491000204367 441911018500397236500306551)
        ·
          refine ⟨662866527750595854750459827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 441911018500397236500306551 662866527750595854750459827)
          ·
            refine ⟨994299791625893782125689741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 662866527750595854750459827 994299791625893782125689741)
            ·
              refine ⟨372862421859710168297133653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 994299791625893782125689741 372862421859710168297133653)
              ·
                refine ⟨4369481506168478534732035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 372862421859710168297133653 4369481506168478534732035)
                ·
                  refine ⟨6554222259252717802098053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4369481506168478534732035 6554222259252717802098053)
                  ·
                    refine ⟨1228916673609884587893385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6554222259252717802098053 1228916673609884587893385)
                    ·
                      rfl

theorem cell23_7179920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 8, 1, 4].length) (baseStart_7179920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7179920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7179920 prefixEnd_7179920 := by exact prefixLift 7179920
  have htrace : WordTrace (prefixWord ++ tailWord_7179920) baseStart_7179920 baseEnd_7179920 := by
    simpa [prefixWord, tailWord_7179920, baseEnd_7179920] using wordTrace_append hprefix tailTrace_7179920
  have hstable : (prefixWord ++ tailWord_7179920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7179920).length < 2 ^ (prefixWord ++ tailWord_7179920).sum := by decide
  have hdescent : baseEnd_7179920 < baseStart_7179920 := by decide
  rcases family_descends (prefixWord ++ tailWord_7179920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7179963 : List Nat := [1, 1, 1, 1, 1, 2, 3, 7, 1, 5]
def baseStart_7179963 : Nat := 118140960795 + 7179963 * 2 ^ 59
def prefixEnd_7179963 : Nat := 4983230072969 + 3 ^ 40 * 7179963 * 2
def baseEnd_7179963 : Nat := 1228924033499265698480819

theorem tailTrace_7179963 : CollatzResearch.WordTrace tailWord_7179963 prefixEnd_7179963 1228924033499265698480819 := by
  unfold tailWord_7179963
  simp only [CollatzResearch.WordTrace]
  refine ⟨261874764487227765899552543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174583176324818510599701695 261874764487227765899552543)
  ·
    refine ⟨392812146730841648849328815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261874764487227765899552543 392812146730841648849328815)
    ·
      refine ⟨589218220096262473273993223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392812146730841648849328815 589218220096262473273993223)
      ·
        refine ⟨883827330144393709910989835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 589218220096262473273993223 883827330144393709910989835)
        ·
          refine ⟨1325740995216590564866484753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 883827330144393709910989835 1325740995216590564866484753)
          ·
            refine ⟨994305746412442923649863565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1325740995216590564866484753 994305746412442923649863565)
            ·
              refine ⟨372864654904666096368698837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 994305746412442923649863565 372864654904666096368698837)
              ·
                refine ⟨8739015349328111633641379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 372864654904666096368698837 8739015349328111633641379)
                ·
                  refine ⟨13108523023992167450462069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8739015349328111633641379 13108523023992167450462069)
                  ·
                    refine ⟨1228924033499265698480819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13108523023992167450462069 1228924033499265698480819)
                    ·
                      rfl

theorem cell23_7179963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 7, 1, 5].length) (baseStart_7179963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7179963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7179963 prefixEnd_7179963 := by exact prefixLift 7179963
  have htrace : WordTrace (prefixWord ++ tailWord_7179963) baseStart_7179963 baseEnd_7179963 := by
    simpa [prefixWord, tailWord_7179963, baseEnd_7179963] using wordTrace_append hprefix tailTrace_7179963
  have hstable : (prefixWord ++ tailWord_7179963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7179963).length < 2 ^ (prefixWord ++ tailWord_7179963).sum := by decide
  have hdescent : baseEnd_7179963 < baseStart_7179963 := by decide
  rcases family_descends (prefixWord ++ tailWord_7179963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7179993 : List Nat := [1, 2, 1, 2, 3, 3, 1, 3, 1, 6]
def baseStart_7179993 : Nat := 118140960795 + 7179993 * 2 ^ 59
def prefixEnd_7179993 : Nat := 4983230072969 + 3 ^ 40 * 7179993 * 2
def baseEnd_7179993 : Nat := 1228929168305810659355773

theorem tailTrace_7179993 : CollatzResearch.WordTrace tailWord_7179993 prefixEnd_7179993 1228929168305810659355773 := by
  unfold tailWord_7179993
  simp only [CollatzResearch.WordTrace]
  refine ⟨261875858677119081023144633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174583905784746054015429755 261875858677119081023144633)
  ·
    refine ⟨196406894007839310767358475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261875858677119081023144633 196406894007839310767358475)
    ·
      refine ⟨294610341011758966151037713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196406894007839310767358475 294610341011758966151037713)
      ·
        refine ⟨220957755758819224613278285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 294610341011758966151037713 220957755758819224613278285)
        ·
          refine ⟨82859158409557209229979357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 220957755758819224613278285 82859158409557209229979357)
          ·
            refine ⟨31072184403583953461242259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82859158409557209229979357 31072184403583953461242259)
            ·
              refine ⟨46608276605375930191863389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31072184403583953461242259 46608276605375930191863389)
              ·
                refine ⟨17478103727015973821948771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46608276605375930191863389 17478103727015973821948771)
                ·
                  refine ⟨26217155590523960732923157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17478103727015973821948771 26217155590523960732923157)
                  ·
                    refine ⟨1228929168305810659355773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26217155590523960732923157 1228929168305810659355773)
                    ·
                      rfl

theorem cell23_7179993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 3, 1, 6].length) (baseStart_7179993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7179993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7179993 prefixEnd_7179993 := by exact prefixLift 7179993
  have htrace : WordTrace (prefixWord ++ tailWord_7179993) baseStart_7179993 baseEnd_7179993 := by
    simpa [prefixWord, tailWord_7179993, baseEnd_7179993] using wordTrace_append hprefix tailTrace_7179993
  have hstable : (prefixWord ++ tailWord_7179993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7179993).length < 2 ^ (prefixWord ++ tailWord_7179993).sum := by decide
  have hdescent : baseEnd_7179993 < baseStart_7179993 := by decide
  rcases family_descends (prefixWord ++ tailWord_7179993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7180017 : List Nat := [1, 2, 2, 2, 2, 3, 4, 1, 1, 1, 4]
def baseStart_7180017 : Nat := 118140960795 + 7180017 * 2 ^ 59
def prefixEnd_7180017 : Nat := 4983230072969 + 3 ^ 40 * 7180017 * 2
def baseEnd_7180017 : Nat := 3686799828453139884167209

theorem tailTrace_7180017 : CollatzResearch.WordTrace tailWord_7180017 prefixEnd_7180017 3686799828453139884167209 := by
  unfold tailWord_7180017
  simp only [CollatzResearch.WordTrace]
  refine ⟨261876734029032133122018305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174584489352688088748012203 261876734029032133122018305)
  ·
    refine ⟨196407550521774099841513729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261876734029032133122018305 196407550521774099841513729)
    ·
      refine ⟨147305662891330574881135297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196407550521774099841513729 147305662891330574881135297)
      ·
        refine ⟨110479247168497931160851473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147305662891330574881135297 110479247168497931160851473)
        ·
          refine ⟨82859435376373448370638605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110479247168497931160851473 82859435376373448370638605)
          ·
            refine ⟨31072288266140043138989477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82859435376373448370638605 31072288266140043138989477)
            ·
              refine ⟨5826054049901258088560527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31072288266140043138989477 5826054049901258088560527)
              ·
                refine ⟨8739081074851887132840791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5826054049901258088560527 8739081074851887132840791)
                ·
                  refine ⟨13108621612277830699261187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8739081074851887132840791 13108621612277830699261187)
                  ·
                    refine ⟨19662932418416746048891781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13108621612277830699261187 19662932418416746048891781)
                    ·
                      refine ⟨3686799828453139884167209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19662932418416746048891781 3686799828453139884167209)
                      ·
                        rfl

theorem cell23_7180017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 4, 1, 1, 1, 4].length) (baseStart_7180017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7180017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7180017 prefixEnd_7180017 := by exact prefixLift 7180017
  have htrace : WordTrace (prefixWord ++ tailWord_7180017) baseStart_7180017 baseEnd_7180017 := by
    simpa [prefixWord, tailWord_7180017, baseEnd_7180017] using wordTrace_append hprefix tailTrace_7180017
  have hstable : (prefixWord ++ tailWord_7180017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7180017).length < 2 ^ (prefixWord ++ tailWord_7180017).sum := by decide
  have hdescent : baseEnd_7180017 < baseStart_7180017 := by decide
  rcases family_descends (prefixWord ++ tailWord_7180017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7180062 : List Nat := [4, 3, 2, 2, 2, 1, 1, 3, 1, 1, 3]
def baseStart_7180062 : Nat := 118140960795 + 7180062 * 2 ^ 59
def prefixEnd_7180062 : Nat := 4983230072969 + 3 ^ 40 * 7180062 * 2
def baseEnd_7180062 : Nat := 3686822935082592208104503

theorem tailTrace_7180062 : CollatzResearch.WordTrace tailWord_7180062 prefixEnd_7180062 3686822935082592208104503 := by
  unfold tailWord_7180062
  simp only [CollatzResearch.WordTrace]
  refine ⟨32734796914233638225925805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174585583542579403871604293 32734796914233638225925805)
  ·
    refine ⟨12275548842837614334722177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32734796914233638225925805 12275548842837614334722177)
    ·
      refine ⟨9206661632128210751041633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12275548842837614334722177 9206661632128210751041633)
      ·
        refine ⟨6904996224096158063281225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9206661632128210751041633 6904996224096158063281225)
        ·
          refine ⟨5178747168072118547460919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6904996224096158063281225 5178747168072118547460919)
          ·
            refine ⟨7768120752108177821191379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5178747168072118547460919 7768120752108177821191379)
            ·
              refine ⟨11652181128162266731787069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7768120752108177821191379 11652181128162266731787069)
              ·
                refine ⟨4369567923060850024420151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11652181128162266731787069 4369567923060850024420151)
                ·
                  refine ⟨6554351884591275036630227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4369567923060850024420151 6554351884591275036630227)
                  ·
                    refine ⟨9831527826886912554945341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6554351884591275036630227 9831527826886912554945341)
                    ·
                      refine ⟨3686822935082592208104503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9831527826886912554945341 3686822935082592208104503)
                      ·
                        rfl

theorem cell23_7180062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_7180062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7180062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7180062 prefixEnd_7180062 := by exact prefixLift 7180062
  have htrace : WordTrace (prefixWord ++ tailWord_7180062) baseStart_7180062 baseEnd_7180062 := by
    simpa [prefixWord, tailWord_7180062, baseEnd_7180062] using wordTrace_append hprefix tailTrace_7180062
  have hstable : (prefixWord ++ tailWord_7180062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7180062).length < 2 ^ (prefixWord ++ tailWord_7180062).sum := by decide
  have hdescent : baseEnd_7180062 < baseStart_7180062 := by decide
  rcases family_descends (prefixWord ++ tailWord_7180062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7180063 : List Nat := [1, 1, 2, 4, 2, 1, 1, 1, 1, 4, 5]
def baseStart_7180063 : Nat := 118140960795 + 7180063 * 2 ^ 59
def prefixEnd_7180063 : Nat := 4983230072969 + 3 ^ 40 * 7180063 * 2
def baseEnd_7180063 : Nat := 3686823448563246704191997

theorem tailTrace_7180063 : CollatzResearch.WordTrace tailWord_7180063 prefixEnd_7180063 3686823448563246704191997 := by
  unfold tailWord_7180063
  simp only [CollatzResearch.WordTrace]
  refine ⟨261878411786865482978192843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174585607857910321985461895 261878411786865482978192843)
  ·
    refine ⟨392817617680298224467289265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261878411786865482978192843 392817617680298224467289265)
    ·
      refine ⟨294613213260223668350466949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 392817617680298224467289265 294613213260223668350466949)
      ·
        refine ⟨55239977486291937815712553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 294613213260223668350466949 55239977486291937815712553)
        ·
          refine ⟨41429983114718953361784415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55239977486291937815712553 41429983114718953361784415)
          ·
            refine ⟨62144974672078430042676623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41429983114718953361784415 62144974672078430042676623)
            ·
              refine ⟨93217462008117645064014935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62144974672078430042676623 93217462008117645064014935)
              ·
                refine ⟨139826193012176467596022403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93217462008117645064014935 139826193012176467596022403)
                ·
                  refine ⟨209739289518264701394033605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 139826193012176467596022403 209739289518264701394033605)
                  ·
                    refine ⟨39326116784674631511381301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 209739289518264701394033605 39326116784674631511381301)
                    ·
                      refine ⟨3686823448563246704191997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39326116784674631511381301 3686823448563246704191997)
                      ·
                        rfl

theorem cell23_7180063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_7180063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7180063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7180063 prefixEnd_7180063 := by exact prefixLift 7180063
  have htrace : WordTrace (prefixWord ++ tailWord_7180063) baseStart_7180063 baseEnd_7180063 := by
    simpa [prefixWord, tailWord_7180063, baseEnd_7180063] using wordTrace_append hprefix tailTrace_7180063
  have hstable : (prefixWord ++ tailWord_7180063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7180063).length < 2 ^ (prefixWord ++ tailWord_7180063).sum := by decide
  have hdescent : baseEnd_7180063 < baseStart_7180063 := by decide
  rcases family_descends (prefixWord ++ tailWord_7180063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7180068 : List Nat := [2, 3, 1, 3, 2, 3, 1, 3, 1, 2, 2]
def baseStart_7180068 : Nat := 118140960795 + 7180068 * 2 ^ 59
def prefixEnd_7180068 : Nat := 4983230072969 + 3 ^ 40 * 7180068 * 2
def baseEnd_7180068 : Nat := 3686826015966519184629475

theorem tailTrace_7180068 : CollatzResearch.WordTrace tailWord_7180068 prefixEnd_7180068 3686826015966519184629475 := by
  unfold tailWord_7180068
  simp only [CollatzResearch.WordTrace]
  refine ⟨130939297075923684416062429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174585729434564912554749905 130939297075923684416062429)
  ·
    refine ⟨49102236403471381656023411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130939297075923684416062429 49102236403471381656023411)
    ·
      refine ⟨73653354605207072484035117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49102236403471381656023411 73653354605207072484035117)
      ·
        refine ⟨27620007976952652181513169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73653354605207072484035117 27620007976952652181513169)
        ·
          refine ⟨20715005982714489136134877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27620007976952652181513169 20715005982714489136134877)
          ·
            refine ⟨7768127243517933426050579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20715005982714489136134877 7768127243517933426050579)
            ·
              refine ⟨11652190865276900139075869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7768127243517933426050579 11652190865276900139075869)
              ·
                refine ⟨4369571574478837552153451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11652190865276900139075869 4369571574478837552153451)
                ·
                  refine ⟨6554357361718256328230177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4369571574478837552153451 6554357361718256328230177)
                  ·
                    refine ⟨4915768021288692246172633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6554357361718256328230177 4915768021288692246172633)
                    ·
                      refine ⟨3686826015966519184629475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4915768021288692246172633 3686826015966519184629475)
                      ·
                        rfl

theorem cell23_7180068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 3, 1, 2, 2].length) (baseStart_7180068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7180068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7180068 prefixEnd_7180068 := by exact prefixLift 7180068
  have htrace : WordTrace (prefixWord ++ tailWord_7180068) baseStart_7180068 baseEnd_7180068 := by
    simpa [prefixWord, tailWord_7180068, baseEnd_7180068] using wordTrace_append hprefix tailTrace_7180068
  have hstable : (prefixWord ++ tailWord_7180068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7180068).length < 2 ^ (prefixWord ++ tailWord_7180068).sum := by decide
  have hdescent : baseEnd_7180068 < baseStart_7180068 := by decide
  rcases family_descends (prefixWord ++ tailWord_7180068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7180084 : List Nat := [2, 5, 1, 1, 2, 1, 2, 1, 4, 1, 3]
def baseStart_7180084 : Nat := 118140960795 + 7180084 * 2 ^ 59
def prefixEnd_7180084 : Nat := 4983230072969 + 3 ^ 40 * 7180084 * 2
def baseEnd_7180084 : Nat := 3686834231656991122029401

theorem tailTrace_7180084 : CollatzResearch.WordTrace tailWord_7180084 prefixEnd_7180084 3686834231656991122029401 := by
  unfold tailWord_7180084
  simp only [CollatzResearch.WordTrace]
  refine ⟨130939588859894701782353653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174586118479859602376471537 130939588859894701782353653)
  ·
    refine ⟨12275586455615128292095655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 130939588859894701782353653 12275586455615128292095655)
    ·
      refine ⟨18413379683422692438143483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12275586455615128292095655 18413379683422692438143483)
      ·
        refine ⟨27620069525134038657215225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18413379683422692438143483 27620069525134038657215225)
        ·
          refine ⟨20715052143850528992911419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27620069525134038657215225 20715052143850528992911419)
          ·
            refine ⟨31072578215775793489367129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20715052143850528992911419 31072578215775793489367129)
            ·
              refine ⟨23304433661831845117025347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31072578215775793489367129 23304433661831845117025347)
              ·
                refine ⟨34956650492747767675538021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23304433661831845117025347 34956650492747767675538021)
                ·
                  refine ⟨6554371967390206439163379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34956650492747767675538021 6554371967390206439163379)
                  ·
                    refine ⟨9831557951085309658745069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6554371967390206439163379 9831557951085309658745069)
                    ·
                      refine ⟨3686834231656991122029401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9831557951085309658745069 3686834231656991122029401)
                      ·
                        rfl

theorem cell23_7180084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_7180084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7180084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7180084 prefixEnd_7180084 := by exact prefixLift 7180084
  have htrace : WordTrace (prefixWord ++ tailWord_7180084) baseStart_7180084 baseEnd_7180084 := by
    simpa [prefixWord, tailWord_7180084, baseEnd_7180084] using wordTrace_append hprefix tailTrace_7180084
  have hstable : (prefixWord ++ tailWord_7180084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7180084).length < 2 ^ (prefixWord ++ tailWord_7180084).sum := by decide
  have hdescent : baseEnd_7180084 < baseStart_7180084 := by decide
  rcases family_descends (prefixWord ++ tailWord_7180084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7180143 : List Nat := [1, 1, 2, 1, 3, 1, 1, 1, 5, 7]
def baseStart_7180143 : Nat := 118140960795 + 7180143 * 2 ^ 59
def prefixEnd_7180143 : Nat := 4983230072969 + 3 ^ 40 * 7180143 * 2
def baseEnd_7180143 : Nat := 1228954842338535463730543

theorem tailTrace_7180143 : CollatzResearch.WordTrace tailWord_7180143 prefixEnd_7180143 1228954842338535463730543 := by
  unfold tailWord_7180143
  simp only [CollatzResearch.WordTrace]
  refine ⟨261881329626575656641105083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174587553084383771094070055 261881329626575656641105083)
  ·
    refine ⟨392821994439863484961657625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261881329626575656641105083 392821994439863484961657625)
    ·
      refine ⟨294616495829897613721243219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 392821994439863484961657625 294616495829897613721243219)
      ·
        refine ⟨441924743744846420581864829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294616495829897613721243219 441924743744846420581864829)
        ·
          refine ⟨165721778904317407718199311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 441924743744846420581864829 165721778904317407718199311)
          ·
            refine ⟨248582668356476111577298967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165721778904317407718199311 248582668356476111577298967)
            ·
              refine ⟨372874002534714167365948451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248582668356476111577298967 372874002534714167365948451)
              ·
                refine ⟨559311003802071251048922677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 372874002534714167365948451 559311003802071251048922677)
                ·
                  refine ⟨52435406606444179785836501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 559311003802071251048922677 52435406606444179785836501)
                  ·
                    refine ⟨1228954842338535463730543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52435406606444179785836501 1228954842338535463730543)
                    ·
                      rfl

theorem cell23_7180143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 5, 7].length) (baseStart_7180143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7180143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7180143 prefixEnd_7180143 := by exact prefixLift 7180143
  have htrace : WordTrace (prefixWord ++ tailWord_7180143) baseStart_7180143 baseEnd_7180143 := by
    simpa [prefixWord, tailWord_7180143, baseEnd_7180143] using wordTrace_append hprefix tailTrace_7180143
  have hstable : (prefixWord ++ tailWord_7180143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7180143).length < 2 ^ (prefixWord ++ tailWord_7180143).sum := by decide
  have hdescent : baseEnd_7180143 < baseStart_7180143 := by decide
  rcases family_descends (prefixWord ++ tailWord_7180143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7180158 : List Nat := [4, 2, 3, 1, 1, 1, 2, 3, 2, 2, 2]
def baseStart_7180158 : Nat := 118140960795 + 7180158 * 2 ^ 59
def prefixEnd_7180158 : Nat := 4983230072969 + 3 ^ 40 * 7180158 * 2
def baseEnd_7180158 : Nat := 3686872229225423832504061

theorem tailTrace_7180158 : CollatzResearch.WordTrace tailWord_7180158 prefixEnd_7180158 3686872229225423832504061 := by
  unfold tailWord_7180158
  simp only [CollatzResearch.WordTrace]
  refine ⟨32735234590190164275362641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174587917814347542801934085 32735234590190164275362641)
  ·
    refine ⟨24551425942642623206521981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32735234590190164275362641 24551425942642623206521981)
    ·
      refine ⟨9206784728490983702445743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24551425942642623206521981 9206784728490983702445743)
      ·
        refine ⟨13810177092736475553668615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9206784728490983702445743 13810177092736475553668615)
        ·
          refine ⟨20715265639104713330502923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13810177092736475553668615 20715265639104713330502923)
          ·
            refine ⟨31072898458657069995754385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20715265639104713330502923 31072898458657069995754385)
            ·
              refine ⟨23304673843992802496815789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31072898458657069995754385 23304673843992802496815789)
              ·
                refine ⟨8739252691497300936305921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23304673843992802496815789 8739252691497300936305921)
                ·
                  refine ⟨6554439518622975702229441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8739252691497300936305921 6554439518622975702229441)
                  ·
                    refine ⟨4915829638967231776672081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6554439518622975702229441 4915829638967231776672081)
                    ·
                      refine ⟨3686872229225423832504061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4915829638967231776672081 3686872229225423832504061)
                      ·
                        rfl

theorem cell23_7180158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_7180158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7180158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7180158 prefixEnd_7180158 := by exact prefixLift 7180158
  have htrace : WordTrace (prefixWord ++ tailWord_7180158) baseStart_7180158 baseEnd_7180158 := by
    simpa [prefixWord, tailWord_7180158, baseEnd_7180158] using wordTrace_append hprefix tailTrace_7180158
  have hstable : (prefixWord ++ tailWord_7180158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7180158).length < 2 ^ (prefixWord ++ tailWord_7180158).sum := by decide
  have hdescent : baseEnd_7180158 < baseStart_7180158 := by decide
  rcases family_descends (prefixWord ++ tailWord_7180158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7180207 : List Nat := [1, 1, 2, 1, 2, 2, 6, 1, 3, 4]
def baseStart_7180207 : Nat := 118140960795 + 7180207 * 2 ^ 59
def prefixEnd_7180207 : Nat := 4983230072969 + 3 ^ 40 * 7180207 * 2
def baseEnd_7180207 : Nat := 1228965796592498046930445

theorem tailTrace_7180207 : CollatzResearch.WordTrace tailWord_7180207 prefixEnd_7180207 1228965796592498046930445 := by
  unfold tailWord_7180207
  simp only [CollatzResearch.WordTrace]
  refine ⟨261883663898343795571434875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174589109265562530380956583 261883663898343795571434875)
  ·
    refine ⟨392825495847515693357152313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261883663898343795571434875 392825495847515693357152313)
    ·
      refine ⟨294619121885636770017864235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 392825495847515693357152313 294619121885636770017864235)
      ·
        refine ⟨441928682828455155026796353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294619121885636770017864235 441928682828455155026796353)
        ·
          refine ⟨331446512121341366270097265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 441928682828455155026796353 331446512121341366270097265)
          ·
            refine ⟨248584884091006024702572949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 331446512121341366270097265 248584884091006024702572949)
            ·
              refine ⟨11652416441765907407933107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 248584884091006024702572949 11652416441765907407933107)
              ·
                refine ⟨17478624662648861111899661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11652416441765907407933107 17478624662648861111899661)
                ·
                  refine ⟨6554484248493322916962373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17478624662648861111899661 6554484248493322916962373)
                  ·
                    refine ⟨1228965796592498046930445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6554484248493322916962373 1228965796592498046930445)
                    ·
                      rfl

theorem cell23_7180207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 1, 3, 4].length) (baseStart_7180207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7180207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7180207 prefixEnd_7180207 := by exact prefixLift 7180207
  have htrace : WordTrace (prefixWord ++ tailWord_7180207) baseStart_7180207 baseEnd_7180207 := by
    simpa [prefixWord, tailWord_7180207, baseEnd_7180207] using wordTrace_append hprefix tailTrace_7180207
  have hstable : (prefixWord ++ tailWord_7180207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7180207).length < 2 ^ (prefixWord ++ tailWord_7180207).sum := by decide
  have hdescent : baseEnd_7180207 < baseStart_7180207 := by decide
  rcases family_descends (prefixWord ++ tailWord_7180207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7180258 : List Nat := [3, 3, 3, 1, 2, 2, 1, 1, 3, 4]
def baseStart_7180258 : Nat := 118140960795 + 7180258 * 2 ^ 59
def prefixEnd_7180258 : Nat := 4983230072969 + 3 ^ 40 * 7180258 * 2
def baseEnd_7180258 : Nat := 1228974525763624480417867

theorem tailTrace_7180258 : CollatzResearch.WordTrace tailWord_7180258 prefixEnd_7180258 1228974525763624480417867 := by
  unfold tailWord_7180258
  simp only [CollatzResearch.WordTrace]
  refine ⟨65471381005289757820385357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174590349347439354187694285 65471381005289757820385357)
  ·
    refine ⟨24551767876983659182644509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65471381005289757820385357 24551767876983659182644509)
    ·
      refine ⟨9206912953868872193491691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24551767876983659182644509 9206912953868872193491691)
      ·
        refine ⟨13810369430803308290237537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9206912953868872193491691 13810369430803308290237537)
        ·
          refine ⟨10357777073102481217678153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13810369430803308290237537 10357777073102481217678153)
          ·
            refine ⟨7768332804826860913258615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10357777073102481217678153 7768332804826860913258615)
            ·
              refine ⟨11652499207240291369887923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7768332804826860913258615 11652499207240291369887923)
              ·
                refine ⟨17478748810860437054831885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11652499207240291369887923 17478748810860437054831885)
                ·
                  refine ⟨6554530804072663895561957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17478748810860437054831885 6554530804072663895561957)
                  ·
                    refine ⟨1228974525763624480417867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6554530804072663895561957 1228974525763624480417867)
                    ·
                      rfl

theorem cell23_7180258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_7180258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7180258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7180258 prefixEnd_7180258 := by exact prefixLift 7180258
  have htrace : WordTrace (prefixWord ++ tailWord_7180258) baseStart_7180258 baseEnd_7180258 := by
    simpa [prefixWord, tailWord_7180258, baseEnd_7180258] using wordTrace_append hprefix tailTrace_7180258
  have hstable : (prefixWord ++ tailWord_7180258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7180258).length < 2 ^ (prefixWord ++ tailWord_7180258).sum := by decide
  have hdescent : baseEnd_7180258 < baseStart_7180258 := by decide
  rcases family_descends (prefixWord ++ tailWord_7180258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7180287 : List Nat := [1, 1, 2, 2, 1, 2, 1, 3, 2, 6, 2]
def baseStart_7180287 : Nat := 118140960795 + 7180287 * 2 ^ 59
def prefixEnd_7180287 : Nat := 4983230072969 + 3 ^ 40 * 7180287 * 2
def baseEnd_7180287 : Nat := 3686938468229853827790967

theorem tailTrace_7180287 : CollatzResearch.WordTrace tailWord_7180287 prefixEnd_7180287 3686938468229853827790967 := by
  unfold tailWord_7180287
  simp only [CollatzResearch.WordTrace]
  refine ⟨261886581738053969234347115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174591054492035979489564743 261886581738053969234347115)
  ·
    refine ⟨392829872607080953851520673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261886581738053969234347115 392829872607080953851520673)
    ·
      refine ⟨294622404455310715388640505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 392829872607080953851520673 294622404455310715388640505)
      ·
        refine ⟨220966803341483036541480379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 294622404455310715388640505 220966803341483036541480379)
        ·
          refine ⟨331450205012224554812220569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220966803341483036541480379 331450205012224554812220569)
          ·
            refine ⟨248587653759168416109165427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 331450205012224554812220569 248587653759168416109165427)
            ·
              refine ⟨372881480638752624163748141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248587653759168416109165427 372881480638752624163748141)
              ·
                refine ⟨139830555239532234061405553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 372881480638752624163748141 139830555239532234061405553)
                ·
                  refine ⟨104872916429649175546054165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139830555239532234061405553 104872916429649175546054165)
                  ·
                    refine ⟨4915917957639805103721289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 104872916429649175546054165 4915917957639805103721289)
                    ·
                      refine ⟨3686938468229853827790967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4915917957639805103721289 3686938468229853827790967)
                      ·
                        rfl

theorem cell23_7180287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 6, 2].length) (baseStart_7180287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7180287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7180287 prefixEnd_7180287 := by exact prefixLift 7180287
  have htrace : WordTrace (prefixWord ++ tailWord_7180287) baseStart_7180287 baseEnd_7180287 := by
    simpa [prefixWord, tailWord_7180287, baseEnd_7180287] using wordTrace_append hprefix tailTrace_7180287
  have hstable : (prefixWord ++ tailWord_7180287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7180287).length < 2 ^ (prefixWord ++ tailWord_7180287).sum := by decide
  have hdescent : baseEnd_7180287 < baseStart_7180287 := by decide
  rcases family_descends (prefixWord ++ tailWord_7180287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7180304 : List Nat := [2, 1, 1, 1, 1, 1, 1, 6, 5, 2, 2]
def baseStart_7180304 : Nat := 118140960795 + 7180304 * 2 ^ 59
def prefixEnd_7180304 : Nat := 4983230072969 + 3 ^ 40 * 7180304 * 2
def baseEnd_7180304 : Nat := 3686947197400980261278389

theorem tailTrace_7180304 : CollatzResearch.WordTrace tailWord_7180304 prefixEnd_7180304 3686947197400980261278389 := by
  unfold tailWord_7180304
  simp only [CollatzResearch.WordTrace]
  refine ⟨130943600889496190568857983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174591467852661587425143977 130943600889496190568857983)
  ·
    refine ⟨196415401334244285853286975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130943600889496190568857983 196415401334244285853286975)
    ·
      refine ⟨294623102001366428779930463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196415401334244285853286975 294623102001366428779930463)
      ·
        refine ⟨441934653002049643169895695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294623102001366428779930463 441934653002049643169895695)
        ·
          refine ⟨662901979503074464754843543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 441934653002049643169895695 662901979503074464754843543)
          ·
            refine ⟨994352969254611697132265315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 662901979503074464754843543 994352969254611697132265315)
            ·
              refine ⟨1491529453881917545698397973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 994352969254611697132265315 1491529453881917545698397973)
              ·
                refine ⟨69915443150714884954612405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1491529453881917545698397973 69915443150714884954612405)
                ·
                  refine ⟨6554572795379520464494913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69915443150714884954612405 6554572795379520464494913)
                  ·
                    refine ⟨4915929596534640348371185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6554572795379520464494913 4915929596534640348371185)
                    ·
                      refine ⟨3686947197400980261278389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4915929596534640348371185 3686947197400980261278389)
                      ·
                        rfl

theorem cell23_7180304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 5, 2, 2].length) (baseStart_7180304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7180304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7180304 prefixEnd_7180304 := by exact prefixLift 7180304
  have htrace : WordTrace (prefixWord ++ tailWord_7180304) baseStart_7180304 baseEnd_7180304 := by
    simpa [prefixWord, tailWord_7180304, baseEnd_7180304] using wordTrace_append hprefix tailTrace_7180304
  have hstable : (prefixWord ++ tailWord_7180304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7180304).length < 2 ^ (prefixWord ++ tailWord_7180304).sum := by decide
  have hdescent : baseEnd_7180304 < baseStart_7180304 := by decide
  rcases family_descends (prefixWord ++ tailWord_7180304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7180307 : List Nat := [1, 1, 1, 2, 1, 4, 5, 1, 1, 1, 5]
def baseStart_7180307 : Nat := 118140960795 + 7180307 * 2 ^ 59
def prefixEnd_7180307 : Nat := 4983230072969 + 3 ^ 40 * 7180307 * 2
def baseEnd_7180307 : Nat := 3686948737842943749540875

theorem tailTrace_7180307 : CollatzResearch.WordTrace tailWord_7180307 prefixEnd_7180307 3686948737842943749540875 := by
  unfold tailWord_7180307
  simp only [CollatzResearch.WordTrace]
  refine ⟨261887311197981512650075175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174591540798654341766716783 261887311197981512650075175)
  ·
    refine ⟨392830966796972268975112763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261887311197981512650075175 392830966796972268975112763)
    ·
      refine ⟨589246450195458403462669145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392830966796972268975112763 589246450195458403462669145)
      ·
        refine ⟨441934837646593802597001859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 589246450195458403462669145 441934837646593802597001859)
        ·
          refine ⟨662902256469890703895502789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 441934837646593802597001859 662902256469890703895502789)
          ·
            refine ⟨124294173088104506980406773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 662902256469890703895502789 124294173088104506980406773)
            ·
              refine ⟨11652578727009797529413135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 124294173088104506980406773 11652578727009797529413135)
              ·
                refine ⟨17478868090514696294119703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11652578727009797529413135 17478868090514696294119703)
                ·
                  refine ⟨26218302135772044441179555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17478868090514696294119703 26218302135772044441179555)
                  ·
                    refine ⟨39327453203658066661769333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26218302135772044441179555 39327453203658066661769333)
                    ·
                      refine ⟨3686948737842943749540875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39327453203658066661769333 3686948737842943749540875)
                      ·
                        rfl

theorem cell23_7180307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 1, 1, 1, 5].length) (baseStart_7180307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7180307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7180307 prefixEnd_7180307 := by exact prefixLift 7180307
  have htrace : WordTrace (prefixWord ++ tailWord_7180307) baseStart_7180307 baseEnd_7180307 := by
    simpa [prefixWord, tailWord_7180307, baseEnd_7180307] using wordTrace_append hprefix tailTrace_7180307
  have hstable : (prefixWord ++ tailWord_7180307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7180307).length < 2 ^ (prefixWord ++ tailWord_7180307).sum := by decide
  have hdescent : baseEnd_7180307 < baseStart_7180307 := by decide
  rcases family_descends (prefixWord ++ tailWord_7180307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7180310 : List Nat := [5, 18]
def baseStart_7180310 : Nat := 118140960795 + 7180310 * 2 ^ 59
def prefixEnd_7180310 : Nat := 4983230072969 + 3 ^ 40 * 7180310 * 2
def baseEnd_7180310 : Nat := 187316480124214156267

theorem tailTrace_7180310 : CollatzResearch.WordTrace tailWord_7180310 prefixEnd_7180310 187316480124214156267 := by
  unfold tailWord_7180310
  simp only [CollatzResearch.WordTrace]
  refine ⟨16367963788560665260152149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 174591613744647096108289589 16367963788560665260152149)
  ·
    refine ⟨187316480124214156267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 18 16367963788560665260152149 187316480124214156267)
    ·
      rfl

theorem cell23_7180310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 18].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 18].length) (baseStart_7180310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7180310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7180310 prefixEnd_7180310 := by exact prefixLift 7180310
  have htrace : WordTrace (prefixWord ++ tailWord_7180310) baseStart_7180310 baseEnd_7180310 := by
    simpa [prefixWord, tailWord_7180310, baseEnd_7180310] using wordTrace_append hprefix tailTrace_7180310
  have hstable : (prefixWord ++ tailWord_7180310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7180310).length < 2 ^ (prefixWord ++ tailWord_7180310).sum := by decide
  have hdescent : baseEnd_7180310 < baseStart_7180310 := by decide
  rcases family_descends (prefixWord ++ tailWord_7180310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7180314 : List Nat := [3, 1, 1, 3, 1, 3, 1, 4, 2, 4]
def baseStart_7180314 : Nat := 118140960795 + 7180314 * 2 ^ 59
def prefixEnd_7180314 : Nat := 4983230072969 + 3 ^ 40 * 7180314 * 2
def baseEnd_7180314 : Nat := 1228984110735841740717781

theorem tailTrace_7180314 : CollatzResearch.WordTrace tailWord_7180314 prefixEnd_7180314 1228984110735841740717781 := by
  unfold tailWord_7180314
  simp only [CollatzResearch.WordTrace]
  refine ⟨65471891627239038211394999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174591711005970768563719997 65471891627239038211394999)
  ·
    refine ⟨98207837440858557317092499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65471891627239038211394999 98207837440858557317092499)
    ·
      refine ⟨147311756161287835975638749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98207837440858557317092499 147311756161287835975638749)
      ·
        refine ⟨55241908560482938490864531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147311756161287835975638749 55241908560482938490864531)
        ·
          refine ⟨82862862840724407736296797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55241908560482938490864531 82862862840724407736296797)
          ·
            refine ⟨31073573565271652901111299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82862862840724407736296797 31073573565271652901111299)
            ·
              refine ⟨46610360347907479351666949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31073573565271652901111299 46610360347907479351666949)
              ·
                refine ⟨8739442565232652378437553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46610360347907479351666949 8739442565232652378437553)
                ·
                  refine ⟨6554581923924489283828165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8739442565232652378437553 6554581923924489283828165)
                  ·
                    refine ⟨1228984110735841740717781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6554581923924489283828165 1228984110735841740717781)
                    ·
                      rfl

theorem cell23_7180314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 4, 2, 4].length) (baseStart_7180314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7180314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7180314 prefixEnd_7180314 := by exact prefixLift 7180314
  have htrace : WordTrace (prefixWord ++ tailWord_7180314) baseStart_7180314 baseEnd_7180314 := by
    simpa [prefixWord, tailWord_7180314, baseEnd_7180314] using wordTrace_append hprefix tailTrace_7180314
  have hstable : (prefixWord ++ tailWord_7180314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7180314).length < 2 ^ (prefixWord ++ tailWord_7180314).sum := by decide
  have hdescent : baseEnd_7180314 < baseStart_7180314 := by decide
  rcases family_descends (prefixWord ++ tailWord_7180314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7180334 : List Nat := [4, 1, 3, 1, 1, 2, 1, 3, 1, 2, 4]
def baseStart_7180334 : Nat := 118140960795 + 7180334 * 2 ^ 59
def prefixEnd_7180334 : Nat := 4983230072969 + 3 ^ 40 * 7180334 * 2
def baseEnd_7180334 : Nat := 3686962601820615143903251

theorem tailTrace_7180334 : CollatzResearch.WordTrace tailWord_7180334 prefixEnd_7180334 3686962601820615143903251 := by
  unfold tailWord_7180334
  simp only [CollatzResearch.WordTrace]
  refine ⟨32736036996110462032663507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174592197312589130840872037 32736036996110462032663507)
  ·
    refine ⟨49104055494165693048995261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32736036996110462032663507 49104055494165693048995261)
    ·
      refine ⟨18414020810312134893373223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49104055494165693048995261 18414020810312134893373223)
      ·
        refine ⟨27621031215468202340059835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18414020810312134893373223 27621031215468202340059835)
        ·
          refine ⟨41431546823202303510089753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27621031215468202340059835 41431546823202303510089753)
          ·
            refine ⟨31073660117401727632567315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41431546823202303510089753 31073660117401727632567315)
            ·
              refine ⟨46610490176102591448850973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31073660117401727632567315 46610490176102591448850973)
              ·
                refine ⟨17478933816038471793319115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46610490176102591448850973 17478933816038471793319115)
                ·
                  refine ⟨26218400724057707689978673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17478933816038471793319115 26218400724057707689978673)
                  ·
                    refine ⟨19663800543043280767484005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26218400724057707689978673 19663800543043280767484005)
                    ·
                      refine ⟨3686962601820615143903251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19663800543043280767484005 3686962601820615143903251)
                      ·
                        rfl

theorem cell23_7180334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_7180334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7180334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7180334 prefixEnd_7180334 := by exact prefixLift 7180334
  have htrace : WordTrace (prefixWord ++ tailWord_7180334) baseStart_7180334 baseEnd_7180334 := by
    simpa [prefixWord, tailWord_7180334, baseEnd_7180334] using wordTrace_append hprefix tailTrace_7180334
  have hstable : (prefixWord ++ tailWord_7180334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7180334).length < 2 ^ (prefixWord ++ tailWord_7180334).sum := by decide
  have hdescent : baseEnd_7180334 < baseStart_7180334 := by decide
  rcases family_descends (prefixWord ++ tailWord_7180334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7180344 : List Nat := [2, 1, 2, 1, 6, 1, 3, 7]
def baseStart_7180344 : Nat := 118140960795 + 7180344 * 2 ^ 59
def prefixEnd_7180344 : Nat := 4983230072969 + 3 ^ 40 * 7180344 * 2
def baseEnd_7180344 : Nat := 136554360615820744621415

theorem tailTrace_7180344 : CollatzResearch.WordTrace tailWord_7180344 prefixEnd_7180344 136554360615820744621415 := by
  unfold tailWord_7180344
  simp only [CollatzResearch.WordTrace]
  refine ⟨130944330349423733984586043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174592440465898311979448057 130944330349423733984586043)
  ·
    refine ⟨196416495524135600976879065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130944330349423733984586043 196416495524135600976879065)
    ·
      refine ⟨147312371643101700732659299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196416495524135600976879065 147312371643101700732659299)
      ·
        refine ⟨220968557464652551098988949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147312371643101700732659299 220968557464652551098988949)
        ·
          refine ⟨10357901131155588332765107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 220968557464652551098988949 10357901131155588332765107)
          ·
            refine ⟨15536851696733382499147661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10357901131155588332765107 15536851696733382499147661)
            ·
              refine ⟨5826319386275018437180373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15536851696733382499147661 5826319386275018437180373)
              ·
                refine ⟨136554360615820744621415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5826319386275018437180373 136554360615820744621415)
                ·
                  rfl

theorem cell23_7180344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 3, 7].length) (baseStart_7180344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7180344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7180344 prefixEnd_7180344 := by exact prefixLift 7180344
  have htrace : WordTrace (prefixWord ++ tailWord_7180344) baseStart_7180344 baseEnd_7180344 := by
    simpa [prefixWord, tailWord_7180344, baseEnd_7180344] using wordTrace_append hprefix tailTrace_7180344
  have hstable : (prefixWord ++ tailWord_7180344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7180344).length < 2 ^ (prefixWord ++ tailWord_7180344).sum := by decide
  have hdescent : baseEnd_7180344 < baseStart_7180344 := by decide
  rcases family_descends (prefixWord ++ tailWord_7180344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7180358 : List Nat := [6, 1, 1, 1, 1, 1, 3, 3, 1, 2, 3]
def baseStart_7180358 : Nat := 118140960795 + 7180358 * 2 ^ 59
def prefixEnd_7180358 : Nat := 4983230072969 + 3 ^ 40 * 7180358 * 2
def baseEnd_7180358 : Nat := 3686974925356323050003141

theorem tailTrace_7180358 : CollatzResearch.WordTrace tailWord_7180358 prefixEnd_7180358 3686974925356323050003141 := by
  unfold tailWord_7180358
  simp only [CollatzResearch.WordTrace]
  refine ⟨8184036603774898386255679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 174592780880531165573454485 8184036603774898386255679)
  ·
    refine ⟨12276054905662347579383519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8184036603774898386255679 12276054905662347579383519)
    ·
      refine ⟨18414082358493521369075279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12276054905662347579383519 18414082358493521369075279)
      ·
        refine ⟨27621123537740282053612919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18414082358493521369075279 27621123537740282053612919)
        ·
          refine ⟨41431685306610423080419379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27621123537740282053612919 41431685306610423080419379)
          ·
            refine ⟨62147527959915634620629069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41431685306610423080419379 62147527959915634620629069)
            ·
              refine ⟨23305322984968362982735901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62147527959915634620629069 23305322984968362982735901)
              ·
                refine ⟨8739496119363136118525963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23305322984968362982735901 8739496119363136118525963)
                ·
                  refine ⟨13109244179044704177788945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8739496119363136118525963 13109244179044704177788945)
                  ·
                    refine ⟨9831933134283528133341709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13109244179044704177788945 9831933134283528133341709)
                    ·
                      refine ⟨3686974925356323050003141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9831933134283528133341709 3686974925356323050003141)
                      ·
                        rfl

theorem cell23_7180358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_7180358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7180358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7180358 prefixEnd_7180358 := by exact prefixLift 7180358
  have htrace : WordTrace (prefixWord ++ tailWord_7180358) baseStart_7180358 baseEnd_7180358 := by
    simpa [prefixWord, tailWord_7180358, baseEnd_7180358] using wordTrace_append hprefix tailTrace_7180358
  have hstable : (prefixWord ++ tailWord_7180358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7180358).length < 2 ^ (prefixWord ++ tailWord_7180358).sum := by decide
  have hdescent : baseEnd_7180358 < baseStart_7180358 := by decide
  rcases family_descends (prefixWord ++ tailWord_7180358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7180382 : List Nat := [4, 4, 1, 1, 2, 1, 3, 1, 2, 4]
def baseStart_7180382 : Nat := 118140960795 + 7180382 * 2 ^ 59
def prefixEnd_7180382 : Nat := 4983230072969 + 3 ^ 40 * 7180382 * 2
def baseEnd_7180382 : Nat := 1228995749630676985367677

theorem tailTrace_7180382 : CollatzResearch.WordTrace tailWord_7180382 prefixEnd_7180382 1228995749630676985367677 := by
  unfold tailWord_7180382
  simp only [CollatzResearch.WordTrace]
  refine ⟨32736255834088725057381925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174593364448473200306036933 32736255834088725057381925)
  ·
    refine ⟨6138047968891635948259111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32736255834088725057381925 6138047968891635948259111)
    ·
      refine ⟨9207071953337453922388667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6138047968891635948259111 9207071953337453922388667)
      ·
        refine ⟨13810607930006180883583001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9207071953337453922388667 13810607930006180883583001)
        ·
          refine ⟨10357955947504635662687251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13810607930006180883583001 10357955947504635662687251)
          ·
            refine ⟨15536933921256953494030877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10357955947504635662687251 15536933921256953494030877)
            ·
              refine ⟨5826350220471357560261579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15536933921256953494030877 5826350220471357560261579)
              ·
                refine ⟨8739525330707036340392369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5826350220471357560261579 8739525330707036340392369)
                ·
                  refine ⟨6554643998030277255294277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8739525330707036340392369 6554643998030277255294277)
                  ·
                    refine ⟨1228995749630676985367677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6554643998030277255294277 1228995749630676985367677)
                    ·
                      rfl

theorem cell23_7180382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_7180382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7180382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7180382 prefixEnd_7180382 := by exact prefixLift 7180382
  have htrace : WordTrace (prefixWord ++ tailWord_7180382) baseStart_7180382 baseEnd_7180382 := by
    simpa [prefixWord, tailWord_7180382, baseEnd_7180382] using wordTrace_append hprefix tailTrace_7180382
  have hstable : (prefixWord ++ tailWord_7180382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7180382).length < 2 ^ (prefixWord ++ tailWord_7180382).sum := by decide
  have hdescent : baseEnd_7180382 < baseStart_7180382 := by decide
  rcases family_descends (prefixWord ++ tailWord_7180382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7180387 : List Nat := [1, 1, 1, 5, 1, 1, 4, 1, 2, 6]
def baseStart_7180387 : Nat := 118140960795 + 7180387 * 2 ^ 59
def prefixEnd_7180387 : Nat := 4983230072969 + 3 ^ 40 * 7180387 * 2
def baseEnd_7180387 : Nat := 1228996605431767812180169

theorem tailTrace_7180387 : CollatzResearch.WordTrace tailWord_7180387 prefixEnd_7180387 1228996605431767812180169 := by
  unfold tailWord_7180387
  simp only [CollatzResearch.WordTrace]
  refine ⟨261890229037691686312987415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174593486025127790875324943 261890229037691686312987415)
  ·
    refine ⟨392835343556537529469481123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261890229037691686312987415 392835343556537529469481123)
    ·
      refine ⟨589253015334806294204221685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392835343556537529469481123 589253015334806294204221685)
      ·
        refine ⟨55242470187638090081645783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 589253015334806294204221685 55242470187638090081645783)
        ·
          refine ⟨82863705281457135122468675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55242470187638090081645783 82863705281457135122468675)
          ·
            refine ⟨124295557922185702683703013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82863705281457135122468675 124295557922185702683703013)
            ·
              refine ⟨23305417110409819253194315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 124295557922185702683703013 23305417110409819253194315)
              ·
                refine ⟨34958125665614728879791473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23305417110409819253194315 34958125665614728879791473)
                ·
                  refine ⟨26218594249211046659843605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34958125665614728879791473 26218594249211046659843605)
                  ·
                    refine ⟨1228996605431767812180169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26218594249211046659843605 1228996605431767812180169)
                    ·
                      rfl

theorem cell23_7180387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 1, 2, 6].length) (baseStart_7180387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7180387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7180387 prefixEnd_7180387 := by exact prefixLift 7180387
  have htrace : WordTrace (prefixWord ++ tailWord_7180387) baseStart_7180387 baseEnd_7180387 := by
    simpa [prefixWord, tailWord_7180387, baseEnd_7180387] using wordTrace_append hprefix tailTrace_7180387
  have hstable : (prefixWord ++ tailWord_7180387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7180387).length < 2 ^ (prefixWord ++ tailWord_7180387).sum := by decide
  have hdescent : baseEnd_7180387 < baseStart_7180387 := by decide
  rcases family_descends (prefixWord ++ tailWord_7180387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7180398 : List Nat := [4, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2]
def baseStart_7180398 : Nat := 118140960795 + 7180398 * 2 ^ 59
def prefixEnd_7180398 : Nat := 4983230072969 + 3 ^ 40 * 7180398 * 2
def baseEnd_7180398 : Nat := 3686995464582502893502957

theorem tailTrace_7180398 : CollatzResearch.WordTrace tailWord_7180398 prefixEnd_7180398 3686995464582502893502957 := by
  unfold tailWord_7180398
  simp only [CollatzResearch.WordTrace]
  refine ⟨32736328780081479398954731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174593753493767890127758565 32736328780081479398954731)
  ·
    refine ⟨49104493170122219098432097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32736328780081479398954731 49104493170122219098432097)
    ·
      refine ⟨36828369877591664323824073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49104493170122219098432097 36828369877591664323824073)
      ·
        refine ⟨27621277408193748242868055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36828369877591664323824073 27621277408193748242868055)
        ·
          refine ⟨41431916112290622364302083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27621277408193748242868055 41431916112290622364302083)
          ·
            refine ⟨62147874168435933546453125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41431916112290622364302083 62147874168435933546453125)
            ·
              refine ⟨11652726406581737539959961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62147874168435933546453125 11652726406581737539959961)
              ·
                refine ⟨8739544804936303154969971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11652726406581737539959961 8739544804936303154969971)
                ·
                  refine ⟨13109317207404454732454957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8739544804936303154969971 13109317207404454732454957)
                  ·
                    refine ⟨4915993952776670524670609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13109317207404454732454957 4915993952776670524670609)
                    ·
                      refine ⟨3686995464582502893502957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4915993952776670524670609 3686995464582502893502957)
                      ·
                        rfl

theorem cell23_7180398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2].length) (baseStart_7180398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7180398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7180398 prefixEnd_7180398 := by exact prefixLift 7180398
  have htrace : WordTrace (prefixWord ++ tailWord_7180398) baseStart_7180398 baseEnd_7180398 := by
    simpa [prefixWord, tailWord_7180398, baseEnd_7180398] using wordTrace_append hprefix tailTrace_7180398
  have hstable : (prefixWord ++ tailWord_7180398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7180398).length < 2 ^ (prefixWord ++ tailWord_7180398).sum := by decide
  have hdescent : baseEnd_7180398 < baseStart_7180398 := by decide
  rcases family_descends (prefixWord ++ tailWord_7180398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7180444 : List Nat := [2, 2, 3, 2, 1, 1, 2, 1, 1, 5, 3]
def baseStart_7180444 : Nat := 118140960795 + 7180444 * 2 ^ 59
def prefixEnd_7180444 : Nat := 4983230072969 + 3 ^ 40 * 7180444 * 2
def baseEnd_7180444 : Nat := 3687019084692609713527745

theorem tailTrace_7180444 : CollatzResearch.WordTrace tailWord_7180444 prefixEnd_7180444 3687019084692609713527745 := by
  unfold tailWord_7180444
  simp only [CollatzResearch.WordTrace]
  refine ⟨130946153999242592523906193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174594871998990123365208257 130946153999242592523906193)
  ·
    refine ⟨98209615499431944392929645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130946153999242592523906193 98209615499431944392929645)
    ·
      refine ⟨36828605812286979147348617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98209615499431944392929645 36828605812286979147348617)
      ·
        refine ⟨27621454359215234360511463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36828605812286979147348617 27621454359215234360511463)
        ·
          refine ⟨41432181538822851540767195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27621454359215234360511463 41432181538822851540767195)
          ·
            refine ⟨62148272308234277311150793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41432181538822851540767195 62148272308234277311150793)
            ·
              refine ⟨46611204231175707983363095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62148272308234277311150793 46611204231175707983363095)
              ·
                refine ⟨69916806346763561975044643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46611204231175707983363095 69916806346763561975044643)
                ·
                  refine ⟨104875209520145342962566965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69916806346763561975044643 104875209520145342962566965)
                  ·
                    refine ⟨9832050892513625902740653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 104875209520145342962566965 9832050892513625902740653)
                    ·
                      refine ⟨3687019084692609713527745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9832050892513625902740653 3687019084692609713527745)
                      ·
                        rfl

theorem cell23_7180444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_7180444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7180444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7180444 prefixEnd_7180444 := by exact prefixLift 7180444
  have htrace : WordTrace (prefixWord ++ tailWord_7180444) baseStart_7180444 baseEnd_7180444 := by
    simpa [prefixWord, tailWord_7180444, baseEnd_7180444] using wordTrace_append hprefix tailTrace_7180444
  have hstable : (prefixWord ++ tailWord_7180444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7180444).length < 2 ^ (prefixWord ++ tailWord_7180444).sum := by decide
  have hdescent : baseEnd_7180444 < baseStart_7180444 := by decide
  rcases family_descends (prefixWord ++ tailWord_7180444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7180445 : List Nat := [1, 4, 2, 1, 1, 3, 4, 1, 2, 2, 2]
def baseStart_7180445 : Nat := 118140960795 + 7180445 * 2 ^ 59
def prefixEnd_7180445 : Nat := 4983230072969 + 3 ^ 40 * 7180445 * 2
def baseEnd_7180445 : Nat := 3687019598173264209615241

theorem tailTrace_7180445 : CollatzResearch.WordTrace tailWord_7180445 prefixEnd_7180445 3687019598173264209615241 := by
  unfold tailWord_7180445
  simp only [CollatzResearch.WordTrace]
  refine ⟨261892344471481562218598789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174594896314321041479065859 261892344471481562218598789)
  ·
    refine ⟨49104814588402792915987273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 261892344471481562218598789 49104814588402792915987273)
    ·
      refine ⟨36828610941302094686990455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49104814588402792915987273 36828610941302094686990455)
      ·
        refine ⟨55242916411953142030485683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36828610941302094686990455 55242916411953142030485683)
        ·
          refine ⟨82864374617929713045728525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55242916411953142030485683 82864374617929713045728525)
          ·
            refine ⟨31074140481723642392148197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82864374617929713045728525 31074140481723642392148197)
            ·
              refine ⟨5826401340323182948527787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31074140481723642392148197 5826401340323182948527787)
              ·
                refine ⟨8739602010484774422791681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5826401340323182948527787 8739602010484774422791681)
                ·
                  refine ⟨6554701507863580817093761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8739602010484774422791681 6554701507863580817093761)
                  ·
                    refine ⟨4916026130897685612820321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6554701507863580817093761 4916026130897685612820321)
                    ·
                      refine ⟨3687019598173264209615241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4916026130897685612820321 3687019598173264209615241)
                      ·
                        rfl

theorem cell23_7180445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 4, 1, 2, 2, 2].length) (baseStart_7180445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7180445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7180445 prefixEnd_7180445 := by exact prefixLift 7180445
  have htrace : WordTrace (prefixWord ++ tailWord_7180445) baseStart_7180445 baseEnd_7180445 := by
    simpa [prefixWord, tailWord_7180445, baseEnd_7180445] using wordTrace_append hprefix tailTrace_7180445
  have hstable : (prefixWord ++ tailWord_7180445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7180445).length < 2 ^ (prefixWord ++ tailWord_7180445).sum := by decide
  have hdescent : baseEnd_7180445 < baseStart_7180445 := by decide
  rcases family_descends (prefixWord ++ tailWord_7180445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7180515 : List Nat := [1, 1, 1, 8, 2, 1, 1, 1, 2, 5]
def baseStart_7180515 : Nat := 118140960795 + 7180515 * 2 ^ 59
def prefixEnd_7180515 : Nat := 4983230072969 + 3 ^ 40 * 7180515 * 2
def baseEnd_7180515 : Nat := 1229018513939692978579973

theorem tailTrace_7180515 : CollatzResearch.WordTrace tailWord_7180515 prefixEnd_7180515 1229018513939692978579973 := by
  unfold tailWord_7180515
  simp only [CollatzResearch.WordTrace]
  refine ⟨261894897581227964173646999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174596598387485309449097999 261894897581227964173646999)
  ·
    refine ⟨392842346371841946260470499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261894897581227964173646999 392842346371841946260470499)
    ·
      refine ⟨589263519557762919390705749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392842346371841946260470499 589263519557762919390705749)
      ·
        refine ⟨6905431869817534211609833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 589263519557762919390705749 6905431869817534211609833)
        ·
          refine ⟨5179073902363150658707375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6905431869817534211609833 5179073902363150658707375)
          ·
            refine ⟨7768610853544725988061063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5179073902363150658707375 7768610853544725988061063)
            ·
              refine ⟨11652916280317088982091595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7768610853544725988061063 11652916280317088982091595)
              ·
                refine ⟨17479374420475633473137393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11652916280317088982091595 17479374420475633473137393)
                ·
                  refine ⟨13109530815356725104853045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17479374420475633473137393 13109530815356725104853045)
                  ·
                    refine ⟨1229018513939692978579973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13109530815356725104853045 1229018513939692978579973)
                    ·
                      rfl

theorem cell23_7180515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 1, 2, 5].length) (baseStart_7180515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7180515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7180515 prefixEnd_7180515 := by exact prefixLift 7180515
  have htrace : WordTrace (prefixWord ++ tailWord_7180515) baseStart_7180515 baseEnd_7180515 := by
    simpa [prefixWord, tailWord_7180515, baseEnd_7180515] using wordTrace_append hprefix tailTrace_7180515
  have hstable : (prefixWord ++ tailWord_7180515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7180515).length < 2 ^ (prefixWord ++ tailWord_7180515).sum := by decide
  have hdescent : baseEnd_7180515 < baseStart_7180515 := by decide
  rcases family_descends (prefixWord ++ tailWord_7180515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7180554 : List Nat := [3, 1, 2, 2, 1, 1, 2, 1, 5, 5]
def baseStart_7180554 : Nat := 118140960795 + 7180554 * 2 ^ 59
def prefixEnd_7180554 : Nat := 4983230072969 + 3 ^ 40 * 7180554 * 2
def baseEnd_7180554 : Nat := 1229025189188201427717413

theorem tailTrace_7180554 : CollatzResearch.WordTrace tailWord_7180554 prefixEnd_7180554 1229025189188201427717413 := by
  unfold tailWord_7180554
  simp only [CollatzResearch.WordTrace]
  refine ⟨65474080007021668458579179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174597546685391115889544477 65474080007021668458579179)
  ·
    refine ⟨98211120010532502687868769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65474080007021668458579179 98211120010532502687868769)
    ·
      refine ⟨73658340007899377015901577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98211120010532502687868769 73658340007899377015901577)
      ·
        refine ⟨55243755005924532761926183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73658340007899377015901577 55243755005924532761926183)
        ·
          refine ⟨82865632508886799142889275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55243755005924532761926183 82865632508886799142889275)
          ·
            refine ⟨124298448763330198714333913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82865632508886799142889275 124298448763330198714333913)
            ·
              refine ⟨93223836572497649035750435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124298448763330198714333913 93223836572497649035750435)
              ·
                refine ⟨139835754858746473553625653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93223836572497649035750435 139835754858746473553625653)
                ·
                  refine ⟨13109602018007481895652405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 139835754858746473553625653 13109602018007481895652405)
                  ·
                    refine ⟨1229025189188201427717413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13109602018007481895652405 1229025189188201427717413)
                    ·
                      rfl

theorem cell23_7180554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 5, 5].length) (baseStart_7180554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7180554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7180554 prefixEnd_7180554 := by exact prefixLift 7180554
  have htrace : WordTrace (prefixWord ++ tailWord_7180554) baseStart_7180554 baseEnd_7180554 := by
    simpa [prefixWord, tailWord_7180554, baseEnd_7180554] using wordTrace_append hprefix tailTrace_7180554
  have hstable : (prefixWord ++ tailWord_7180554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7180554).length < 2 ^ (prefixWord ++ tailWord_7180554).sum := by decide
  have hdescent : baseEnd_7180554 < baseStart_7180554 := by decide
  rcases family_descends (prefixWord ++ tailWord_7180554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7180561 : List Nat := [1, 2, 2, 1, 1, 5, 1, 2, 1, 5, 2]
def baseStart_7180561 : Nat := 118140960795 + 7180561 * 2 ^ 59
def prefixEnd_7180561 : Nat := 4983230072969 + 3 ^ 40 * 7180561 * 2
def baseEnd_7180561 : Nat := 3687079161929185755764707

theorem tailTrace_7180561 : CollatzResearch.WordTrace tailWord_7180561 prefixEnd_7180561 3687079161929185755764707 := by
  unfold tailWord_7180561
  simp only [CollatzResearch.WordTrace]
  refine ⟨261896575339061314029821537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174597716892707542686547691 261896575339061314029821537)
  ·
    refine ⟨196422431504295985522366153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261896575339061314029821537 196422431504295985522366153)
    ·
      refine ⟨147316823628221989141774615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196422431504295985522366153 147316823628221989141774615)
      ·
        refine ⟨220975235442332983712661923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147316823628221989141774615 220975235442332983712661923)
        ·
          refine ⟨331462853163499475568992885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220975235442332983712661923 331462853163499475568992885)
          ·
            refine ⟨31074642484078075834593083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 331462853163499475568992885 31074642484078075834593083)
            ·
              refine ⟨46611963726117113751889625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31074642484078075834593083 46611963726117113751889625)
              ·
                refine ⟨34958972794587835313917219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46611963726117113751889625 34958972794587835313917219)
                ·
                  refine ⟨52438459191881752970875829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34958972794587835313917219 52438459191881752970875829)
                  ·
                    refine ⟨4916105549238914341019609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52438459191881752970875829 4916105549238914341019609)
                    ·
                      refine ⟨3687079161929185755764707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4916105549238914341019609 3687079161929185755764707)
                      ·
                        rfl

theorem cell23_7180561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 5, 2].length) (baseStart_7180561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7180561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7180561 prefixEnd_7180561 := by exact prefixLift 7180561
  have htrace : WordTrace (prefixWord ++ tailWord_7180561) baseStart_7180561 baseEnd_7180561 := by
    simpa [prefixWord, tailWord_7180561, baseEnd_7180561] using wordTrace_append hprefix tailTrace_7180561
  have hstable : (prefixWord ++ tailWord_7180561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7180561).length < 2 ^ (prefixWord ++ tailWord_7180561).sum := by decide
  have hdescent : baseEnd_7180561 < baseStart_7180561 := by decide
  rcases family_descends (prefixWord ++ tailWord_7180561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7180578 : List Nat := [3, 3, 1, 1, 3, 1, 2, 1, 1, 5, 2]
def baseStart_7180578 : Nat := 118140960795 + 7180578 * 2 ^ 59
def prefixEnd_7180578 : Nat := 4983230072969 + 3 ^ 40 * 7180578 * 2
def baseEnd_7180578 : Nat := 3687087891100312189252129

theorem tailTrace_7180578 : CollatzResearch.WordTrace tailWord_7180578 prefixEnd_7180578 3687087891100312189252129 := by
  unfold tailWord_7180578
  simp only [CollatzResearch.WordTrace]
  refine ⟨65474298844999931483297597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174598130253333150622126925 65474298844999931483297597)
  ·
    refine ⟨24552862066874974306236599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65474298844999931483297597 24552862066874974306236599)
    ·
      refine ⟨36829293100312461459354899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24552862066874974306236599 36829293100312461459354899)
      ·
        refine ⟨55243939650468692189032349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36829293100312461459354899 55243939650468692189032349)
        ·
          refine ⟨20716477368925759570887131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55243939650468692189032349 20716477368925759570887131)
          ·
            refine ⟨31074716053388639356330697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20716477368925759570887131 31074716053388639356330697)
            ·
              refine ⟨23306037040041479517248023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31074716053388639356330697 23306037040041479517248023)
              ·
                refine ⟨34959055560062219275872035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23306037040041479517248023 34959055560062219275872035)
                ·
                  refine ⟨52438583340093328913808053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34959055560062219275872035 52438583340093328913808053)
                  ·
                    refine ⟨4916117188133749585669505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52438583340093328913808053 4916117188133749585669505)
                    ·
                      refine ⟨3687087891100312189252129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4916117188133749585669505 3687087891100312189252129)
                      ·
                        rfl

theorem cell23_7180578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 1, 1, 5, 2].length) (baseStart_7180578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7180578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7180578 prefixEnd_7180578 := by exact prefixLift 7180578
  have htrace : WordTrace (prefixWord ++ tailWord_7180578) baseStart_7180578 baseEnd_7180578 := by
    simpa [prefixWord, tailWord_7180578, baseEnd_7180578] using wordTrace_append hprefix tailTrace_7180578
  have hstable : (prefixWord ++ tailWord_7180578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7180578).length < 2 ^ (prefixWord ++ tailWord_7180578).sum := by decide
  have hdescent : baseEnd_7180578 < baseStart_7180578 := by decide
  rcases family_descends (prefixWord ++ tailWord_7180578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7180591 : List Nat := [1, 1, 2, 1, 2, 1, 6, 3, 1, 1, 4]
def baseStart_7180591 : Nat := 118140960795 + 7180591 * 2 ^ 59
def prefixEnd_7180591 : Nat := 4983230072969 + 3 ^ 40 * 7180591 * 2
def baseEnd_7180591 : Nat := 3687094566348820638389569

theorem tailTrace_7180591 : CollatzResearch.WordTrace tailWord_7180591 prefixEnd_7180591 3687094566348820638389569 := by
  unfold tailWord_7180591
  simp only [CollatzResearch.WordTrace]
  refine ⟨261897669528952629153413627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174598446352635086102275751 261897669528952629153413627)
  ·
    refine ⟨392846504293428943730120441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261897669528952629153413627 392846504293428943730120441)
    ·
      refine ⟨294634878220071707797590331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 392846504293428943730120441 294634878220071707797590331)
      ·
        refine ⟨441952317330107561696385497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294634878220071707797590331 441952317330107561696385497)
        ·
          refine ⟨331464237997580671272289123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 441952317330107561696385497 331464237997580671272289123)
          ·
            refine ⟨497196356996371006908433685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 331464237997580671272289123 497196356996371006908433685)
            ·
              refine ⟨23306079234204890948832829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 497196356996371006908433685 23306079234204890948832829)
              ·
                refine ⟨8739779712826834105812311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23306079234204890948832829 8739779712826834105812311)
                ·
                  refine ⟨13109669569240251158718467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8739779712826834105812311 13109669569240251158718467)
                  ·
                    refine ⟨19664504353860376738077701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13109669569240251158718467 19664504353860376738077701)
                    ·
                      refine ⟨3687094566348820638389569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19664504353860376738077701 3687094566348820638389569)
                      ·
                        rfl

theorem cell23_7180591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 3, 1, 1, 4].length) (baseStart_7180591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7180591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7180591 prefixEnd_7180591 := by exact prefixLift 7180591
  have htrace : WordTrace (prefixWord ++ tailWord_7180591) baseStart_7180591 baseEnd_7180591 := by
    simpa [prefixWord, tailWord_7180591, baseEnd_7180591] using wordTrace_append hprefix tailTrace_7180591
  have hstable : (prefixWord ++ tailWord_7180591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7180591).length < 2 ^ (prefixWord ++ tailWord_7180591).sum := by decide
  have hdescent : baseEnd_7180591 < baseStart_7180591 := by decide
  rcases family_descends (prefixWord ++ tailWord_7180591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7180602 : List Nat := [3, 1, 1, 1, 4, 3, 3, 2, 1, 1, 3]
def baseStart_7180602 : Nat := 118140960795 + 7180602 * 2 ^ 59
def prefixEnd_7180602 : Nat := 4983230072969 + 3 ^ 40 * 7180602 * 2
def baseEnd_7180602 : Nat := 3687100214636020095352019

theorem tailTrace_7180602 : CollatzResearch.WordTrace tailWord_7180602 prefixEnd_7180602 3687100214636020095352019 := by
  unfold tailWord_7180602
  simp only [CollatzResearch.WordTrace]
  refine ⟨65474517682978194508016015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174598713821275185354709373 65474517682978194508016015)
  ·
    refine ⟨98211776524467291762024023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65474517682978194508016015 98211776524467291762024023)
    ·
      refine ⟨147317664786700937643036035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98211776524467291762024023 147317664786700937643036035)
      ·
        refine ⟨220976497180051406464554053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147317664786700937643036035 220976497180051406464554053)
        ·
          refine ⟨41433093221259638712103885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 220976497180051406464554053 41433093221259638712103885)
          ·
            refine ⟨15537409957972364517038957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41433093221259638712103885 15537409957972364517038957)
            ·
              refine ⟨5826528734239636693889609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15537409957972364517038957 5826528734239636693889609)
              ·
                refine ⟨4369896550679727520417207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5826528734239636693889609 4369896550679727520417207)
                ·
                  refine ⟨6554844826019591280625811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4369896550679727520417207 6554844826019591280625811)
                  ·
                    refine ⟨9832267239029386920938717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6554844826019591280625811 9832267239029386920938717)
                    ·
                      refine ⟨3687100214636020095352019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9832267239029386920938717 3687100214636020095352019)
                      ·
                        rfl

theorem cell23_7180602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 3, 2, 1, 1, 3].length) (baseStart_7180602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7180602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7180602 prefixEnd_7180602 := by exact prefixLift 7180602
  have htrace : WordTrace (prefixWord ++ tailWord_7180602) baseStart_7180602 baseEnd_7180602 := by
    simpa [prefixWord, tailWord_7180602, baseEnd_7180602] using wordTrace_append hprefix tailTrace_7180602
  have hstable : (prefixWord ++ tailWord_7180602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7180602).length < 2 ^ (prefixWord ++ tailWord_7180602).sum := by decide
  have hdescent : baseEnd_7180602 < baseStart_7180602 := by decide
  rcases family_descends (prefixWord ++ tailWord_7180602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7180604 : List Nat := [2, 2, 2, 2, 1, 2, 1, 1, 3, 1, 6]
def baseStart_7180604 : Nat := 118140960795 + 7180604 * 2 ^ 59
def prefixEnd_7180604 : Nat := 4983230072969 + 3 ^ 40 * 7180604 * 2
def baseEnd_7180604 : Nat := 3687101241597329087527009

theorem tailTrace_7180604 : CollatzResearch.WordTrace tailWord_7180604 prefixEnd_7180604 3687101241597329087527009 := by
  unfold tailWord_7180604
  simp only [CollatzResearch.WordTrace]
  refine ⟨130949071838952766186818433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174598762451937021582424577 130949071838952766186818433)
  ·
    refine ⟨98211803879214574640113825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130949071838952766186818433 98211803879214574640113825)
    ·
      refine ⟨73658852909410930980085369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98211803879214574640113825 73658852909410930980085369)
      ·
        refine ⟨55244139682058198235064027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73658852909410930980085369 55244139682058198235064027)
        ·
          refine ⟨82866209523087297352596041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55244139682058198235064027 82866209523087297352596041)
          ·
            refine ⟨62149657142315473014447031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82866209523087297352596041 62149657142315473014447031)
            ·
              refine ⟨93224485713473209521670547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62149657142315473014447031 93224485713473209521670547)
              ·
                refine ⟨139836728570209814282505821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93224485713473209521670547 139836728570209814282505821)
                ·
                  refine ⟨52438773213828680355939683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 139836728570209814282505821 52438773213828680355939683)
                  ·
                    refine ⟨78658159820743020533909525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52438773213828680355939683 78658159820743020533909525)
                    ·
                      refine ⟨3687101241597329087527009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78658159820743020533909525 3687101241597329087527009)
                      ·
                        rfl

theorem cell23_7180604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_7180604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7180604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7180604 prefixEnd_7180604 := by exact prefixLift 7180604
  have htrace : WordTrace (prefixWord ++ tailWord_7180604) baseStart_7180604 baseEnd_7180604 := by
    simpa [prefixWord, tailWord_7180604, baseEnd_7180604] using wordTrace_append hprefix tailTrace_7180604
  have hstable : (prefixWord ++ tailWord_7180604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7180604).length < 2 ^ (prefixWord ++ tailWord_7180604).sum := by decide
  have hdescent : baseEnd_7180604 < baseStart_7180604 := by decide
  rcases family_descends (prefixWord ++ tailWord_7180604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7180608 : List Nat := [2, 1, 1, 2, 2, 1, 2, 5, 3, 2, 2]
def baseStart_7180608 : Nat := 118140960795 + 7180608 * 2 ^ 59
def prefixEnd_7180608 : Nat := 4983230072969 + 3 ^ 40 * 7180608 * 2
def baseEnd_7180608 : Nat := 3687103295519947071876991

theorem tailTrace_7180608 : CollatzResearch.WordTrace tailWord_7180608 prefixEnd_7180608 3687103295519947071876991 := by
  unfold tailWord_7180608
  simp only [CollatzResearch.WordTrace]
  refine ⟨130949144784945520528391239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174598859713260694037854985 130949144784945520528391239)
  ·
    refine ⟨196423717177418280792586859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130949144784945520528391239 196423717177418280792586859)
    ·
      refine ⟨294635575766127421188880289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196423717177418280792586859 294635575766127421188880289)
      ·
        refine ⟨220976681824595565891660217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 294635575766127421188880289 220976681824595565891660217)
        ·
          refine ⟨165732511368446674418745163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220976681824595565891660217 165732511368446674418745163)
          ·
            refine ⟨248598767052670011628117745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165732511368446674418745163 248598767052670011628117745)
            ·
              refine ⟨186449075289502508721088309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 248598767052670011628117745 186449075289502508721088309)
              ·
                refine ⟨17479600808390860192602029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 186449075289502508721088309 17479600808390860192602029)
                ·
                  refine ⟨6554850303146572572225761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17479600808390860192602029 6554850303146572572225761)
                  ·
                    refine ⟨4916137727359929429169321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6554850303146572572225761 4916137727359929429169321)
                    ·
                      refine ⟨3687103295519947071876991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4916137727359929429169321 3687103295519947071876991)
                      ·
                        rfl

theorem cell23_7180608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 5, 3, 2, 2].length) (baseStart_7180608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7180608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7180608 prefixEnd_7180608 := by exact prefixLift 7180608
  have htrace : WordTrace (prefixWord ++ tailWord_7180608) baseStart_7180608 baseEnd_7180608 := by
    simpa [prefixWord, tailWord_7180608, baseEnd_7180608] using wordTrace_append hprefix tailTrace_7180608
  have hstable : (prefixWord ++ tailWord_7180608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7180608).length < 2 ^ (prefixWord ++ tailWord_7180608).sum := by decide
  have hdescent : baseEnd_7180608 < baseStart_7180608 := by decide
  rcases family_descends (prefixWord ++ tailWord_7180608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7180628 : List Nat := [2, 4, 1, 1, 2, 3, 1, 1, 3, 2, 3]
def baseStart_7180628 : Nat := 118140960795 + 7180628 * 2 ^ 59
def prefixEnd_7180628 : Nat := 4983230072969 + 3 ^ 40 * 7180628 * 2
def baseEnd_7180628 : Nat := 3687113565133036993626899

theorem tailTrace_7180628 : CollatzResearch.WordTrace tailWord_7180628 prefixEnd_7180628 3687113565133036993626899 := by
  unfold tailWord_7180628
  simp only [CollatzResearch.WordTrace]
  refine ⟨130949509514909292236255269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174599346019879056315007025 130949509514909292236255269)
  ·
    refine ⟨24553033034045492294297863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130949509514909292236255269 24553033034045492294297863)
    ·
      refine ⟨36829549551068238441446795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24553033034045492294297863 36829549551068238441446795)
      ·
        refine ⟨55244324326602357662170193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36829549551068238441446795 55244324326602357662170193)
        ·
          refine ⟨41433243244951768246627645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55244324326602357662170193 41433243244951768246627645)
          ·
            refine ⟨15537466216856913092485367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41433243244951768246627645 15537466216856913092485367)
            ·
              refine ⟨23306199325285369638728051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15537466216856913092485367 23306199325285369638728051)
              ·
                refine ⟨34959298987928054458092077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23306199325285369638728051 34959298987928054458092077)
                ·
                  refine ⟨13109737120473020421784529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34959298987928054458092077 13109737120473020421784529)
                  ·
                    refine ⟨9832302840354765316338397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13109737120473020421784529 9832302840354765316338397)
                    ·
                      refine ⟨3687113565133036993626899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9832302840354765316338397 3687113565133036993626899)
                      ·
                        rfl

theorem cell23_7180628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 1, 3, 2, 3].length) (baseStart_7180628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7180628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7180628 prefixEnd_7180628 := by exact prefixLift 7180628
  have htrace : WordTrace (prefixWord ++ tailWord_7180628) baseStart_7180628 baseEnd_7180628 := by
    simpa [prefixWord, tailWord_7180628, baseEnd_7180628] using wordTrace_append hprefix tailTrace_7180628
  have hstable : (prefixWord ++ tailWord_7180628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7180628).length < 2 ^ (prefixWord ++ tailWord_7180628).sum := by decide
  have hdescent : baseEnd_7180628 < baseStart_7180628 := by decide
  rcases family_descends (prefixWord ++ tailWord_7180628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7180645 : List Nat := [1, 3, 1, 3, 1, 4, 3, 1, 1, 2, 3]
def baseStart_7180645 : Nat := 118140960795 + 7180645 * 2 ^ 59
def prefixEnd_7180645 : Nat := 4983230072969 + 3 ^ 40 * 7180645 * 2
def baseEnd_7180645 : Nat := 3687122294304163427114321

theorem tailTrace_7180645 : CollatzResearch.WordTrace tailWord_7180645 prefixEnd_7180645 3687122294304163427114321 := by
  unfold tailWord_7180645
  simp only [CollatzResearch.WordTrace]
  refine ⟨261899639070756996375879389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174599759380504664250586259 261899639070756996375879389)
  ·
    refine ⟨98212364651533873640954771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261899639070756996375879389 98212364651533873640954771)
    ·
      refine ⟨147318546977300810461432157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98212364651533873640954771 147318546977300810461432157)
      ·
        refine ⟨55244455116487803923037059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147318546977300810461432157 55244455116487803923037059)
        ·
          refine ⟨82866682674731705884555589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55244455116487803923037059 82866682674731705884555589)
          ·
            refine ⟨15537503001512194853354173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82866682674731705884555589 15537503001512194853354173)
            ·
              refine ⟨5826563625567073070007815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15537503001512194853354173 5826563625567073070007815)
              ·
                refine ⟨8739845438350609605011723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5826563625567073070007815 8739845438350609605011723)
                ·
                  refine ⟨13109768157525914407517585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8739845438350609605011723 13109768157525914407517585)
                  ·
                    refine ⟨9832326118144435805638189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13109768157525914407517585 9832326118144435805638189)
                    ·
                      refine ⟨3687122294304163427114321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9832326118144435805638189 3687122294304163427114321)
                      ·
                        rfl

theorem cell23_7180645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 3, 1, 1, 2, 3].length) (baseStart_7180645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7180645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7180645 prefixEnd_7180645 := by exact prefixLift 7180645
  have htrace : WordTrace (prefixWord ++ tailWord_7180645) baseStart_7180645 baseEnd_7180645 := by
    simpa [prefixWord, tailWord_7180645, baseEnd_7180645] using wordTrace_append hprefix tailTrace_7180645
  have hstable : (prefixWord ++ tailWord_7180645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7180645).length < 2 ^ (prefixWord ++ tailWord_7180645).sum := by decide
  have hdescent : baseEnd_7180645 < baseStart_7180645 := by decide
  rcases family_descends (prefixWord ++ tailWord_7180645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7180661 : List Nat := [1, 3, 4, 1, 2, 1, 1, 1, 2, 7]
def baseStart_7180661 : Nat := 118140960795 + 7180661 * 2 ^ 59
def prefixEnd_7180661 : Nat := 4983230072969 + 3 ^ 40 * 7180661 * 2
def baseEnd_7180661 : Nat := 1229043503331545121504749

theorem tailTrace_7180661 : CollatzResearch.WordTrace tailWord_7180661 prefixEnd_7180661 1229043503331545121504749 := by
  unfold tailWord_7180661
  simp only [CollatzResearch.WordTrace]
  refine ⟨261900222638699031108461837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174600148425799354072307891 261900222638699031108461837)
  ·
    refine ⟨98212583489512136665673189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261900222638699031108461837 98212583489512136665673189)
    ·
      refine ⟨18414859404283525624813723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98212583489512136665673189 18414859404283525624813723)
      ·
        refine ⟨27622289106425288437220585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18414859404283525624813723 27622289106425288437220585)
        ·
          refine ⟨20716716829818966327915439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27622289106425288437220585 20716716829818966327915439)
          ·
            refine ⟨31075075244728449491873159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20716716829818966327915439 31075075244728449491873159)
            ·
              refine ⟨46612612867092674237809739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31075075244728449491873159 46612612867092674237809739)
              ·
                refine ⟨69918919300639011356714609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46612612867092674237809739 69918919300639011356714609)
                ·
                  refine ⟨52439189475479258517535957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69918919300639011356714609 52439189475479258517535957)
                  ·
                    refine ⟨1229043503331545121504749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52439189475479258517535957 1229043503331545121504749)
                    ·
                      rfl

theorem cell23_7180661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_7180661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7180661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7180661 prefixEnd_7180661 := by exact prefixLift 7180661
  have htrace : WordTrace (prefixWord ++ tailWord_7180661) baseStart_7180661 baseEnd_7180661 := by
    simpa [prefixWord, tailWord_7180661, baseEnd_7180661] using wordTrace_append hprefix tailTrace_7180661
  have hstable : (prefixWord ++ tailWord_7180661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7180661).length < 2 ^ (prefixWord ++ tailWord_7180661).sum := by decide
  have hdescent : baseEnd_7180661 < baseStart_7180661 := by decide
  rcases family_descends (prefixWord ++ tailWord_7180661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7180721 : List Nat := [1, 2, 2, 4, 1, 2, 1, 3, 7]
def baseStart_7180721 : Nat := 118140960795 + 7180721 * 2 ^ 59
def prefixEnd_7180721 : Nat := 4983230072969 + 3 ^ 40 * 7180721 * 2
def baseEnd_7180721 : Nat := 409684590981545014418219

theorem tailTrace_7180721 : CollatzResearch.WordTrace tailWord_7180721 prefixEnd_7180721 409684590981545014418219 := by
  unfold tailWord_7180721
  simp only [CollatzResearch.WordTrace]
  refine ⟨261902411018481661355646017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174601607345654440903764011 261902411018481661355646017)
  ·
    refine ⟨196426808263861246016734513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261902411018481661355646017 196426808263861246016734513)
    ·
      refine ⟨147320106197895934512550885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196426808263861246016734513 147320106197895934512550885)
      ·
        refine ⟨27622519912105487721103291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 147320106197895934512550885 27622519912105487721103291)
        ·
          refine ⟨41433779868158231581654937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27622519912105487721103291 41433779868158231581654937)
          ·
            refine ⟨31075334901118673686241203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41433779868158231581654937 31075334901118673686241203)
            ·
              refine ⟨46613002351678010529361805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31075334901118673686241203 46613002351678010529361805)
              ·
                refine ⟨17479875881879253948510677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46613002351678010529361805 17479875881879253948510677)
                ·
                  refine ⟨409684590981545014418219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17479875881879253948510677 409684590981545014418219)
                  ·
                    rfl

theorem cell23_7180721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 3, 7].length) (baseStart_7180721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7180721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7180721 prefixEnd_7180721 := by exact prefixLift 7180721
  have htrace : WordTrace (prefixWord ++ tailWord_7180721) baseStart_7180721 baseEnd_7180721 := by
    simpa [prefixWord, tailWord_7180721, baseEnd_7180721] using wordTrace_append hprefix tailTrace_7180721
  have hstable : (prefixWord ++ tailWord_7180721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7180721).length < 2 ^ (prefixWord ++ tailWord_7180721).sum := by decide
  have hdescent : baseEnd_7180721 < baseStart_7180721 := by decide
  rcases family_descends (prefixWord ++ tailWord_7180721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7180732 : List Nat := [2, 2, 2, 4, 1, 3, 1, 1, 1, 4, 2]
def baseStart_7180732 : Nat := 118140960795 + 7180732 * 2 ^ 59
def prefixEnd_7180732 : Nat := 4983230072969 + 3 ^ 40 * 7180732 * 2
def baseEnd_7180732 : Nat := 3687166967121104586726421

theorem tailTrace_7180732 : CollatzResearch.WordTrace tailWord_7180732 prefixEnd_7180732 3687166967121104586726421 := by
  unfold tailWord_7180732
  simp only [CollatzResearch.WordTrace]
  refine ⟨130951406110720905117148225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174601874814294540156197633 130951406110720905117148225)
  ·
    refine ⟨98213554583040678837861169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130951406110720905117148225 98213554583040678837861169)
    ·
      refine ⟨73660165937280509128395877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98213554583040678837861169 73660165937280509128395877)
      ·
        refine ⟨13811281113240095461574227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73660165937280509128395877 13811281113240095461574227)
        ·
          refine ⟨20716921669860143192361341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13811281113240095461574227 20716921669860143192361341)
          ·
            refine ⟨7768845626197553697135503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20716921669860143192361341 7768845626197553697135503)
            ·
              refine ⟨11653268439296330545703255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7768845626197553697135503 11653268439296330545703255)
              ·
                refine ⟨17479902658944495818554883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11653268439296330545703255 17479902658944495818554883)
                ·
                  refine ⟨26219853988416743727832325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17479902658944495818554883 26219853988416743727832325)
                  ·
                    refine ⟨4916222622828139448968561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26219853988416743727832325 4916222622828139448968561)
                    ·
                      refine ⟨3687166967121104586726421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4916222622828139448968561 3687166967121104586726421)
                      ·
                        rfl

theorem cell23_7180732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_7180732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7180732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7180732 prefixEnd_7180732 := by exact prefixLift 7180732
  have htrace : WordTrace (prefixWord ++ tailWord_7180732) baseStart_7180732 baseEnd_7180732 := by
    simpa [prefixWord, tailWord_7180732, baseEnd_7180732] using wordTrace_append hprefix tailTrace_7180732
  have hstable : (prefixWord ++ tailWord_7180732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7180732).length < 2 ^ (prefixWord ++ tailWord_7180732).sum := by decide
  have hdescent : baseEnd_7180732 < baseStart_7180732 := by decide
  rcases family_descends (prefixWord ++ tailWord_7180732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7180751 : List Nat := [1, 1, 2, 1, 1, 4, 1, 5, 2, 5]
def baseStart_7180751 : Nat := 118140960795 + 7180751 * 2 ^ 59
def prefixEnd_7180751 : Nat := 4983230072969 + 3 ^ 40 * 7180751 * 2
def baseEnd_7180751 : Nat := 1229058907751180004129611

theorem tailTrace_7180751 : CollatzResearch.WordTrace tailWord_7180751 prefixEnd_7180751 1229058907751180004129611 := by
  unfold tailWord_7180751
  simp only [CollatzResearch.WordTrace]
  refine ⟨261903505208372976479238107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174602336805581984319492071 261903505208372976479238107)
  ·
    refine ⟨392855257812559464718857161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261903505208372976479238107 392855257812559464718857161)
    ·
      refine ⟨294641443359419598539142871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 392855257812559464718857161 294641443359419598539142871)
      ·
        refine ⟨441962165039129397808714307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294641443359419598539142871 441962165039129397808714307)
        ·
          refine ⟨662943247558694096713071461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 441962165039129397808714307 662943247558694096713071461)
          ·
            refine ⟨124301858917255143133700899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 662943247558694096713071461 124301858917255143133700899)
            ·
              refine ⟨186452788375882714700551349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124301858917255143133700899 186452788375882714700551349)
              ·
                refine ⟨17479948910239004503176689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 186452788375882714700551349 17479948910239004503176689)
                ·
                  refine ⟨13109961682679253377382517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17479948910239004503176689 13109961682679253377382517)
                  ·
                    refine ⟨1229058907751180004129611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13109961682679253377382517 1229058907751180004129611)
                    ·
                      rfl

theorem cell23_7180751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 5, 2, 5].length) (baseStart_7180751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7180751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7180751 prefixEnd_7180751 := by exact prefixLift 7180751
  have htrace : WordTrace (prefixWord ++ tailWord_7180751) baseStart_7180751 baseEnd_7180751 := by
    simpa [prefixWord, tailWord_7180751, baseEnd_7180751] using wordTrace_append hprefix tailTrace_7180751
  have hstable : (prefixWord ++ tailWord_7180751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7180751).length < 2 ^ (prefixWord ++ tailWord_7180751).sum := by decide
  have hdescent : baseEnd_7180751 < baseStart_7180751 := by decide
  rcases family_descends (prefixWord ++ tailWord_7180751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7180761 : List Nat := [1, 2, 1, 2, 4, 1, 2, 2, 1, 2, 5]
def baseStart_7180761 : Nat := 118140960795 + 7180761 * 2 ^ 59
def prefixEnd_7180761 : Nat := 4983230072969 + 3 ^ 40 * 7180761 * 2
def baseEnd_7180761 : Nat := 3687181858060084973263787

theorem tailTrace_7180761 : CollatzResearch.WordTrace tailWord_7180761 prefixEnd_7180761 3687181858060084973263787 := by
  unfold tailWord_7180761
  simp only [CollatzResearch.WordTrace]
  refine ⟨261903869938336748187102137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174602579958891165458068091 261903869938336748187102137)
  ·
    refine ⟨196427902453752561140326603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261903869938336748187102137 196427902453752561140326603)
    ·
      refine ⟨294641853680628841710489905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196427902453752561140326603 294641853680628841710489905)
      ·
        refine ⟨220981390260471631282867429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 294641853680628841710489905 220981390260471631282867429)
        ·
          refine ⟨41434010673838430865537643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 220981390260471631282867429 41434010673838430865537643)
          ·
            refine ⟨62151016010757646298306465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41434010673838430865537643 62151016010757646298306465)
            ·
              refine ⟨46613262008068234723729849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62151016010757646298306465 46613262008068234723729849)
              ·
                refine ⟨34959946506051176042797387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46613262008068234723729849 34959946506051176042797387)
                ·
                  refine ⟨52439919759076764064196081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34959946506051176042797387 52439919759076764064196081)
                  ·
                    refine ⟨39329939819307573048147061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52439919759076764064196081 39329939819307573048147061)
                    ·
                      refine ⟨3687181858060084973263787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39329939819307573048147061 3687181858060084973263787)
                      ·
                        rfl

theorem cell23_7180761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 2, 1, 2, 5].length) (baseStart_7180761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7180761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7180761 prefixEnd_7180761 := by exact prefixLift 7180761
  have htrace : WordTrace (prefixWord ++ tailWord_7180761) baseStart_7180761 baseEnd_7180761 := by
    simpa [prefixWord, tailWord_7180761, baseEnd_7180761] using wordTrace_append hprefix tailTrace_7180761
  have hstable : (prefixWord ++ tailWord_7180761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7180761).length < 2 ^ (prefixWord ++ tailWord_7180761).sum := by decide
  have hdescent : baseEnd_7180761 < baseStart_7180761 := by decide
  rcases family_descends (prefixWord ++ tailWord_7180761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7180778 : List Nat := [3, 1, 3, 1, 3, 2, 1, 1, 1, 2, 5]
def baseStart_7180778 : Nat := 118140960795 + 7180778 * 2 ^ 59
def prefixEnd_7180778 : Nat := 4983230072969 + 3 ^ 40 * 7180778 * 2
def baseEnd_7180778 : Nat := 3687190587231211406751209

theorem tailTrace_7180778 : CollatzResearch.WordTrace tailWord_7180778 prefixEnd_7180778 3687190587231211406751209 := by
  unfold tailWord_7180778
  simp only [CollatzResearch.WordTrace]
  refine ⟨65476122494818790022617747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174602993319516773393647325 65476122494818790022617747)
  ·
    refine ⟨98214183742228185033926621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65476122494818790022617747 98214183742228185033926621)
    ·
      refine ⟨36830318903335569387722483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98214183742228185033926621 36830318903335569387722483)
      ·
        refine ⟨55245478355003354081583725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36830318903335569387722483 55245478355003354081583725)
        ·
          refine ⟨20717054383126257780593897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55245478355003354081583725 20717054383126257780593897)
          ·
            refine ⟨15537790787344693335445423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20717054383126257780593897 15537790787344693335445423)
            ·
              refine ⟨23306686181017040003168135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15537790787344693335445423 23306686181017040003168135)
              ·
                refine ⟨34960029271525560004752203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23306686181017040003168135 34960029271525560004752203)
                ·
                  refine ⟨52440043907288340007128305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34960029271525560004752203 52440043907288340007128305)
                  ·
                    refine ⟨39330032930466255005346229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52440043907288340007128305 39330032930466255005346229)
                    ·
                      refine ⟨3687190587231211406751209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39330032930466255005346229 3687190587231211406751209)
                      ·
                        rfl

theorem cell23_7180778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_7180778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7180778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7180778 prefixEnd_7180778 := by exact prefixLift 7180778
  have htrace : WordTrace (prefixWord ++ tailWord_7180778) baseStart_7180778 baseEnd_7180778 := by
    simpa [prefixWord, tailWord_7180778, baseEnd_7180778] using wordTrace_append hprefix tailTrace_7180778
  have hstable : (prefixWord ++ tailWord_7180778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7180778).length < 2 ^ (prefixWord ++ tailWord_7180778).sum := by decide
  have hdescent : baseEnd_7180778 < baseStart_7180778 := by decide
  rcases family_descends (prefixWord ++ tailWord_7180778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7180802 : List Nat := [3, 4, 1, 2, 2, 1, 2, 1, 2, 5]
def baseStart_7180802 : Nat := 118140960795 + 7180802 * 2 ^ 59
def prefixEnd_7180802 : Nat := 4983230072969 + 3 ^ 40 * 7180802 * 2
def baseEnd_7180802 : Nat := 1229067636922306437617033

theorem tailTrace_7180802 : CollatzResearch.WordTrace tailWord_7180802 prefixEnd_7180802 1229067636922306437617033 := by
  unfold tailWord_7180802
  simp only [CollatzResearch.WordTrace]
  refine ⟨65476341332797053047336165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174603576887458808126229773 65476341332797053047336165)
  ·
    refine ⟨12276813999899447446375531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65476341332797053047336165 12276813999899447446375531)
    ·
      refine ⟨18415220999849171169563297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12276813999899447446375531 18415220999849171169563297)
      ·
        refine ⟨13811415749886878377172473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18415220999849171169563297 13811415749886878377172473)
        ·
          refine ⟨10358561812415158782879355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13811415749886878377172473 10358561812415158782879355)
          ·
            refine ⟨15537842718622738174319033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10358561812415158782879355 15537842718622738174319033)
            ·
              refine ⟨11653382038967053630739275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15537842718622738174319033 11653382038967053630739275)
              ·
                refine ⟨17480073058450580446108913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11653382038967053630739275 17480073058450580446108913)
                ·
                  refine ⟨13110054793837935334581685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17480073058450580446108913 13110054793837935334581685)
                  ·
                    refine ⟨1229067636922306437617033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13110054793837935334581685 1229067636922306437617033)
                    ·
                      rfl

theorem cell23_7180802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_7180802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7180802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7180802 prefixEnd_7180802 := by exact prefixLift 7180802
  have htrace : WordTrace (prefixWord ++ tailWord_7180802) baseStart_7180802 baseEnd_7180802 := by
    simpa [prefixWord, tailWord_7180802, baseEnd_7180802] using wordTrace_append hprefix tailTrace_7180802
  have hstable : (prefixWord ++ tailWord_7180802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7180802).length < 2 ^ (prefixWord ++ tailWord_7180802).sum := by decide
  have hdescent : baseEnd_7180802 < baseStart_7180802 := by decide
  rcases family_descends (prefixWord ++ tailWord_7180802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7180828 : List Nat := [2, 2, 3, 1, 2, 2, 1, 4, 6]
def baseStart_7180828 : Nat := 118140960795 + 7180828 * 2 ^ 59
def prefixEnd_7180828 : Nat := 4983230072969 + 3 ^ 40 * 7180828 * 2
def baseEnd_7180828 : Nat := 409690695695992912347331

theorem tailTrace_7180828 : CollatzResearch.WordTrace tailWord_7180828 prefixEnd_7180828 409690695695992912347331 := by
  unfold tailWord_7180828
  simp only [CollatzResearch.WordTrace]
  refine ⟨130953156814547009314895569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174604209086062679086527425 130953156814547009314895569)
  ·
    refine ⟨98214867610910256986171677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130953156814547009314895569 98214867610910256986171677)
    ·
      refine ⟨36830575354091346369814379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98214867610910256986171677 36830575354091346369814379)
      ·
        refine ⟨55245863031137019554721569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36830575354091346369814379 55245863031137019554721569)
        ·
          refine ⟨41434397273352764666041177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55245863031137019554721569 41434397273352764666041177)
          ·
            refine ⟨31075797955014573499530883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41434397273352764666041177 31075797955014573499530883)
            ·
              refine ⟨46613696932521860249296325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31075797955014573499530883 46613696932521860249296325)
              ·
                refine ⟨8740068174847848796743061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46613696932521860249296325 8740068174847848796743061)
                ·
                  refine ⟨409690695695992912347331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8740068174847848796743061 409690695695992912347331)
                  ·
                    rfl

theorem cell23_7180828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 4, 6].length) (baseStart_7180828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7180828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7180828 prefixEnd_7180828 := by exact prefixLift 7180828
  have htrace : WordTrace (prefixWord ++ tailWord_7180828) baseStart_7180828 baseEnd_7180828 := by
    simpa [prefixWord, tailWord_7180828, baseEnd_7180828] using wordTrace_append hprefix tailTrace_7180828
  have hstable : (prefixWord ++ tailWord_7180828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7180828).length < 2 ^ (prefixWord ++ tailWord_7180828).sum := by decide
  have hdescent : baseEnd_7180828 < baseStart_7180828 := by decide
  rcases family_descends (prefixWord ++ tailWord_7180828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7180831 : List Nat := [1, 1, 2, 4, 1, 1, 1, 3, 1, 2, 6]
def baseStart_7180831 : Nat := 118140960795 + 7180831 * 2 ^ 59
def prefixEnd_7180831 : Nat := 4983230072969 + 3 ^ 40 * 7180831 * 2
def baseEnd_7180831 : Nat := 3687217801705899699388465

theorem tailTrace_7180831 : CollatzResearch.WordTrace tailWord_7180831 prefixEnd_7180831 3687217801705899699388465 := by
  unfold tailWord_7180831
  simp only [CollatzResearch.WordTrace]
  refine ⟨261906423048083150142150347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174604282032055433428100231 261906423048083150142150347)
  ·
    refine ⟨392859634572124725213225521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261906423048083150142150347 392859634572124725213225521)
    ·
      refine ⟨294644725929093543909919141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 392859634572124725213225521 294644725929093543909919141)
      ·
        refine ⟨55245886111705039483109839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 294644725929093543909919141 55245886111705039483109839)
        ·
          refine ⟨82868829167557559224664759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55245886111705039483109839 82868829167557559224664759)
          ·
            refine ⟨124303243751336338836997139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82868829167557559224664759 124303243751336338836997139)
            ·
              refine ⟨186454865627004508255495709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124303243751336338836997139 186454865627004508255495709)
              ·
                refine ⟨69920574610126690595810891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 186454865627004508255495709 69920574610126690595810891)
                ·
                  refine ⟨104880861915190035893716337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69920574610126690595810891 104880861915190035893716337)
                  ·
                    refine ⟨78660646436392526920287253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 104880861915190035893716337 78660646436392526920287253)
                    ·
                      refine ⟨3687217801705899699388465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78660646436392526920287253 3687217801705899699388465)
                      ·
                        rfl

theorem cell23_7180831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_7180831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7180831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7180831 prefixEnd_7180831 := by exact prefixLift 7180831
  have htrace : WordTrace (prefixWord ++ tailWord_7180831) baseStart_7180831 baseEnd_7180831 := by
    simpa [prefixWord, tailWord_7180831, baseEnd_7180831] using wordTrace_append hprefix tailTrace_7180831
  have hstable : (prefixWord ++ tailWord_7180831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7180831).length < 2 ^ (prefixWord ++ tailWord_7180831).sum := by decide
  have hdescent : baseEnd_7180831 < baseStart_7180831 := by decide
  rcases family_descends (prefixWord ++ tailWord_7180831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7180839 : List Nat := [1, 1, 7, 2, 1, 1, 1, 1, 2, 4, 2]
def baseStart_7180839 : Nat := 118140960795 + 7180839 * 2 ^ 59
def prefixEnd_7180839 : Nat := 4983230072969 + 3 ^ 40 * 7180839 * 2
def baseEnd_7180839 : Nat := 3687221909551135668088429

theorem tailTrace_7180839 : CollatzResearch.WordTrace tailWord_7180839 prefixEnd_7180839 3687221909551135668088429 := by
  unfold tailWord_7180839
  simp only [CollatzResearch.WordTrace]
  refine ⟨261906714832054167508441571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174604476554702778338961047 261906714832054167508441571)
  ·
    refine ⟨392860072248081251262662357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261906714832054167508441571 392860072248081251262662357)
    ·
      refine ⟨9207657943314404326468649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 392860072248081251262662357 9207657943314404326468649)
      ·
        refine ⟨6905743457485803244851487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9207657943314404326468649 6905743457485803244851487)
        ·
          refine ⟨10358615186228704867277231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6905743457485803244851487 10358615186228704867277231)
          ·
            refine ⟨15537922779343057300915847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10358615186228704867277231 15537922779343057300915847)
            ·
              refine ⟨23306884169014585951373771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15537922779343057300915847 23306884169014585951373771)
              ·
                refine ⟨34960326253521878927060657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23306884169014585951373771 34960326253521878927060657)
                ·
                  refine ⟨26220244690141409195295493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34960326253521878927060657 26220244690141409195295493)
                  ·
                    refine ⟨4916295879401514224117905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26220244690141409195295493 4916295879401514224117905)
                    ·
                      refine ⟨3687221909551135668088429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4916295879401514224117905 3687221909551135668088429)
                      ·
                        rfl

theorem cell23_7180839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_7180839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7180839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7180839 prefixEnd_7180839 := by exact prefixLift 7180839
  have htrace : WordTrace (prefixWord ++ tailWord_7180839) baseStart_7180839 baseEnd_7180839 := by
    simpa [prefixWord, tailWord_7180839, baseEnd_7180839] using wordTrace_append hprefix tailTrace_7180839
  have hstable : (prefixWord ++ tailWord_7180839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7180839).length < 2 ^ (prefixWord ++ tailWord_7180839).sum := by decide
  have hdescent : baseEnd_7180839 < baseStart_7180839 := by decide
  rcases family_descends (prefixWord ++ tailWord_7180839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7180851 : List Nat := [1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 7]
def baseStart_7180851 : Nat := 118140960795 + 7180851 * 2 ^ 59
def prefixEnd_7180851 : Nat := 4983230072969 + 3 ^ 40 * 7180851 * 2
def baseEnd_7180851 : Nat := 3687228071318989621138373

theorem tailTrace_7180851 : CollatzResearch.WordTrace tailWord_7180851 prefixEnd_7180851 3687228071318989621138373 := by
  unfold tailWord_7180851
  simp only [CollatzResearch.WordTrace]
  refine ⟨261907152508010693557878407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174604768338673795705252271 261907152508010693557878407)
  ·
    refine ⟨392860728762016040336817611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261907152508010693557878407 392860728762016040336817611)
    ·
      refine ⟨589291093143024060505226417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392860728762016040336817611 589291093143024060505226417)
      ·
        refine ⟨441968319857268045378919813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 589291093143024060505226417 441968319857268045378919813)
        ·
          refine ⟨82869059973237758508547465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 441968319857268045378919813 82869059973237758508547465)
          ·
            refine ⟨62151794979928318881410599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82869059973237758508547465 62151794979928318881410599)
            ·
              refine ⟨93227692469892478322115899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62151794979928318881410599 93227692469892478322115899)
              ·
                refine ⟨139841538704838717483173849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93227692469892478322115899 139841538704838717483173849)
                ·
                  refine ⟨104881154028629038112380387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139841538704838717483173849 104881154028629038112380387)
                  ·
                    refine ⟨157321731042943557168570581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 104881154028629038112380387 157321731042943557168570581)
                    ·
                      refine ⟨3687228071318989621138373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 157321731042943557168570581 3687228071318989621138373)
                      ·
                        rfl

theorem cell23_7180851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 7].length) (baseStart_7180851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7180851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7180851 prefixEnd_7180851 := by exact prefixLift 7180851
  have htrace : WordTrace (prefixWord ++ tailWord_7180851) baseStart_7180851 baseEnd_7180851 := by
    simpa [prefixWord, tailWord_7180851, baseEnd_7180851] using wordTrace_append hprefix tailTrace_7180851
  have hstable : (prefixWord ++ tailWord_7180851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7180851).length < 2 ^ (prefixWord ++ tailWord_7180851).sum := by decide
  have hdescent : baseEnd_7180851 < baseStart_7180851 := by decide
  rcases family_descends (prefixWord ++ tailWord_7180851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7180855 : List Nat := [1, 1, 3, 1, 2, 3, 3, 2, 3, 1, 3]
def baseStart_7180855 : Nat := 118140960795 + 7180855 * 2 ^ 59
def prefixEnd_7180855 : Nat := 4983230072969 + 3 ^ 40 * 7180855 * 2
def baseEnd_7180855 : Nat := 3687230125241607605488355

theorem tailTrace_7180855 : CollatzResearch.WordTrace tailWord_7180855 prefixEnd_7180855 3687230125241607605488355 := by
  unfold tailWord_7180855
  simp only [CollatzResearch.WordTrace]
  refine ⟨261907298399996202241024019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174604865599997468160682679 261907298399996202241024019)
  ·
    refine ⟨392860947599994303361536029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261907298399996202241024019 392860947599994303361536029)
    ·
      refine ⟨147322855349997863760576011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 392860947599994303361536029 147322855349997863760576011)
      ·
        refine ⟨220984283024996795640864017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147322855349997863760576011 220984283024996795640864017)
        ·
          refine ⟨165738212268747596730648013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220984283024996795640864017 165738212268747596730648013)
          ·
            refine ⟨62151829600780348773993005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165738212268747596730648013 62151829600780348773993005)
            ·
              refine ⟨23306936100292630790247377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62151829600780348773993005 23306936100292630790247377)
              ·
                refine ⟨17480202075219473092685533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23306936100292630790247377 17480202075219473092685533)
                ·
                  refine ⟨6555075778207302409757075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17480202075219473092685533 6555075778207302409757075)
                  ·
                    refine ⟨9832613667310953614635613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6555075778207302409757075 9832613667310953614635613)
                    ·
                      refine ⟨3687230125241607605488355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9832613667310953614635613 3687230125241607605488355)
                      ·
                        rfl

theorem cell23_7180855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 2, 3, 1, 3].length) (baseStart_7180855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7180855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7180855 prefixEnd_7180855 := by exact prefixLift 7180855
  have htrace : WordTrace (prefixWord ++ tailWord_7180855) baseStart_7180855 baseEnd_7180855 := by
    simpa [prefixWord, tailWord_7180855, baseEnd_7180855] using wordTrace_append hprefix tailTrace_7180855
  have hstable : (prefixWord ++ tailWord_7180855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7180855).length < 2 ^ (prefixWord ++ tailWord_7180855).sum := by decide
  have hdescent : baseEnd_7180855 < baseStart_7180855 := by decide
  rcases family_descends (prefixWord ++ tailWord_7180855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7180858 : List Nat := [3, 1, 1, 1, 3, 3, 2, 1, 3, 5]
def baseStart_7180858 : Nat := 118140960795 + 7180858 * 2 ^ 59
def prefixEnd_7180858 : Nat := 4983230072969 + 3 ^ 40 * 7180858 * 2
def baseEnd_7180858 : Nat := 1229077221894523697916947

theorem tailTrace_7180858 : CollatzResearch.WordTrace tailWord_7180858 prefixEnd_7180858 1229077221894523697916947 := by
  unfold tailWord_7180858
  simp only [CollatzResearch.WordTrace]
  refine ⟨65476851954746333438345807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174604938545990222502255485 65476851954746333438345807)
  ·
    refine ⟨98215277932119500157518711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65476851954746333438345807 98215277932119500157518711)
    ·
      refine ⟨147322916898179250236278067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98215277932119500157518711 147322916898179250236278067)
      ·
        refine ⟨220984375347268875354417101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147322916898179250236278067 220984375347268875354417101)
        ·
          refine ⟨82869140755225828257906413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 220984375347268875354417101 82869140755225828257906413)
          ·
            refine ⟨31075927783209685596714905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82869140755225828257906413 31075927783209685596714905)
            ·
              refine ⟨23306945837407264197536179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31075927783209685596714905 23306945837407264197536179)
              ·
                refine ⟨34960418756110896296304269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23306945837407264197536179 34960418756110896296304269)
                ·
                  refine ⟨13110157033541586111114101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34960418756110896296304269 13110157033541586111114101)
                  ·
                    refine ⟨1229077221894523697916947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13110157033541586111114101 1229077221894523697916947)
                    ·
                      rfl

theorem cell23_7180858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 1, 3, 5].length) (baseStart_7180858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7180858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7180858 prefixEnd_7180858 := by exact prefixLift 7180858
  have htrace : WordTrace (prefixWord ++ tailWord_7180858) baseStart_7180858 baseEnd_7180858 := by
    simpa [prefixWord, tailWord_7180858, baseEnd_7180858] using wordTrace_append hprefix tailTrace_7180858
  have hstable : (prefixWord ++ tailWord_7180858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7180858).length < 2 ^ (prefixWord ++ tailWord_7180858).sum := by decide
  have hdescent : baseEnd_7180858 < baseStart_7180858 := by decide
  rcases family_descends (prefixWord ++ tailWord_7180858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7180875 : List Nat := [1, 1, 1, 1, 3, 1, 8, 1, 1, 5]
def baseStart_7180875 : Nat := 118140960795 + 7180875 * 2 ^ 59
def prefixEnd_7180875 : Nat := 4983230072969 + 3 ^ 40 * 7180875 * 2
def baseEnd_7180875 : Nat := 1229080131618232509079421

theorem tailTrace_7180875 : CollatzResearch.WordTrace tailWord_7180875 prefixEnd_7180875 1229080131618232509079421 := by
  unfold tailWord_7180875
  simp only [CollatzResearch.WordTrace]
  refine ⟨261908027859923745656752079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174605351906615830437834719 261908027859923745656752079)
  ·
    refine ⟨392862041789885618485128119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261908027859923745656752079 392862041789885618485128119)
    ·
      refine ⟨589293062684828427727692179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392862041789885618485128119 589293062684828427727692179)
      ·
        refine ⟨883939594027242641591538269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 589293062684828427727692179 883939594027242641591538269)
        ·
          refine ⟨331477347760215990596826851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 883939594027242641591538269 331477347760215990596826851)
          ·
            refine ⟨497216021640323985895240277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 331477347760215990596826851 497216021640323985895240277)
            ·
              refine ⟨5826750253597546709709847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 497216021640323985895240277 5826750253597546709709847)
              ·
                refine ⟨8740125380396320064564771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5826750253597546709709847 8740125380396320064564771)
                ·
                  refine ⟨13110188070594480096847157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8740125380396320064564771 13110188070594480096847157)
                  ·
                    refine ⟨1229080131618232509079421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13110188070594480096847157 1229080131618232509079421)
                    ·
                      rfl

theorem cell23_7180875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 8, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 8, 1, 1, 5].length) (baseStart_7180875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7180875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7180875 prefixEnd_7180875 := by exact prefixLift 7180875
  have htrace : WordTrace (prefixWord ++ tailWord_7180875) baseStart_7180875 baseEnd_7180875 := by
    simpa [prefixWord, tailWord_7180875, baseEnd_7180875] using wordTrace_append hprefix tailTrace_7180875
  have hstable : (prefixWord ++ tailWord_7180875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7180875).length < 2 ^ (prefixWord ++ tailWord_7180875).sum := by decide
  have hdescent : baseEnd_7180875 < baseStart_7180875 := by decide
  rcases family_descends (prefixWord ++ tailWord_7180875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7180912 : List Nat := [2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 4]
def baseStart_7180912 : Nat := 118140960795 + 7180912 * 2 ^ 59
def prefixEnd_7180912 : Nat := 4983230072969 + 3 ^ 40 * 7180912 * 2
def baseEnd_7180912 : Nat := 3687259393638913882475593

theorem tailTrace_7180912 : CollatzResearch.WordTrace tailWord_7180912 prefixEnd_7180912 3687259393638913882475593 := by
  unfold tailWord_7180912
  simp only [CollatzResearch.WordTrace]
  refine ⟨130954688680394850487924495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174606251573859800650565993 130954688680394850487924495)
  ·
    refine ⟨196432033020592275731886743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130954688680394850487924495 196432033020592275731886743)
    ·
      refine ⟨294648049530888413597830115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196432033020592275731886743 294648049530888413597830115)
      ·
        refine ⟨441972074296332620396745173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294648049530888413597830115 441972074296332620396745173)
        ·
          refine ⟨10358720491320295790548715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 441972074296332620396745173 10358720491320295790548715)
          ·
            refine ⟨15538080736980443685823073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10358720491320295790548715 15538080736980443685823073)
            ·
              refine ⟨11653560552735332764367305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15538080736980443685823073 11653560552735332764367305)
              ·
                refine ⟨8740170414551499573275479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11653560552735332764367305 8740170414551499573275479)
                ·
                  refine ⟨13110255621827249359913219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8740170414551499573275479 13110255621827249359913219)
                  ·
                    refine ⟨19665383432740874039869829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13110255621827249359913219 19665383432740874039869829)
                    ·
                      refine ⟨3687259393638913882475593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19665383432740874039869829 3687259393638913882475593)
                      ·
                        rfl

theorem cell23_7180912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 4].length) (baseStart_7180912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7180912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7180912 prefixEnd_7180912 := by exact prefixLift 7180912
  have htrace : WordTrace (prefixWord ++ tailWord_7180912) baseStart_7180912 baseEnd_7180912 := by
    simpa [prefixWord, tailWord_7180912, baseEnd_7180912] using wordTrace_append hprefix tailTrace_7180912
  have hstable : (prefixWord ++ tailWord_7180912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7180912).length < 2 ^ (prefixWord ++ tailWord_7180912).sum := by decide
  have hdescent : baseEnd_7180912 < baseStart_7180912 := by decide
  rcases family_descends (prefixWord ++ tailWord_7180912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7180932 : List Nat := [2, 3, 2, 1, 3, 1, 2, 3, 1, 2, 3]
def baseStart_7180932 : Nat := 118140960795 + 7180932 * 2 ^ 59
def prefixEnd_7180932 : Nat := 4983230072969 + 3 ^ 40 * 7180932 * 2
def baseEnd_7180932 : Nat := 3687269663252003804225501

theorem tailTrace_7180932 : CollatzResearch.WordTrace tailWord_7180932 prefixEnd_7180932 3687269663252003804225501 := by
  unfold tailWord_7180932
  simp only [CollatzResearch.WordTrace]
  refine ⟨130955053410358622195788525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174606737880478162927718033 130955053410358622195788525)
  ·
    refine ⟨49108145028884483323420697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130955053410358622195788525 49108145028884483323420697)
    ·
      refine ⟨36831108771663362492565523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49108145028884483323420697 36831108771663362492565523)
      ·
        refine ⟨55246663157495043738848285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36831108771663362492565523 55246663157495043738848285)
        ·
          refine ⟨20717498684060641402068107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55246663157495043738848285 20717498684060641402068107)
          ·
            refine ⟨31076248026090962103102161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20717498684060641402068107 31076248026090962103102161)
            ·
              refine ⟨23307186019568221577326621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31076248026090962103102161 23307186019568221577326621)
              ·
                refine ⟨8740194757338083091497483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23307186019568221577326621 8740194757338083091497483)
                ·
                  refine ⟨13110292136007124637246225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8740194757338083091497483 13110292136007124637246225)
                  ·
                    refine ⟨9832719102005343477934669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13110292136007124637246225 9832719102005343477934669)
                    ·
                      refine ⟨3687269663252003804225501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9832719102005343477934669 3687269663252003804225501)
                      ·
                        rfl

theorem cell23_7180932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 3, 1, 2, 3].length) (baseStart_7180932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7180932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7180932 prefixEnd_7180932 := by exact prefixLift 7180932
  have htrace : WordTrace (prefixWord ++ tailWord_7180932) baseStart_7180932 baseEnd_7180932 := by
    simpa [prefixWord, tailWord_7180932, baseEnd_7180932] using wordTrace_append hprefix tailTrace_7180932
  have hstable : (prefixWord ++ tailWord_7180932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7180932).length < 2 ^ (prefixWord ++ tailWord_7180932).sum := by decide
  have hdescent : baseEnd_7180932 < baseStart_7180932 := by decide
  rcases family_descends (prefixWord ++ tailWord_7180932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7180946 : List Nat := [3, 2, 3, 1, 2, 3, 1, 1, 3, 2, 2]
def baseStart_7180946 : Nat := 118140960795 + 7180946 * 2 ^ 59
def prefixEnd_7180946 : Nat := 4983230072969 + 3 ^ 40 * 7180946 * 2
def baseEnd_7180946 : Nat := 3687276851981166749450437

theorem tailTrace_7180946 : CollatzResearch.WordTrace tailWord_7180946 prefixEnd_7180946 3687276851981166749450437 := by
  unfold tailWord_7180946
  simp only [CollatzResearch.WordTrace]
  refine ⟨65477654360666631195646673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174607078295111016521724461 65477654360666631195646673)
  ·
    refine ⟨49108240770499973396735005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65477654360666631195646673 49108240770499973396735005)
    ·
      refine ⟨18415590288937490023775627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49108240770499973396735005 18415590288937490023775627)
      ·
        refine ⟨27623385433406235035663441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18415590288937490023775627 27623385433406235035663441)
        ·
          refine ⟨20717539075054676276747581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27623385433406235035663441 20717539075054676276747581)
          ·
            refine ⟨7769077153145503603780343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20717539075054676276747581 7769077153145503603780343)
            ·
              refine ⟨11653615729718255405670515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7769077153145503603780343 11653615729718255405670515)
              ·
                refine ⟨17480423594577383108505773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11653615729718255405670515 17480423594577383108505773)
                ·
                  refine ⟨6555158847966518665689665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17480423594577383108505773 6555158847966518665689665)
                  ·
                    refine ⟨4916369135974888999267249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6555158847966518665689665 4916369135974888999267249)
                    ·
                      refine ⟨3687276851981166749450437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4916369135974888999267249 3687276851981166749450437)
                      ·
                        rfl

theorem cell23_7180946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 1, 3, 2, 2].length) (baseStart_7180946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7180946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7180946 prefixEnd_7180946 := by exact prefixLift 7180946
  have htrace : WordTrace (prefixWord ++ tailWord_7180946) baseStart_7180946 baseEnd_7180946 := by
    simpa [prefixWord, tailWord_7180946, baseEnd_7180946] using wordTrace_append hprefix tailTrace_7180946
  have hstable : (prefixWord ++ tailWord_7180946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7180946).length < 2 ^ (prefixWord ++ tailWord_7180946).sum := by decide
  have hdescent : baseEnd_7180946 < baseStart_7180946 := by decide
  rcases family_descends (prefixWord ++ tailWord_7180946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
