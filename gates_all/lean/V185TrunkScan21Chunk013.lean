import V185TrunkScan21Chunk012

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_155841 : List Nat := [1, 2, 6, 1, 2, 2, 1, 3, 3]
def baseStart_155841 : Nat := 118140960795 + 155841 * 2 ^ 59
def prefixEnd_155841 : Nat := 4983230072969 + 3 ^ 40 * 155841 * 2
def baseEnd_155841 : Nat := 35565039412191113364803

theorem tailTrace_155841 : CollatzResearch.WordTrace tailWord_155841 prefixEnd_155841 35565039412191113364803 := by
  unfold tailWord_155841
  simp only [CollatzResearch.WordTrace]
  refine ⟨5683988228422147368939377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3789325485614764912626251 5683988228422147368939377)
  ·
    refine ⟨4262991171316610526704533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5683988228422147368939377 4262991171316610526704533)
    ·
      refine ⟨199827711155466118439275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 4262991171316610526704533 199827711155466118439275)
      ·
        refine ⟨299741566733199177658913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199827711155466118439275 299741566733199177658913)
        ·
          refine ⟨224806175049899383244185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 299741566733199177658913 224806175049899383244185)
          ·
            refine ⟨168604631287424537433139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 224806175049899383244185 168604631287424537433139)
            ·
              refine ⟨252906946931136806149709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 168604631287424537433139 252906946931136806149709)
              ·
                refine ⟨94840105099176302306141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 252906946931136806149709 94840105099176302306141)
                ·
                  refine ⟨35565039412191113364803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 94840105099176302306141 35565039412191113364803)
                  ·
                    rfl

theorem cell21_155841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 3, 3].length) (baseStart_155841 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_155841 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_155841 prefixEnd_155841 := by exact prefixLift 155841
  have htrace : WordTrace (prefixWord ++ tailWord_155841) baseStart_155841 baseEnd_155841 := by
    simpa [prefixWord, tailWord_155841, baseEnd_155841] using wordTrace_append hprefix tailTrace_155841
  have hstable : (prefixWord ++ tailWord_155841).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155841).length < 2 ^ (prefixWord ++ tailWord_155841).sum := by decide
  have hdescent : baseEnd_155841 < baseStart_155841 := by decide
  rcases family_descends (prefixWord ++ tailWord_155841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155852 : List Nat := [2, 2, 1, 6, 1, 2, 7]
def baseStart_155852 : Nat := 118140960795 + 155852 * 2 ^ 59
def prefixEnd_155852 : Nat := 4983230072969 + 3 ^ 40 * 155852 * 2
def baseEnd_155852 : Nat := 3951949973561948742383

theorem tailTrace_155852 : CollatzResearch.WordTrace tailWord_155852 prefixEnd_155852 3951949973561948742383 := by
  unfold tailWord_155852
  simp only [CollatzResearch.WordTrace]
  refine ⟨2842194715691148123794905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3789592954254864165059873 2842194715691148123794905)
  ·
    refine ⟨2131646036768361092846179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2842194715691148123794905 2131646036768361092846179)
    ·
      refine ⟨3197469055152541639269269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2131646036768361092846179 3197469055152541639269269)
      ·
        refine ⟨149881361960275389340747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 3197469055152541639269269 149881361960275389340747)
        ·
          refine ⟨224822042940413084011121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149881361960275389340747 224822042940413084011121)
          ·
            refine ⟨168616532205309813008341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 224822042940413084011121 168616532205309813008341)
            ·
              refine ⟨3951949973561948742383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 168616532205309813008341 3951949973561948742383)
              ·
                rfl

theorem cell21_155852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 7].length) (baseStart_155852 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_155852 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_155852 prefixEnd_155852 := by exact prefixLift 155852
  have htrace : WordTrace (prefixWord ++ tailWord_155852) baseStart_155852 baseEnd_155852 := by
    simpa [prefixWord, tailWord_155852, baseEnd_155852] using wordTrace_append hprefix tailTrace_155852
  have hstable : (prefixWord ++ tailWord_155852).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155852).length < 2 ^ (prefixWord ++ tailWord_155852).sum := by decide
  have hdescent : baseEnd_155852 < baseStart_155852 := by decide
  rcases family_descends (prefixWord ++ tailWord_155852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155866 : List Nat := [3, 1, 1, 2, 2, 1, 2, 6, 3]
def baseStart_155866 : Nat := 118140960795 + 155866 * 2 ^ 59
def prefixEnd_155866 : Nat := 4983230072969 + 3 ^ 40 * 155866 * 2
def baseEnd_155866 : Nat := 35570744752796625448085

theorem tailTrace_155866 : CollatzResearch.WordTrace tailWord_155866 prefixEnd_155866 35570744752796625448085 := by
  unfold tailWord_155866
  simp only [CollatzResearch.WordTrace]
  refine ⟨1421225013332894159649863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3789933368887717759066301 1421225013332894159649863)
  ·
    refine ⟨2131837519999341239474795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1421225013332894159649863 2131837519999341239474795)
    ·
      refine ⟨3197756279999011859212193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2131837519999341239474795 3197756279999011859212193)
      ·
        refine ⟨2398317209999258894409145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3197756279999011859212193 2398317209999258894409145)
        ·
          refine ⟨1798737907499444170806859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2398317209999258894409145 1798737907499444170806859)
          ·
            refine ⟨2698106861249166256210289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1798737907499444170806859 2698106861249166256210289)
            ·
              refine ⟨2023580145936874692157717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2698106861249166256210289 2023580145936874692157717)
              ·
                refine ⟨94855319340791001194893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2023580145936874692157717 94855319340791001194893)
                ·
                  refine ⟨35570744752796625448085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 94855319340791001194893 35570744752796625448085)
                  ·
                    rfl

theorem cell21_155866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 6, 3].length) (baseStart_155866 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_155866 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_155866 prefixEnd_155866 := by exact prefixLift 155866
  have htrace : WordTrace (prefixWord ++ tailWord_155866) baseStart_155866 baseEnd_155866 := by
    simpa [prefixWord, tailWord_155866, baseEnd_155866] using wordTrace_append hprefix tailTrace_155866
  have hstable : (prefixWord ++ tailWord_155866).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155866).length < 2 ^ (prefixWord ++ tailWord_155866).sum := by decide
  have hdescent : baseEnd_155866 < baseStart_155866 := by decide
  rcases family_descends (prefixWord ++ tailWord_155866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155911 : List Nat := [1, 1, 4, 5, 1, 9]
def baseStart_155911 : Nat := 118140960795 + 155911 * 2 ^ 59
def prefixEnd_155911 : Nat := 4983230072969 + 3 ^ 40 * 155911 * 2
def baseEnd_155911 : Nat := 1317815346884686933259

theorem tailTrace_155911 : CollatzResearch.WordTrace tailWord_155911 prefixEnd_155911 1317815346884686933259 := by
  unfold tailWord_155911
  simp only [CollatzResearch.WordTrace]
  refine ⟨5686541338168549323987587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3791027558779032882658391 5686541338168549323987587)
  ·
    refine ⟨8529812007252823985981381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5686541338168549323987587 8529812007252823985981381)
    ·
      refine ⟨1599339751359904497371509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8529812007252823985981381 1599339751359904497371509)
      ·
        refine ⟨149938101689991046628579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1599339751359904497371509 149938101689991046628579)
        ·
          refine ⟨224907152534986569942869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149938101689991046628579 224907152534986569942869)
          ·
            refine ⟨1317815346884686933259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 224907152534986569942869 1317815346884686933259)
            ·
              rfl

theorem cell21_155911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 9].length) (baseStart_155911 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_155911 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_155911 prefixEnd_155911 := by exact prefixLift 155911
  have htrace : WordTrace (prefixWord ++ tailWord_155911) baseStart_155911 baseEnd_155911 := by
    simpa [prefixWord, tailWord_155911, baseEnd_155911] using wordTrace_append hprefix tailTrace_155911
  have hstable : (prefixWord ++ tailWord_155911).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155911).length < 2 ^ (prefixWord ++ tailWord_155911).sum := by decide
  have hdescent : baseEnd_155911 < baseStart_155911 := by decide
  rcases family_descends (prefixWord ++ tailWord_155911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156035 : List Nat := [1, 1, 1, 3, 7, 1, 1, 1, 5]
def baseStart_156035 : Nat := 118140960795 + 156035 * 2 ^ 59
def prefixEnd_156035 : Nat := 4983230072969 + 3 ^ 40 * 156035 * 2
def baseEnd_156035 : Nat := 35609312855289887131073

theorem tailTrace_156035 : CollatzResearch.WordTrace tailWord_156035 prefixEnd_156035 35609312855289887131073 := by
  unfold tailWord_156035
  simp only [CollatzResearch.WordTrace]
  refine ⟨5691063989719318501501559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3794042659812879001001039 5691063989719318501501559)
  ·
    refine ⟨8536595984578977752252339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5691063989719318501501559 8536595984578977752252339)
    ·
      refine ⟨12804893976868466628378509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8536595984578977752252339 12804893976868466628378509)
      ·
        refine ⟨4801835241325674985641941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12804893976868466628378509 4801835241325674985641941)
        ·
          refine ⟨112543013468570507475983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 4801835241325674985641941 112543013468570507475983)
          ·
            refine ⟨168814520202855761213975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112543013468570507475983 168814520202855761213975)
            ·
              refine ⟨253221780304283641820963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 168814520202855761213975 253221780304283641820963)
              ·
                refine ⟨379832670456425462731445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 253221780304283641820963 379832670456425462731445)
                ·
                  refine ⟨35609312855289887131073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 379832670456425462731445 35609312855289887131073)
                  ·
                    rfl

theorem cell21_156035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 1, 5].length) (baseStart_156035 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_156035 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_156035 prefixEnd_156035 := by exact prefixLift 156035
  have htrace : WordTrace (prefixWord ++ tailWord_156035) baseStart_156035 baseEnd_156035 := by
    simpa [prefixWord, tailWord_156035, baseEnd_156035] using wordTrace_append hprefix tailTrace_156035
  have hstable : (prefixWord ++ tailWord_156035).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156035).length < 2 ^ (prefixWord ++ tailWord_156035).sum := by decide
  have hdescent : baseEnd_156035 < baseStart_156035 := by decide
  rcases family_descends (prefixWord ++ tailWord_156035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156173 : List Nat := [1, 7, 1, 1, 1, 1, 4, 5]
def baseStart_156173 : Nat := 118140960795 + 156173 * 2 ^ 59
def prefixEnd_156173 : Nat := 4983230072969 + 3 ^ 40 * 156173 * 2
def baseEnd_156173 : Nat := 11880268778477437943597

theorem tailTrace_156173 : CollatzResearch.WordTrace tailWord_156173 prefixEnd_156173 11880268778477437943597 := by
  unfold tailWord_156173
  simp only [CollatzResearch.WordTrace]
  refine ⟨5696097263219368070025173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3797398175479578713350115 5696097263219368070025173)
  ·
    refine ⟨133502279606703939141215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 5696097263219368070025173 133502279606703939141215)
    ·
      refine ⟨200253419410055908711823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133502279606703939141215 200253419410055908711823)
      ·
        refine ⟨300380129115083863067735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200253419410055908711823 300380129115083863067735)
        ·
          refine ⟨450570193672625794601603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 300380129115083863067735 450570193672625794601603)
          ·
            refine ⟨675855290508938691902405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 450570193672625794601603 675855290508938691902405)
            ·
              refine ⟨126722866970426004731701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 675855290508938691902405 126722866970426004731701)
              ·
                refine ⟨11880268778477437943597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 126722866970426004731701 11880268778477437943597)
                ·
                  rfl

theorem cell21_156173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 4, 5].length) (baseStart_156173 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_156173 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_156173 prefixEnd_156173 := by exact prefixLift 156173
  have htrace : WordTrace (prefixWord ++ tailWord_156173) baseStart_156173 baseEnd_156173 := by
    simpa [prefixWord, tailWord_156173, baseEnd_156173] using wordTrace_append hprefix tailTrace_156173
  have hstable : (prefixWord ++ tailWord_156173).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156173).length < 2 ^ (prefixWord ++ tailWord_156173).sum := by decide
  have hdescent : baseEnd_156173 < baseStart_156173 := by decide
  rcases family_descends (prefixWord ++ tailWord_156173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156257 : List Nat := [1, 2, 3, 1, 1, 13]
def baseStart_156257 : Nat := 118140960795 + 156257 * 2 ^ 59
def prefixEnd_156257 : Nat := 4983230072969 + 3 ^ 40 * 156257 * 2
def baseEnd_156257 : Nat := 1320739862217290164097

theorem tailTrace_156257 : CollatzResearch.WordTrace tailWord_156257 prefixEnd_156257 1320739862217290164097 := by
  unfold tailWord_156257
  simp only [CollatzResearch.WordTrace]
  refine ⟨5699160994915050416083025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3799440663276700277388683 5699160994915050416083025)
  ·
    refine ⟨4274370746186287812062269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5699160994915050416083025 4274370746186287812062269)
    ·
      refine ⟨1602889029819857929523351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4274370746186287812062269 1602889029819857929523351)
      ·
        refine ⟨2404333544729786894285027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1602889029819857929523351 2404333544729786894285027)
        ·
          refine ⟨3606500317094680341427541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2404333544729786894285027 3606500317094680341427541)
          ·
            refine ⟨1320739862217290164097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 3606500317094680341427541 1320739862217290164097)
            ·
              rfl

theorem cell21_156257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 13].length) (baseStart_156257 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_156257 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_156257 prefixEnd_156257 := by exact prefixLift 156257
  have htrace : WordTrace (prefixWord ++ tailWord_156257) baseStart_156257 baseEnd_156257 := by
    simpa [prefixWord, tailWord_156257, baseEnd_156257] using wordTrace_append hprefix tailTrace_156257
  have hstable : (prefixWord ++ tailWord_156257).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156257).length < 2 ^ (prefixWord ++ tailWord_156257).sum := by decide
  have hdescent : baseEnd_156257 < baseStart_156257 := by decide
  rcases family_descends (prefixWord ++ tailWord_156257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156260 : List Nat := [2, 3, 1, 1, 2, 2, 4, 2, 4]
def baseStart_156260 : Nat := 118140960795 + 156260 * 2 ^ 59
def prefixEnd_156260 : Nat := 4983230072969 + 3 ^ 40 * 156260 * 2
def baseEnd_156260 : Nat := 35660660920739495880613

theorem tailTrace_156260 : CollatzResearch.WordTrace tailWord_156260 prefixEnd_156260 35660660920739495880613 := by
  unfold tailWord_156260
  simp only [CollatzResearch.WordTrace]
  refine ⟨2849635206952090964221117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3799513609269454618961489 2849635206952090964221117)
  ·
    refine ⟨1068613202607034111582919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2849635206952090964221117 1068613202607034111582919)
    ·
      refine ⟨1602919803910551167374379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1068613202607034111582919 1602919803910551167374379)
      ·
        refine ⟨2404379705865826751061569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1602919803910551167374379 2404379705865826751061569)
        ·
          refine ⟨1803284779399370063296177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2404379705865826751061569 1803284779399370063296177)
          ·
            refine ⟨1352463584549527547472133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1803284779399370063296177 1352463584549527547472133)
            ·
              refine ⟨253586922103036415151025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1352463584549527547472133 253586922103036415151025)
              ·
                refine ⟨190190191577277311363269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 253586922103036415151025 190190191577277311363269)
                ·
                  refine ⟨35660660920739495880613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 190190191577277311363269 35660660920739495880613)
                  ·
                    rfl

theorem cell21_156260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 2, 4].length) (baseStart_156260 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_156260 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_156260 prefixEnd_156260 := by exact prefixLift 156260
  have htrace : WordTrace (prefixWord ++ tailWord_156260) baseStart_156260 baseEnd_156260 := by
    simpa [prefixWord, tailWord_156260, baseEnd_156260] using wordTrace_append hprefix tailTrace_156260
  have hstable : (prefixWord ++ tailWord_156260).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156260).length < 2 ^ (prefixWord ++ tailWord_156260).sum := by decide
  have hdescent : baseEnd_156260 < baseStart_156260 := by decide
  rcases family_descends (prefixWord ++ tailWord_156260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156288 : List Nat := [2, 1, 1, 2, 1, 5, 1, 1, 7]
def baseStart_156288 : Nat := 118140960795 + 156288 * 2 ^ 59
def prefixEnd_156288 : Nat := 4983230072969 + 3 ^ 40 * 156288 * 2
def baseEnd_156288 : Nat := 35667050902217669413889

theorem tailTrace_156288 : CollatzResearch.WordTrace tailWord_156288 prefixEnd_156288 35667050902217669413889 := by
  unfold tailWord_156288
  simp only [CollatzResearch.WordTrace]
  refine ⟨2850145828901371355230759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3800194438535161806974345 2850145828901371355230759)
  ·
    refine ⟨4275218743352057032846139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2850145828901371355230759 4275218743352057032846139)
    ·
      refine ⟨6412828115028085549269209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4275218743352057032846139 6412828115028085549269209)
      ·
        refine ⟨4809621086271064161951907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6412828115028085549269209 4809621086271064161951907)
        ·
          refine ⟨7214431629406596242927861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4809621086271064161951907 7214431629406596242927861)
          ·
            refine ⟨676352965256868397774487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7214431629406596242927861 676352965256868397774487)
            ·
              refine ⟨1014529447885302596661731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 676352965256868397774487 1014529447885302596661731)
              ·
                refine ⟨1521794171827953894992597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1014529447885302596661731 1521794171827953894992597)
                ·
                  refine ⟨35667050902217669413889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1521794171827953894992597 35667050902217669413889)
                  ·
                    rfl

theorem cell21_156288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 7].length) (baseStart_156288 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_156288 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_156288 prefixEnd_156288 := by exact prefixLift 156288
  have htrace : WordTrace (prefixWord ++ tailWord_156288) baseStart_156288 baseEnd_156288 := by
    simpa [prefixWord, tailWord_156288, baseEnd_156288] using wordTrace_append hprefix tailTrace_156288
  have hstable : (prefixWord ++ tailWord_156288).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156288).length < 2 ^ (prefixWord ++ tailWord_156288).sum := by decide
  have hdescent : baseEnd_156288 < baseStart_156288 := by decide
  rcases family_descends (prefixWord ++ tailWord_156288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156342 : List Nat := [5, 1, 3, 1, 3, 1, 2, 5]
def baseStart_156342 : Nat := 118140960795 + 156342 * 2 ^ 59
def prefixEnd_156342 : Nat := 4983230072969 + 3 ^ 40 * 156342 * 2
def baseEnd_156342 : Nat := 11893124812641858504593

theorem tailTrace_156342 : CollatzResearch.WordTrace tailWord_156342 prefixEnd_156342 11893124812641858504593 := by
  unfold tailWord_156342
  simp only [CollatzResearch.WordTrace]
  refine ⟨356391324975444370807955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3801507466404739955284853 356391324975444370807955)
  ·
    refine ⟨534586987463166556211933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 356391324975444370807955 534586987463166556211933)
    ·
      refine ⟨200470120298687458579475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 534586987463166556211933 200470120298687458579475)
      ·
        refine ⟨300705180448031187869213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200470120298687458579475 300705180448031187869213)
        ·
          refine ⟨112764442668011695450955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 300705180448031187869213 112764442668011695450955)
          ·
            refine ⟨169146664002017543176433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112764442668011695450955 169146664002017543176433)
            ·
              refine ⟨126859998001513157382325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 169146664002017543176433 126859998001513157382325)
              ·
                refine ⟨11893124812641858504593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 126859998001513157382325 11893124812641858504593)
                ·
                  rfl

theorem cell21_156342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 2, 5].length) (baseStart_156342 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_156342 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_156342 prefixEnd_156342 := by exact prefixLift 156342
  have htrace : WordTrace (prefixWord ++ tailWord_156342) baseStart_156342 baseEnd_156342 := by
    simpa [prefixWord, tailWord_156342, baseEnd_156342] using wordTrace_append hprefix tailTrace_156342
  have hstable : (prefixWord ++ tailWord_156342).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156342).length < 2 ^ (prefixWord ++ tailWord_156342).sum := by decide
  have hdescent : baseEnd_156342 < baseStart_156342 := by decide
  rcases family_descends (prefixWord ++ tailWord_156342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156350 : List Nat := [4, 2, 1, 1, 2, 1, 3, 7]
def baseStart_156350 : Nat := 118140960795 + 156350 * 2 ^ 59
def prefixEnd_156350 : Nat := 4983230072969 + 3 ^ 40 * 156350 * 2
def baseEnd_156350 : Nat := 11893733382306446460143

theorem tailTrace_156350 : CollatzResearch.WordTrace tailWord_156350 prefixEnd_156350 11893733382306446460143 := by
  unfold tailWord_156350
  simp only [CollatzResearch.WordTrace]
  refine ⟨712819122947265912402313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3801701989052084866145669 712819122947265912402313)
  ·
    refine ⟨534614342210449434301735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 712819122947265912402313 534614342210449434301735)
    ·
      refine ⟨801921513315674151452603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 534614342210449434301735 801921513315674151452603)
      ·
        refine ⟨1202882269973511227178905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 801921513315674151452603 1202882269973511227178905)
        ·
          refine ⟨902161702480133420384179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1202882269973511227178905 902161702480133420384179)
          ·
            refine ⟨1353242553720200130576269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 902161702480133420384179 1353242553720200130576269)
            ·
              refine ⟨507465957645075048966101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1353242553720200130576269 507465957645075048966101)
              ·
                refine ⟨11893733382306446460143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 507465957645075048966101 11893733382306446460143)
                ·
                  rfl

theorem cell21_156350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 7].length) (baseStart_156350 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_156350 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_156350 prefixEnd_156350 := by exact prefixLift 156350
  have htrace : WordTrace (prefixWord ++ tailWord_156350) baseStart_156350 baseEnd_156350 := by
    simpa [prefixWord, tailWord_156350, baseEnd_156350] using wordTrace_append hprefix tailTrace_156350
  have hstable : (prefixWord ++ tailWord_156350).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156350).length < 2 ^ (prefixWord ++ tailWord_156350).sum := by decide
  have hdescent : baseEnd_156350 < baseStart_156350 := by decide
  rcases family_descends (prefixWord ++ tailWord_156350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156440 : List Nat := [2, 1, 2, 3, 1, 1, 1, 5, 5]
def baseStart_156440 : Nat := 118140960795 + 156440 * 2 ^ 59
def prefixEnd_156440 : Nat := 4983230072969 + 3 ^ 40 * 156440 * 2
def baseEnd_156440 : Nat := 35701739373099182880245

theorem tailTrace_156440 : CollatzResearch.WordTrace tailWord_156440 prefixEnd_156440 35701739373099182880245 := by
  unfold tailWord_156440
  simp only [CollatzResearch.WordTrace]
  refine ⟨2852917776626036334997387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3803890368834715113329849 2852917776626036334997387)
  ·
    refine ⟨4279376664939054502496081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2852917776626036334997387 4279376664939054502496081)
    ·
      refine ⟨3209532498704290876872061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4279376664939054502496081 3209532498704290876872061)
      ·
        refine ⟨1203574687014109078827023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3209532498704290876872061 1203574687014109078827023)
        ·
          refine ⟨1805362030521163618240535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1203574687014109078827023 1805362030521163618240535)
          ·
            refine ⟨2708043045781745427360803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1805362030521163618240535 2708043045781745427360803)
            ·
              refine ⟨4062064568672618141041205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2708043045781745427360803 4062064568672618141041205)
              ·
                refine ⟨380818553313057950722613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4062064568672618141041205 380818553313057950722613)
                ·
                  refine ⟨35701739373099182880245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 380818553313057950722613 35701739373099182880245)
                  ·
                    rfl

theorem cell21_156440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 5, 5].length) (baseStart_156440 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_156440 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_156440 prefixEnd_156440 := by exact prefixLift 156440
  have htrace : WordTrace (prefixWord ++ tailWord_156440) baseStart_156440 baseEnd_156440 := by
    simpa [prefixWord, tailWord_156440, baseEnd_156440] using wordTrace_append hprefix tailTrace_156440
  have hstable : (prefixWord ++ tailWord_156440).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156440).length < 2 ^ (prefixWord ++ tailWord_156440).sum := by decide
  have hdescent : baseEnd_156440 < baseStart_156440 := by decide
  rcases family_descends (prefixWord ++ tailWord_156440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156519 : List Nat := [1, 1, 5, 1, 2, 4, 2, 5]
def baseStart_156519 : Nat := 118140960795 + 156519 * 2 ^ 59
def prefixEnd_156519 : Nat := 4983230072969 + 3 ^ 40 * 156519 * 2
def baseEnd_156519 : Nat := 11906589416470867021139

theorem tailTrace_156519 : CollatzResearch.WordTrace tailWord_156519 prefixEnd_156519 11906589416470867021139 := by
  unfold tailWord_156519
  simp only [CollatzResearch.WordTrace]
  refine ⟨5708716919965869162120611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3805811279977246108080407 5708716919965869162120611)
  ·
    refine ⟨8563075379948803743180917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5708716919965869162120611 8563075379948803743180917)
    ·
      refine ⟨802788316870200350923211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8563075379948803743180917 802788316870200350923211)
      ·
        refine ⟨1204182475305300526384817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 802788316870200350923211 1204182475305300526384817)
        ·
          refine ⟨903136856478975394788613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1204182475305300526384817 903136856478975394788613)
          ·
            refine ⟨169338160589807886522865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 903136856478975394788613 169338160589807886522865)
            ·
              refine ⟨127003620442355914892149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 169338160589807886522865 127003620442355914892149)
              ·
                refine ⟨11906589416470867021139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 127003620442355914892149 11906589416470867021139)
                ·
                  rfl

theorem cell21_156519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 2, 5].length) (baseStart_156519 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_156519 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_156519 prefixEnd_156519 := by exact prefixLift 156519
  have htrace : WordTrace (prefixWord ++ tailWord_156519) baseStart_156519 baseEnd_156519 := by
    simpa [prefixWord, tailWord_156519, baseEnd_156519] using wordTrace_append hprefix tailTrace_156519
  have hstable : (prefixWord ++ tailWord_156519).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156519).length < 2 ^ (prefixWord ++ tailWord_156519).sum := by decide
  have hdescent : baseEnd_156519 < baseStart_156519 := by decide
  rcases family_descends (prefixWord ++ tailWord_156519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156547 : List Nat := [1, 1, 1, 3, 4, 1, 2, 4, 4]
def baseStart_156547 : Nat := 118140960795 + 156547 * 2 ^ 59
def prefixEnd_156547 : Nat := 4983230072969 + 3 ^ 40 * 156547 * 2
def baseEnd_156547 : Nat := 35726158230890774596693

theorem tailTrace_156547 : CollatzResearch.WordTrace tailWord_156547 prefixEnd_156547 35726158230890774596693 := by
  unfold tailWord_156547
  simp only [CollatzResearch.WordTrace]
  refine ⟨5709738163864429944139895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3806492109242953296093263 5709738163864429944139895)
  ·
    refine ⟨8564607245796644916209843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5709738163864429944139895 8564607245796644916209843)
    ·
      refine ⟨12846910868694967374314765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8564607245796644916209843 12846910868694967374314765)
      ·
        refine ⟨4817591575760612765368037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12846910868694967374314765 4817591575760612765368037)
        ·
          refine ⟨903298420455114893506507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4817591575760612765368037 903298420455114893506507)
          ·
            refine ⟨1354947630682672340259761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 903298420455114893506507 1354947630682672340259761)
            ·
              refine ⟨1016210723012004255194821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1354947630682672340259761 1016210723012004255194821)
              ·
                refine ⟨190539510564750797849029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1016210723012004255194821 190539510564750797849029)
                ·
                  refine ⟨35726158230890774596693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 190539510564750797849029 35726158230890774596693)
                  ·
                    rfl

theorem cell21_156547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 4, 4].length) (baseStart_156547 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_156547 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_156547 prefixEnd_156547 := by exact prefixLift 156547
  have htrace : WordTrace (prefixWord ++ tailWord_156547) baseStart_156547 baseEnd_156547 := by
    simpa [prefixWord, tailWord_156547, baseEnd_156547] using wordTrace_append hprefix tailTrace_156547
  have hstable : (prefixWord ++ tailWord_156547).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156547).length < 2 ^ (prefixWord ++ tailWord_156547).sum := by decide
  have hdescent : baseEnd_156547 < baseStart_156547 := by decide
  rcases family_descends (prefixWord ++ tailWord_156547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156564 : List Nat := [2, 4, 2, 1, 1, 1, 3, 3, 4]
def baseStart_156564 : Nat := 118140960795 + 156564 * 2 ^ 59
def prefixEnd_156564 : Nat := 4983230072969 + 3 ^ 40 * 156564 * 2
def baseEnd_156564 : Nat := 35730037862502522813325

theorem tailTrace_156564 : CollatzResearch.WordTrace tailWord_156564 prefixEnd_156564 35730037862502522813325 := by
  unfold tailWord_156564
  simp only [CollatzResearch.WordTrace]
  refine ⟨2855179102401420923754373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3806905469868561231672497 2855179102401420923754373)
  ·
    refine ⟨535346081700266423203945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2855179102401420923754373 535346081700266423203945)
    ·
      refine ⟨401509561275199817402959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 535346081700266423203945 401509561275199817402959)
      ·
        refine ⟨602264341912799726104439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 401509561275199817402959 602264341912799726104439)
        ·
          refine ⟨903396512869199589156659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 602264341912799726104439 903396512869199589156659)
          ·
            refine ⟨1355094769303799383734989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 903396512869199589156659 1355094769303799383734989)
            ·
              refine ⟨508160538488924768900621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1355094769303799383734989 508160538488924768900621)
              ·
                refine ⟨190560201933346788337733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 508160538488924768900621 190560201933346788337733)
                ·
                  refine ⟨35730037862502522813325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 190560201933346788337733 35730037862502522813325)
                  ·
                    rfl

theorem cell21_156564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_156564 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_156564 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_156564 prefixEnd_156564 := by exact prefixLift 156564
  have htrace : WordTrace (prefixWord ++ tailWord_156564) baseStart_156564 baseEnd_156564 := by
    simpa [prefixWord, tailWord_156564, baseEnd_156564] using wordTrace_append hprefix tailTrace_156564
  have hstable : (prefixWord ++ tailWord_156564).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156564).length < 2 ^ (prefixWord ++ tailWord_156564).sum := by decide
  have hdescent : baseEnd_156564 < baseStart_156564 := by decide
  rcases family_descends (prefixWord ++ tailWord_156564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156578 : List Nat := [3, 3, 1, 2, 2, 1, 2, 7]
def baseStart_156578 : Nat := 118140960795 + 156578 * 2 ^ 59
def prefixEnd_156578 : Nat := 4983230072969 + 3 ^ 40 * 156578 * 2
def baseEnd_156578 : Nat := 11911077617747203193321

theorem tailTrace_156578 : CollatzResearch.WordTrace tailWord_156578 prefixEnd_156578 11911077617747203193321 := by
  unfold tailWord_156578
  simp only [CollatzResearch.WordTrace]
  refine ⟨1427717206688030559629597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3807245884501414825678925 1427717206688030559629597)
  ·
    refine ⟨535393952508011459861099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1427717206688030559629597 535393952508011459861099)
    ·
      refine ⟨803090928762017189791649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 535393952508011459861099 803090928762017189791649)
      ·
        refine ⟨602318196571512892343737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 803090928762017189791649 602318196571512892343737)
        ·
          refine ⟨451738647428634669257803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 602318196571512892343737 451738647428634669257803)
          ·
            refine ⟨677607971142952003886705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 451738647428634669257803 677607971142952003886705)
            ·
              refine ⟨508205978357214002915029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 677607971142952003886705 508205978357214002915029)
              ·
                refine ⟨11911077617747203193321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 508205978357214002915029 11911077617747203193321)
                ·
                  rfl

theorem cell21_156578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 7].length) (baseStart_156578 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_156578 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_156578 prefixEnd_156578 := by exact prefixLift 156578
  have htrace : WordTrace (prefixWord ++ tailWord_156578) baseStart_156578 baseEnd_156578 := by
    simpa [prefixWord, tailWord_156578, baseEnd_156578] using wordTrace_append hprefix tailTrace_156578
  have hstable : (prefixWord ++ tailWord_156578).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156578).length < 2 ^ (prefixWord ++ tailWord_156578).sum := by decide
  have hdescent : baseEnd_156578 < baseStart_156578 := by decide
  rcases family_descends (prefixWord ++ tailWord_156578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156612 : List Nat := [2, 3, 3, 3, 1, 2, 1, 6]
def baseStart_156612 : Nat := 118140960795 + 156612 * 2 ^ 59
def prefixEnd_156612 : Nat := 4983230072969 + 3 ^ 40 * 156612 * 2
def baseEnd_156612 : Nat := 11913664038821702004409

theorem tailTrace_156612 : CollatzResearch.WordTrace tailWord_156612 prefixEnd_156612 11913664038821702004409 := by
  unfold tailWord_156612
  simp only [CollatzResearch.WordTrace]
  refine ⟨2856054454314473022628045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3808072605752630696837393 2856054454314473022628045)
  ·
    refine ⟨1071020420367927383485517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2856054454314473022628045 1071020420367927383485517)
    ·
      refine ⟨401632657637972768807069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1071020420367927383485517 401632657637972768807069)
      ·
        refine ⟨150612246614239788302651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 401632657637972768807069 150612246614239788302651)
        ·
          refine ⟨225918369921359682453977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150612246614239788302651 225918369921359682453977)
          ·
            refine ⟨169438777441019761840483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 225918369921359682453977 169438777441019761840483)
            ·
              refine ⟨254158166161529642760725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 169438777441019761840483 254158166161529642760725)
              ·
                refine ⟨11913664038821702004409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 254158166161529642760725 11913664038821702004409)
                ·
                  rfl

theorem cell21_156612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 6].length) (baseStart_156612 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_156612 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_156612 prefixEnd_156612 := by exact prefixLift 156612
  have htrace : WordTrace (prefixWord ++ tailWord_156612) baseStart_156612 baseEnd_156612 := by
    simpa [prefixWord, tailWord_156612, baseEnd_156612] using wordTrace_append hprefix tailTrace_156612
  have hstable : (prefixWord ++ tailWord_156612).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156612).length < 2 ^ (prefixWord ++ tailWord_156612).sum := by decide
  have hdescent : baseEnd_156612 < baseStart_156612 := by decide
  rcases family_descends (prefixWord ++ tailWord_156612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156623 : List Nat := [1, 1, 2, 1, 1, 6, 2, 3, 4]
def baseStart_156623 : Nat := 118140960795 + 156623 * 2 ^ 59
def prefixEnd_156623 : Nat := 4983230072969 + 3 ^ 40 * 156623 * 2
def baseEnd_156623 : Nat := 35743502466331531329871

theorem tailTrace_156623 : CollatzResearch.WordTrace tailWord_156623 prefixEnd_156623 35743502466331531329871 := by
  unfold tailWord_156623
  simp only [CollatzResearch.WordTrace]
  refine ⟨5712510111589094923906523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3808340074392729949271015 5712510111589094923906523)
  ·
    refine ⟨8568765167383642385859785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5712510111589094923906523 8568765167383642385859785)
    ·
      refine ⟨6426573875537731789394839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8568765167383642385859785 6426573875537731789394839)
      ·
        refine ⟨9639860813306597684092259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6426573875537731789394839 9639860813306597684092259)
        ·
          refine ⟨14459791219959896526138389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9639860813306597684092259 14459791219959896526138389)
          ·
            refine ⟨677802713435620149662737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 14459791219959896526138389 677802713435620149662737)
            ·
              refine ⟨508352035076715112247053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 677802713435620149662737 508352035076715112247053)
              ·
                refine ⟨190632013153768167092645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 508352035076715112247053 190632013153768167092645)
                ·
                  refine ⟨35743502466331531329871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 190632013153768167092645 35743502466331531329871)
                  ·
                    rfl

theorem cell21_156623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 3, 4].length) (baseStart_156623 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_156623 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_156623 prefixEnd_156623 := by exact prefixLift 156623
  have htrace : WordTrace (prefixWord ++ tailWord_156623) baseStart_156623 baseEnd_156623 := by
    simpa [prefixWord, tailWord_156623, baseEnd_156623] using wordTrace_append hprefix tailTrace_156623
  have hstable : (prefixWord ++ tailWord_156623).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156623).length < 2 ^ (prefixWord ++ tailWord_156623).sum := by decide
  have hdescent : baseEnd_156623 < baseStart_156623 := by decide
  rcases family_descends (prefixWord ++ tailWord_156623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156654 : List Nat := [4, 1, 2, 1, 4, 1, 8]
def baseStart_156654 : Nat := 118140960795 + 156654 * 2 ^ 59
def prefixEnd_156654 : Nat := 4983230072969 + 3 ^ 40 * 156654 * 2
def baseEnd_156654 : Nat := 3972286343186929590349

theorem tailTrace_156654 : CollatzResearch.WordTrace tailWord_156654 prefixEnd_156654 3972286343186929590349 := by
  unfold tailWord_156654
  simp only [CollatzResearch.WordTrace]
  refine ⟨714205096809598402285627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3809093849651191478856677 714205096809598402285627)
  ·
    refine ⟨1071307645214397603428441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 714205096809598402285627 1071307645214397603428441)
    ·
      refine ⟨803480733910798202571331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1071307645214397603428441 803480733910798202571331)
      ·
        refine ⟨1205221100866197303856997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 803480733910798202571331 1205221100866197303856997)
        ·
          refine ⟨225978956412411994473187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1205221100866197303856997 225978956412411994473187)
          ·
            refine ⟨338968434618617991709781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 225978956412411994473187 338968434618617991709781)
            ·
              refine ⟨3972286343186929590349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 338968434618617991709781 3972286343186929590349)
              ·
                rfl

theorem cell21_156654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 8].length) (baseStart_156654 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_156654 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_156654 prefixEnd_156654 := by exact prefixLift 156654
  have htrace : WordTrace (prefixWord ++ tailWord_156654) baseStart_156654 baseEnd_156654 := by
    simpa [prefixWord, tailWord_156654, baseEnd_156654] using wordTrace_append hprefix tailTrace_156654
  have hstable : (prefixWord ++ tailWord_156654).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156654).length < 2 ^ (prefixWord ++ tailWord_156654).sum := by decide
  have hdescent : baseEnd_156654 < baseStart_156654 := by decide
  rcases family_descends (prefixWord ++ tailWord_156654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156668 : List Nat := [2, 2, 2, 1, 2, 3, 1, 3, 5]
def baseStart_156668 : Nat := 118140960795 + 156668 * 2 ^ 59
def prefixEnd_156668 : Nat := 4983230072969 + 3 ^ 40 * 156668 * 2
def baseEnd_156668 : Nat := 35753772079421453079779

theorem tailTrace_156668 : CollatzResearch.WordTrace tailWord_156668 prefixEnd_156668 35753772079421453079779 := by
  unfold tailWord_156668
  simp only [CollatzResearch.WordTrace]
  refine ⟨2857075698213033804647329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3809434264284045072863105 2857075698213033804647329)
  ·
    refine ⟨2142806773659775353485497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2857075698213033804647329 2142806773659775353485497)
    ·
      refine ⟨1607105080244831515114123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2142806773659775353485497 1607105080244831515114123)
      ·
        refine ⟨2410657620367247272671185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1607105080244831515114123 2410657620367247272671185)
        ·
          refine ⟨1807993215275435454503389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2410657620367247272671185 1807993215275435454503389)
          ·
            refine ⟨677997455728288295438771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1807993215275435454503389 677997455728288295438771)
            ·
              refine ⟨1016996183592432443158157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 677997455728288295438771 1016996183592432443158157)
              ·
                refine ⟨381373568847162166184309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1016996183592432443158157 381373568847162166184309)
                ·
                  refine ⟨35753772079421453079779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 381373568847162166184309 35753772079421453079779)
                  ·
                    rfl

theorem cell21_156668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 3, 5].length) (baseStart_156668 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_156668 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_156668 prefixEnd_156668 := by exact prefixLift 156668
  have htrace : WordTrace (prefixWord ++ tailWord_156668) baseStart_156668 baseEnd_156668 := by
    simpa [prefixWord, tailWord_156668, baseEnd_156668] using wordTrace_append hprefix tailTrace_156668
  have hstable : (prefixWord ++ tailWord_156668).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156668).length < 2 ^ (prefixWord ++ tailWord_156668).sum := by decide
  have hdescent : baseEnd_156668 < baseStart_156668 := by decide
  rcases family_descends (prefixWord ++ tailWord_156668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156733 : List Nat := [1, 4, 1, 3, 1, 4, 2, 1, 4]
def baseStart_156733 : Nat := 118140960795 + 156733 * 2 ^ 59
def prefixEnd_156733 : Nat := 4983230072969 + 3 ^ 40 * 156733 * 2
def baseEnd_156733 : Nat := 35768605964995784496313

theorem tailTrace_156733 : CollatzResearch.WordTrace tailWord_156733 prefixEnd_156733 35768605964995784496313 := by
  unfold tailWord_156733
  simp only [CollatzResearch.WordTrace]
  refine ⟨5716522141190583710410853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3811014760793722473607235 5716522141190583710410853)
  ·
    refine ⟨1071847901473234445702035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5716522141190583710410853 1071847901473234445702035)
    ·
      refine ⟨1607771852209851668553053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1071847901473234445702035 1607771852209851668553053)
      ·
        refine ⟨602914444578694375707395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1607771852209851668553053 602914444578694375707395)
        ·
          refine ⟨904371666868041563561093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 602914444578694375707395 904371666868041563561093)
          ·
            refine ⟨169569687537757793167705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 904371666868041563561093 169569687537757793167705)
            ·
              refine ⟨127177265653318344875779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 169569687537757793167705 127177265653318344875779)
              ·
                refine ⟨190765898479977517313669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 127177265653318344875779 190765898479977517313669)
                ·
                  refine ⟨35768605964995784496313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 190765898479977517313669 35768605964995784496313)
                  ·
                    rfl

theorem cell21_156733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 2, 1, 4].length) (baseStart_156733 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_156733 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_156733 prefixEnd_156733 := by exact prefixLift 156733
  have htrace : WordTrace (prefixWord ++ tailWord_156733) baseStart_156733 baseEnd_156733 := by
    simpa [prefixWord, tailWord_156733, baseEnd_156733] using wordTrace_append hprefix tailTrace_156733
  have hstable : (prefixWord ++ tailWord_156733).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156733).length < 2 ^ (prefixWord ++ tailWord_156733).sum := by decide
  have hdescent : baseEnd_156733 < baseStart_156733 := by decide
  rcases family_descends (prefixWord ++ tailWord_156733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156775 : List Nat := [1, 1, 5, 1, 1, 3, 1, 4, 4]
def baseStart_156775 : Nat := 118140960795 + 156775 * 2 ^ 59
def prefixEnd_156775 : Nat := 4983230072969 + 3 ^ 40 * 156775 * 2
def baseEnd_156775 : Nat := 35778190937213044796227

theorem tailTrace_156775 : CollatzResearch.WordTrace tailWord_156775 prefixEnd_156775 35778190937213044796227 := by
  unfold tailWord_156775
  simp only [CollatzResearch.WordTrace]
  refine ⟨5718054007038424883439779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3812036004692283255626519 5718054007038424883439779)
  ·
    refine ⟨8577081010557637325159669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5718054007038424883439779 8577081010557637325159669)
    ·
      refine ⟨804101344739778499233719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8577081010557637325159669 804101344739778499233719)
      ·
        refine ⟨1206152017109667748850579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 804101344739778499233719 1206152017109667748850579)
        ·
          refine ⟨1809228025664501623275869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1206152017109667748850579 1809228025664501623275869)
          ·
            refine ⟨678460509624188108728451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1809228025664501623275869 678460509624188108728451)
            ·
              refine ⟨1017690764436282163092677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 678460509624188108728451 1017690764436282163092677)
              ·
                refine ⟨190817018331802905579877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1017690764436282163092677 190817018331802905579877)
                ·
                  refine ⟨35778190937213044796227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 190817018331802905579877 35778190937213044796227)
                  ·
                    rfl

theorem cell21_156775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 4, 4].length) (baseStart_156775 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_156775 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_156775 prefixEnd_156775 := by exact prefixLift 156775
  have htrace : WordTrace (prefixWord ++ tailWord_156775) baseStart_156775 baseEnd_156775 := by
    simpa [prefixWord, tailWord_156775, baseEnd_156775] using wordTrace_append hprefix tailTrace_156775
  have hstable : (prefixWord ++ tailWord_156775).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156775).length < 2 ^ (prefixWord ++ tailWord_156775).sum := by decide
  have hdescent : baseEnd_156775 < baseStart_156775 := by decide
  rcases family_descends (prefixWord ++ tailWord_156775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156778 : List Nat := [3, 1, 3, 2, 2, 2, 1, 4, 3]
def baseStart_156778 : Nat := 118140960795 + 156778 * 2 ^ 59
def prefixEnd_156778 : Nat := 4983230072969 + 3 ^ 40 * 156778 * 2
def baseEnd_156778 : Nat := 35778875578085706246221

theorem tailTrace_156778 : CollatzResearch.WordTrace tailWord_156778 prefixEnd_156778 35778875578085706246221 := by
  unfold tailWord_156778
  simp only [CollatzResearch.WordTrace]
  refine ⟨1429540856506889098949747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3812108950685037597199325 1429540856506889098949747)
  ·
    refine ⟨2144311284760333648424621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1429540856506889098949747 2144311284760333648424621)
    ·
      refine ⟨804116731785125118159233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2144311284760333648424621 804116731785125118159233)
      ·
        refine ⟨603087548838843838619425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 804116731785125118159233 603087548838843838619425)
        ·
          refine ⟨452315661629132878964569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 603087548838843838619425 452315661629132878964569)
          ·
            refine ⟨339236746221849659223427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 452315661629132878964569 339236746221849659223427)
            ·
              refine ⟨508855119332774488835141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 339236746221849659223427 508855119332774488835141)
              ·
                refine ⟨95410334874895216656589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 508855119332774488835141 95410334874895216656589)
                ·
                  refine ⟨35778875578085706246221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 95410334874895216656589 35778875578085706246221)
                  ·
                    rfl

theorem cell21_156778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 4, 3].length) (baseStart_156778 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_156778 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_156778 prefixEnd_156778 := by exact prefixLift 156778
  have htrace : WordTrace (prefixWord ++ tailWord_156778) baseStart_156778 baseEnd_156778 := by
    simpa [prefixWord, tailWord_156778, baseEnd_156778] using wordTrace_append hprefix tailTrace_156778
  have hstable : (prefixWord ++ tailWord_156778).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156778).length < 2 ^ (prefixWord ++ tailWord_156778).sum := by decide
  have hdescent : baseEnd_156778 < baseStart_156778 := by decide
  rcases family_descends (prefixWord ++ tailWord_156778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156837 : List Nat := [1, 3, 1, 2, 1, 4, 2, 4, 3]
def baseStart_156837 : Nat := 118140960795 + 156837 * 2 ^ 59
def prefixEnd_156837 : Nat := 4983230072969 + 3 ^ 40 * 156837 * 2
def baseEnd_156837 : Nat := 35792340181914714762767

theorem tailTrace_156837 : CollatzResearch.WordTrace tailWord_156837 prefixEnd_156837 35792340181914714762767 := by
  unfold tailWord_156837
  simp only [CollatzResearch.WordTrace]
  refine ⟨5720315332813809472196765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3813543555209206314797843 5720315332813809472196765)
  ·
    refine ⟨2145118249805178552073787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5720315332813809472196765 2145118249805178552073787)
    ·
      refine ⟨3217677374707767828110681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2145118249805178552073787 3217677374707767828110681)
      ·
        refine ⟨2413258031030825871083011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3217677374707767828110681 2413258031030825871083011)
        ·
          refine ⟨3619887046546238806624517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2413258031030825871083011 3619887046546238806624517)
          ·
            refine ⟨678728821227419776242097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3619887046546238806624517 678728821227419776242097)
            ·
              refine ⟨509046615920564832181573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 678728821227419776242097 509046615920564832181573)
              ·
                refine ⟨95446240485105906034045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 509046615920564832181573 95446240485105906034045)
                ·
                  refine ⟨35792340181914714762767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 95446240485105906034045 35792340181914714762767)
                  ·
                    rfl

theorem cell21_156837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 4, 3].length) (baseStart_156837 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_156837 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_156837 prefixEnd_156837 := by exact prefixLift 156837
  have htrace : WordTrace (prefixWord ++ tailWord_156837) baseStart_156837 baseEnd_156837 := by
    simpa [prefixWord, tailWord_156837, baseEnd_156837] using wordTrace_append hprefix tailTrace_156837
  have hstable : (prefixWord ++ tailWord_156837).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156837).length < 2 ^ (prefixWord ++ tailWord_156837).sum := by decide
  have hdescent : baseEnd_156837 < baseStart_156837 := by decide
  rcases family_descends (prefixWord ++ tailWord_156837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156896 : List Nat := [2, 1, 1, 3, 1, 4, 3, 1, 5]
def baseStart_156896 : Nat := 118140960795 + 156896 * 2 ^ 59
def prefixEnd_156896 : Nat := 4983230072969 + 3 ^ 40 * 156896 * 2
def baseEnd_156896 : Nat := 35805804785743723279313

theorem tailTrace_156896 : CollatzResearch.WordTrace tailWord_156896 prefixEnd_156896 35805804785743723279313 := by
  unfold tailWord_156896
  simp only [CollatzResearch.WordTrace]
  refine ⟨2861233619800031274297271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3814978159733375032396361 2861233619800031274297271)
  ·
    refine ⟨4291850429700046911445907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2861233619800031274297271 4291850429700046911445907)
    ·
      refine ⟨6437775644550070367168861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4291850429700046911445907 6437775644550070367168861)
      ·
        refine ⟨2414165866706276387688323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6437775644550070367168861 2414165866706276387688323)
        ·
          refine ⟨3621248800059414581532485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2414165866706276387688323 3621248800059414581532485)
          ·
            refine ⟨678984150011140234037341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3621248800059414581532485 678984150011140234037341)
            ·
              refine ⟨254619056254177587764003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 678984150011140234037341 254619056254177587764003)
              ·
                refine ⟨381928584381266381646005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 254619056254177587764003 381928584381266381646005)
                ·
                  refine ⟨35805804785743723279313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 381928584381266381646005 35805804785743723279313)
                  ·
                    rfl

theorem cell21_156896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 1, 5].length) (baseStart_156896 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_156896 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_156896 prefixEnd_156896 := by exact prefixLift 156896
  have htrace : WordTrace (prefixWord ++ tailWord_156896) baseStart_156896 baseEnd_156896 := by
    simpa [prefixWord, tailWord_156896, baseEnd_156896] using wordTrace_append hprefix tailTrace_156896
  have hstable : (prefixWord ++ tailWord_156896).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156896).length < 2 ^ (prefixWord ++ tailWord_156896).sum := by decide
  have hdescent : baseEnd_156896 < baseStart_156896 := by decide
  rcases family_descends (prefixWord ++ tailWord_156896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156941 : List Nat := [1, 7, 13]
def baseStart_156941 : Nat := 118140960795 + 156941 * 2 ^ 59
def prefixEnd_156941 : Nat := 4983230072969 + 3 ^ 40 * 156941 * 2
def baseEnd_156941 : Nat := 49130417556699101549

theorem tailTrace_156941 : CollatzResearch.WordTrace tailWord_156941 prefixEnd_156941 49130417556699101549 := by
  unfold tailWord_156941
  simp only [CollatzResearch.WordTrace]
  refine ⟨5724108524437035233982677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3816072349624690155988451 5724108524437035233982677)
  ·
    refine ⟨134158793541493013296469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 5724108524437035233982677 134158793541493013296469)
    ·
      refine ⟨49130417556699101549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 13 134158793541493013296469 49130417556699101549)
      ·
        rfl

theorem cell21_156941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 13].length) (baseStart_156941 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_156941 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_156941 prefixEnd_156941 := by exact prefixLift 156941
  have htrace : WordTrace (prefixWord ++ tailWord_156941) baseStart_156941 baseEnd_156941 := by
    simpa [prefixWord, tailWord_156941, baseEnd_156941] using wordTrace_append hprefix tailTrace_156941
  have hstable : (prefixWord ++ tailWord_156941).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156941).length < 2 ^ (prefixWord ++ tailWord_156941).sum := by decide
  have hdescent : baseEnd_156941 < baseStart_156941 := by decide
  rcases family_descends (prefixWord ++ tailWord_156941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156955 : List Nat := [1, 1, 1, 1, 1, 1, 5, 5, 5]
def baseStart_156955 : Nat := 118140960795 + 156955 * 2 ^ 59
def prefixEnd_156955 : Nat := 4983230072969 + 3 ^ 40 * 156955 * 2
def baseEnd_156955 : Nat := 35819269389572731795859

theorem tailTrace_156955 : CollatzResearch.WordTrace tailWord_156955 prefixEnd_156955 35819269389572731795859 := by
  unfold tailWord_156955
  simp only [CollatzResearch.WordTrace]
  refine ⟨5724619146386315624992319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3816412764257543749994879 5724619146386315624992319)
  ·
    refine ⟨8586928719579473437488479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5724619146386315624992319 8586928719579473437488479)
    ·
      refine ⟨12880393079369210156232719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8586928719579473437488479 12880393079369210156232719)
      ·
        refine ⟨19320589619053815234349079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12880393079369210156232719 19320589619053815234349079)
        ·
          refine ⟨28980884428580722851523619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19320589619053815234349079 28980884428580722851523619)
          ·
            refine ⟨43471326642871084277285429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28980884428580722851523619 43471326642871084277285429)
            ·
              refine ⟨4075436872769164150995509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43471326642871084277285429 4075436872769164150995509)
              ·
                refine ⟨382072206822109139155829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4075436872769164150995509 382072206822109139155829)
                ·
                  refine ⟨35819269389572731795859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 382072206822109139155829 35819269389572731795859)
                  ·
                    rfl

theorem cell21_156955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5, 5].length) (baseStart_156955 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_156955 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_156955 prefixEnd_156955 := by exact prefixLift 156955
  have htrace : WordTrace (prefixWord ++ tailWord_156955) baseStart_156955 baseEnd_156955 := by
    simpa [prefixWord, tailWord_156955, baseEnd_156955] using wordTrace_append hprefix tailTrace_156955
  have hstable : (prefixWord ++ tailWord_156955).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156955).length < 2 ^ (prefixWord ++ tailWord_156955).sum := by decide
  have hdescent : baseEnd_156955 < baseStart_156955 := by decide
  rcases family_descends (prefixWord ++ tailWord_156955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156986 : List Nat := [3, 1, 1, 1, 4, 1, 2, 2, 6]
def baseStart_156986 : Nat := 118140960795 + 156986 * 2 ^ 59
def prefixEnd_156986 : Nat := 4983230072969 + 3 ^ 40 * 156986 * 2
def baseEnd_156986 : Nat := 35826344011923566779129

theorem tailTrace_156986 : CollatzResearch.WordTrace tailWord_156986 prefixEnd_156986 35826344011923566779129 := by
  unfold tailWord_156986
  simp only [CollatzResearch.WordTrace]
  refine ⟨1431437452318501979842703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3817166539516005279580541 1431437452318501979842703)
  ·
    refine ⟨2147156178477752969764055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1431437452318501979842703 2147156178477752969764055)
    ·
      refine ⟨3220734267716629454646083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2147156178477752969764055 3220734267716629454646083)
      ·
        refine ⟨4831101401574944181969125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3220734267716629454646083 4831101401574944181969125)
        ·
          refine ⟨905831512795302034119211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4831101401574944181969125 905831512795302034119211)
          ·
            refine ⟨1358747269192953051178817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 905831512795302034119211 1358747269192953051178817)
            ·
              refine ⟨1019060451894714788384113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1358747269192953051178817 1019060451894714788384113)
              ·
                refine ⟨764295338921036091288085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1019060451894714788384113 764295338921036091288085)
                ·
                  refine ⟨35826344011923566779129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 764295338921036091288085 35826344011923566779129)
                  ·
                    rfl

theorem cell21_156986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 2, 6].length) (baseStart_156986 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_156986 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_156986 prefixEnd_156986 := by exact prefixLift 156986
  have htrace : WordTrace (prefixWord ++ tailWord_156986) baseStart_156986 baseEnd_156986 := by
    simpa [prefixWord, tailWord_156986, baseEnd_156986] using wordTrace_append hprefix tailTrace_156986
  have hstable : (prefixWord ++ tailWord_156986).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156986).length < 2 ^ (prefixWord ++ tailWord_156986).sum := by decide
  have hdescent : baseEnd_156986 < baseStart_156986 := by decide
  rcases family_descends (prefixWord ++ tailWord_156986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157034 : List Nat := [3, 1, 3, 3, 2, 1, 1, 7]
def baseStart_157034 : Nat := 118140960795 + 157034 * 2 ^ 59
def prefixEnd_157034 : Nat := 4983230072969 + 3 ^ 40 * 157034 * 2
def baseEnd_157034 : Nat := 11945766088628716659677

theorem tailTrace_157034 : CollatzResearch.WordTrace tailWord_157034 prefixEnd_157034 11945766088628716659677 := by
  unfold tailWord_157034
  simp only [CollatzResearch.WordTrace]
  refine ⟨1431875128275028029279539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3818333675400074744745437 1431875128275028029279539)
  ·
    refine ⟨2147812692412542043919309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1431875128275028029279539 2147812692412542043919309)
    ·
      refine ⟨805429759654703266469741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2147812692412542043919309 805429759654703266469741)
      ·
        refine ⟨302036159870513724926153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 805429759654703266469741 302036159870513724926153)
        ·
          refine ⟨226527119902885293694615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 302036159870513724926153 226527119902885293694615)
          ·
            refine ⟨339790679854327940541923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 226527119902885293694615 339790679854327940541923)
            ·
              refine ⟨509686019781491910812885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 339790679854327940541923 509686019781491910812885)
              ·
                refine ⟨11945766088628716659677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 509686019781491910812885 11945766088628716659677)
                ·
                  rfl

theorem cell21_157034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 7].length) (baseStart_157034 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_157034 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_157034 prefixEnd_157034 := by exact prefixLift 157034
  have htrace : WordTrace (prefixWord ++ tailWord_157034) baseStart_157034 baseEnd_157034 := by
    simpa [prefixWord, tailWord_157034, baseEnd_157034] using wordTrace_append hprefix tailTrace_157034
  have hstable : (prefixWord ++ tailWord_157034).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157034).length < 2 ^ (prefixWord ++ tailWord_157034).sum := by decide
  have hdescent : baseEnd_157034 < baseStart_157034 := by decide
  rcases family_descends (prefixWord ++ tailWord_157034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157065 : List Nat := [1, 2, 1, 1, 7, 2, 1, 1, 5]
def baseStart_157065 : Nat := 118140960795 + 157065 * 2 ^ 59
def prefixEnd_157065 : Nat := 4983230072969 + 3 ^ 40 * 157065 * 2
def baseEnd_157065 : Nat := 35844372888236984962301

theorem tailTrace_157065 : CollatzResearch.WordTrace tailWord_157065 prefixEnd_157065 35844372888236984962301 := by
  unfold tailWord_157065
  simp only [CollatzResearch.WordTrace]
  refine ⟨5728631175987804411496649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3819087450658536274331099 5728631175987804411496649)
  ·
    refine ⟨4296473381990853308622487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5728631175987804411496649 4296473381990853308622487)
    ·
      refine ⟨6444710072986279962933731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4296473381990853308622487 6444710072986279962933731)
      ·
        refine ⟨9667065109479419944400597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6444710072986279962933731 9667065109479419944400597)
        ·
          refine ⟨226571838503423904946889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 9667065109479419944400597 226571838503423904946889)
          ·
            refine ⟨169928878877567928710167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 226571838503423904946889 169928878877567928710167)
            ·
              refine ⟨254893318316351893065251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 169928878877567928710167 254893318316351893065251)
              ·
                refine ⟨382339977474527839597877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 254893318316351893065251 382339977474527839597877)
                ·
                  refine ⟨35844372888236984962301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 382339977474527839597877 35844372888236984962301)
                  ·
                    rfl

theorem cell21_157065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 1, 5].length) (baseStart_157065 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_157065 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_157065 prefixEnd_157065 := by exact prefixLift 157065
  have htrace : WordTrace (prefixWord ++ tailWord_157065) baseStart_157065 baseEnd_157065 := by
    simpa [prefixWord, tailWord_157065, baseEnd_157065] using wordTrace_append hprefix tailTrace_157065
  have hstable : (prefixWord ++ tailWord_157065).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157065).length < 2 ^ (prefixWord ++ tailWord_157065).sum := by decide
  have hdescent : baseEnd_157065 < baseStart_157065 := by decide
  rcases family_descends (prefixWord ++ tailWord_157065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157116 : List Nat := [2, 2, 2, 4, 3, 1, 2, 2, 3]
def baseStart_157116 : Nat := 118140960795 + 157116 * 2 ^ 59
def prefixEnd_157116 : Nat := 4983230072969 + 3 ^ 40 * 157116 * 2
def baseEnd_157116 : Nat := 35856011783072229612197

theorem tailTrace_157116 : CollatzResearch.WordTrace tailWord_157116 prefixEnd_157116 35856011783072229612197 := by
  unfold tailWord_157116
  simp only [CollatzResearch.WordTrace]
  refine ⟨2865245649401520060801601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3820327532535360081068801 2865245649401520060801601)
  ·
    refine ⟨2148934237051140045601201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2865245649401520060801601 2148934237051140045601201)
    ·
      refine ⟨1611700677788355034200901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2148934237051140045601201 1611700677788355034200901)
      ·
        refine ⟨302193877085316568912669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1611700677788355034200901 302193877085316568912669)
        ·
          refine ⟨113322703906993713342251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 302193877085316568912669 113322703906993713342251)
          ·
            refine ⟨169984055860490570013377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113322703906993713342251 169984055860490570013377)
            ·
              refine ⟨127488041895367927510033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 169984055860490570013377 127488041895367927510033)
              ·
                refine ⟨95616031421525945632525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 127488041895367927510033 95616031421525945632525)
                ·
                  refine ⟨35856011783072229612197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 95616031421525945632525 35856011783072229612197)
                  ·
                    rfl

theorem cell21_157116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 2, 2, 3].length) (baseStart_157116 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_157116 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_157116 prefixEnd_157116 := by exact prefixLift 157116
  have htrace : WordTrace (prefixWord ++ tailWord_157116) baseStart_157116 baseEnd_157116 := by
    simpa [prefixWord, tailWord_157116, baseEnd_157116] using wordTrace_append hprefix tailTrace_157116
  have hstable : (prefixWord ++ tailWord_157116).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157116).length < 2 ^ (prefixWord ++ tailWord_157116).sum := by decide
  have hdescent : baseEnd_157116 < baseStart_157116 := by decide
  rcases family_descends (prefixWord ++ tailWord_157116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157217 : List Nat := [1, 2, 3, 2, 2, 2, 3, 3, 3]
def baseStart_157217 : Nat := 118140960795 + 157217 * 2 ^ 59
def prefixEnd_157217 : Nat := 4983230072969 + 3 ^ 40 * 157217 * 2
def baseEnd_157217 : Nat := 35879061359118498428657

theorem tailTrace_157217 : CollatzResearch.WordTrace tailWord_157217 prefixEnd_157217 35879061359118498428657 := by
  unfold tailWord_157217
  simp only [CollatzResearch.WordTrace]
  refine ⟨5734175071437134371029905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3822783380958089580686603 5734175071437134371029905)
  ·
    refine ⟨4300631303577850778272429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5734175071437134371029905 4300631303577850778272429)
    ·
      refine ⟨1612736738841694041852161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4300631303577850778272429 1612736738841694041852161)
      ·
        refine ⟨1209552554131270531389121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1612736738841694041852161 1209552554131270531389121)
        ·
          refine ⟨907164415598452898541841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1209552554131270531389121 907164415598452898541841)
          ·
            refine ⟨680373311698839673906381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 907164415598452898541841 680373311698839673906381)
            ·
              refine ⟨255139991887064877714893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 680373311698839673906381 255139991887064877714893)
              ·
                refine ⟨95677496957649329143085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 255139991887064877714893 95677496957649329143085)
                ·
                  refine ⟨35879061359118498428657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 95677496957649329143085 35879061359118498428657)
                  ·
                    rfl

theorem cell21_157217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 3, 3].length) (baseStart_157217 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_157217 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_157217 prefixEnd_157217 := by exact prefixLift 157217
  have htrace : WordTrace (prefixWord ++ tailWord_157217) baseStart_157217 baseEnd_157217 := by
    simpa [prefixWord, tailWord_157217, baseEnd_157217] using wordTrace_append hprefix tailTrace_157217
  have hstable : (prefixWord ++ tailWord_157217).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157217).length < 2 ^ (prefixWord ++ tailWord_157217).sum := by decide
  have hdescent : baseEnd_157217 < baseStart_157217 := by decide
  rcases family_descends (prefixWord ++ tailWord_157217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157273 : List Nat := [1, 2, 1, 2, 2, 1, 1, 3, 8]
def baseStart_157273 : Nat := 118140960795 + 157273 * 2 ^ 59
def prefixEnd_157273 : Nat := 4983230072969 + 3 ^ 40 * 157273 * 2
def baseEnd_157273 : Nat := 35891841322074845495209

theorem tailTrace_157273 : CollatzResearch.WordTrace tailWord_157273 prefixEnd_157273 35891841322074845495209 := by
  unfold tailWord_157273
  simp only [CollatzResearch.WordTrace]
  refine ⟨5736217559234255935068473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3824145039489503956712315 5736217559234255935068473)
  ·
    refine ⟨4302163169425691951301355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5736217559234255935068473 4302163169425691951301355)
    ·
      refine ⟨6453244754138537926952033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4302163169425691951301355 6453244754138537926952033)
      ·
        refine ⟨4839933565603903445214025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6453244754138537926952033 4839933565603903445214025)
        ·
          refine ⟨3629950174202927583910519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4839933565603903445214025 3629950174202927583910519)
          ·
            refine ⟨5444925261304391375865779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3629950174202927583910519 5444925261304391375865779)
            ·
              refine ⟨8167387891956587063798669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5444925261304391375865779 8167387891956587063798669)
              ·
                refine ⟨3062770459483720148924501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8167387891956587063798669 3062770459483720148924501)
                ·
                  refine ⟨35891841322074845495209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3062770459483720148924501 35891841322074845495209)
                  ·
                    rfl

theorem cell21_157273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 8].length) (baseStart_157273 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_157273 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_157273 prefixEnd_157273 := by exact prefixLift 157273
  have htrace : WordTrace (prefixWord ++ tailWord_157273) baseStart_157273 baseEnd_157273 := by
    simpa [prefixWord, tailWord_157273, baseEnd_157273] using wordTrace_append hprefix tailTrace_157273
  have hstable : (prefixWord ++ tailWord_157273).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157273).length < 2 ^ (prefixWord ++ tailWord_157273).sum := by decide
  have hdescent : baseEnd_157273 < baseStart_157273 := by decide
  rcases family_descends (prefixWord ++ tailWord_157273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157386 : List Nat := [3, 1, 2, 1, 5, 2, 1, 3, 3]
def baseStart_157386 : Nat := 118140960795 + 157386 * 2 ^ 59
def prefixEnd_157386 : Nat := 4983230072969 + 3 ^ 40 * 157386 * 2
def baseEnd_157386 : Nat := 35917629461611760111645

theorem tailTrace_157386 : CollatzResearch.WordTrace tailWord_157386 prefixEnd_157386 35917629461611760111645 := by
  unfold tailWord_157386
  simp only [CollatzResearch.WordTrace]
  refine ⟨1435084751956219058483003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3826892671883250822621341 1435084751956219058483003)
  ·
    refine ⟨2152627127934328587724505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1435084751956219058483003 2152627127934328587724505)
    ·
      refine ⟨1614470345950746440793379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2152627127934328587724505 1614470345950746440793379)
      ·
        refine ⟨2421705518926119661190069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1614470345950746440793379 2421705518926119661190069)
        ·
          refine ⟨227034892399323718236569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2421705518926119661190069 227034892399323718236569)
          ·
            refine ⟨170276169299492788677427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 227034892399323718236569 170276169299492788677427)
            ·
              refine ⟨255414253949239183016141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170276169299492788677427 255414253949239183016141)
              ·
                refine ⟨95780345230964693631053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 255414253949239183016141 95780345230964693631053)
                ·
                  refine ⟨35917629461611760111645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 95780345230964693631053 35917629461611760111645)
                  ·
                    rfl

theorem cell21_157386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 3, 3].length) (baseStart_157386 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_157386 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_157386 prefixEnd_157386 := by exact prefixLift 157386
  have htrace : WordTrace (prefixWord ++ tailWord_157386) baseStart_157386 baseEnd_157386 := by
    simpa [prefixWord, tailWord_157386, baseEnd_157386] using wordTrace_append hprefix tailTrace_157386
  have hstable : (prefixWord ++ tailWord_157386).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157386).length < 2 ^ (prefixWord ++ tailWord_157386).sum := by decide
  have hdescent : baseEnd_157386 < baseStart_157386 := by decide
  rcases family_descends (prefixWord ++ tailWord_157386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157473 : List Nat := [1, 2, 3, 2, 1, 5, 1, 6]
def baseStart_157473 : Nat := 118140960795 + 157473 * 2 ^ 59
def prefixEnd_157473 : Nat := 4983230072969 + 3 ^ 40 * 157473 * 2
def baseEnd_157473 : Nat := 11979161348972980720489

theorem tailTrace_157473 : CollatzResearch.WordTrace tailWord_157473 prefixEnd_157473 11979161348972980720489 := by
  unfold tailWord_157473
  simp only [CollatzResearch.WordTrace]
  refine ⟨5743512158509690092349073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3829008105673126728232715 5743512158509690092349073)
  ·
    refine ⟨4307634118882267569261805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5743512158509690092349073 4307634118882267569261805)
    ·
      refine ⟨1615362794580850338473177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4307634118882267569261805 1615362794580850338473177)
      ·
        refine ⟨1211522095935637753854883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1615362794580850338473177 1211522095935637753854883)
        ·
          refine ⟨1817283143903456630782325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1211522095935637753854883 1817283143903456630782325)
          ·
            refine ⟨170370294740949059135843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1817283143903456630782325 170370294740949059135843)
            ·
              refine ⟨255555442111423588703765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170370294740949059135843 255555442111423588703765)
              ·
                refine ⟨11979161348972980720489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 255555442111423588703765 11979161348972980720489)
                ·
                  rfl

theorem cell21_157473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 6].length) (baseStart_157473 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_157473 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_157473 prefixEnd_157473 := by exact prefixLift 157473
  have htrace : WordTrace (prefixWord ++ tailWord_157473) baseStart_157473 baseEnd_157473 := by
    simpa [prefixWord, tailWord_157473, baseEnd_157473] using wordTrace_append hprefix tailTrace_157473
  have hstable : (prefixWord ++ tailWord_157473).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157473).length < 2 ^ (prefixWord ++ tailWord_157473).sum := by decide
  have hdescent : baseEnd_157473 < baseStart_157473 := by decide
  rcases family_descends (prefixWord ++ tailWord_157473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157535 : List Nat := [1, 1, 2, 3, 1, 5, 3, 1, 4]
def baseStart_157535 : Nat := 118140960795 + 157535 * 2 ^ 59
def prefixEnd_157535 : Nat := 4983230072969 + 3 ^ 40 * 157535 * 2
def baseEnd_157535 : Nat := 35951633291620612128007

theorem tailTrace_157535 : CollatzResearch.WordTrace tailWord_157535 prefixEnd_157535 35951633291620612128007 := by
  unfold tailWord_157535
  simp only [CollatzResearch.WordTrace]
  refine ⟨5745773484285074681106059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3830515656190049787404039 5745773484285074681106059)
  ·
    refine ⟨8618660226427612021659089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5745773484285074681106059 8618660226427612021659089)
    ·
      refine ⟨6463995169820709016244317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8618660226427612021659089 6463995169820709016244317)
      ·
        refine ⟨2423998188682765881091619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6463995169820709016244317 2423998188682765881091619)
        ·
          refine ⟨3635997283024148821637429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2423998188682765881091619 3635997283024148821637429)
          ·
            refine ⟨340874745283513952028509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3635997283024148821637429 340874745283513952028509)
            ·
              refine ⟨127828029481317732010691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 340874745283513952028509 127828029481317732010691)
              ·
                refine ⟨191742044221976598016037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 127828029481317732010691 191742044221976598016037)
                ·
                  refine ⟨35951633291620612128007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 191742044221976598016037 35951633291620612128007)
                  ·
                    rfl

theorem cell21_157535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 3, 1, 4].length) (baseStart_157535 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_157535 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_157535 prefixEnd_157535 := by exact prefixLift 157535
  have htrace : WordTrace (prefixWord ++ tailWord_157535) baseStart_157535 baseEnd_157535 := by
    simpa [prefixWord, tailWord_157535, baseEnd_157535] using wordTrace_append hprefix tailTrace_157535
  have hstable : (prefixWord ++ tailWord_157535).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157535).length < 2 ^ (prefixWord ++ tailWord_157535).sum := by decide
  have hdescent : baseEnd_157535 < baseStart_157535 := by decide
  rcases family_descends (prefixWord ++ tailWord_157535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157549 : List Nat := [1, 5, 1, 1, 1, 1, 6, 5]
def baseStart_157549 : Nat := 118140960795 + 157549 * 2 ^ 59
def prefixEnd_157549 : Nat := 4983230072969 + 3 ^ 40 * 157549 * 2
def baseEnd_157549 : Nat := 11984942760786566298215

theorem tailTrace_157549 : CollatzResearch.WordTrace tailWord_157549 prefixEnd_157549 11984942760786566298215 := by
  unfold tailWord_157549
  simp only [CollatzResearch.WordTrace]
  refine ⟨5746284106234355072115701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3830856070822903381410467 5746284106234355072115701)
  ·
    refine ⟨538714134959470788010847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5746284106234355072115701 538714134959470788010847)
    ·
      refine ⟨808071202439206182016271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 538714134959470788010847 808071202439206182016271)
      ·
        refine ⟨1212106803658809273024407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 808071202439206182016271 1212106803658809273024407)
        ·
          refine ⟨1818160205488213909536611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1212106803658809273024407 1818160205488213909536611)
          ·
            refine ⟨2727240308232320864304917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1818160205488213909536611 2727240308232320864304917)
            ·
              refine ⟨127839389448390040514293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2727240308232320864304917 127839389448390040514293)
              ·
                refine ⟨11984942760786566298215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 127839389448390040514293 11984942760786566298215)
                ·
                  rfl

theorem cell21_157549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 6, 5].length) (baseStart_157549 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_157549 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_157549 prefixEnd_157549 := by exact prefixLift 157549
  have htrace : WordTrace (prefixWord ++ tailWord_157549) baseStart_157549 baseEnd_157549 := by
    simpa [prefixWord, tailWord_157549, baseEnd_157549] using wordTrace_append hprefix tailTrace_157549
  have hstable : (prefixWord ++ tailWord_157549).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157549).length < 2 ^ (prefixWord ++ tailWord_157549).sum := by decide
  have hdescent : baseEnd_157549 < baseStart_157549 := by decide
  rcases family_descends (prefixWord ++ tailWord_157549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157566 : List Nat := [4, 2, 3, 1, 1, 3, 7]
def baseStart_157566 : Nat := 118140960795 + 157566 * 2 ^ 59
def prefixEnd_157566 : Nat := 4983230072969 + 3 ^ 40 * 157566 * 2
def baseEnd_157566 : Nat := 3995411990441271901253

theorem tailTrace_157566 : CollatzResearch.WordTrace tailWord_157566 prefixEnd_157566 3995411990441271901253 := by
  unfold tailWord_157566
  simp only [CollatzResearch.WordTrace]
  refine ⟨718363018396595871935569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3831269431448511316989701 718363018396595871935569)
  ·
    refine ⟨538772263797446903951677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 718363018396595871935569 538772263797446903951677)
    ·
      refine ⟨202039598924042588981879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 538772263797446903951677 202039598924042588981879)
      ·
        refine ⟨303059398386063883472819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202039598924042588981879 303059398386063883472819)
        ·
          refine ⟨454589097579095825209229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 303059398386063883472819 454589097579095825209229)
          ·
            refine ⟨170470911592160934453461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 454589097579095825209229 170470911592160934453461)
            ·
              refine ⟨3995411990441271901253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 170470911592160934453461 3995411990441271901253)
              ·
                rfl

theorem cell21_157566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 7].length) (baseStart_157566 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_157566 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_157566 prefixEnd_157566 := by exact prefixLift 157566
  have htrace : WordTrace (prefixWord ++ tailWord_157566) baseStart_157566 baseEnd_157566 := by
    simpa [prefixWord, tailWord_157566, baseEnd_157566] using wordTrace_append hprefix tailTrace_157566
  have hstable : (prefixWord ++ tailWord_157566).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157566).length < 2 ^ (prefixWord ++ tailWord_157566).sum := by decide
  have hdescent : baseEnd_157566 < baseStart_157566 := by decide
  rcases family_descends (prefixWord ++ tailWord_157566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157577 : List Nat := [1, 2, 1, 1, 5, 1, 1, 3, 6]
def baseStart_157577 : Nat := 118140960795 + 157577 * 2 ^ 59
def prefixEnd_157577 : Nat := 4983230072969 + 3 ^ 40 * 157577 * 2
def baseEnd_157577 : Nat := 35961218263837872427921

theorem tailTrace_157577 : CollatzResearch.WordTrace tailWord_157577 prefixEnd_157577 35961218263837872427921 := by
  unfold tailWord_157577
  simp only [CollatzResearch.WordTrace]
  refine ⟨5747305350132915854134985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3831536900088610569423323 5747305350132915854134985)
  ·
    refine ⟨4310479012599686890601239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5747305350132915854134985 4310479012599686890601239)
    ·
      refine ⟨6465718518899530335901859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4310479012599686890601239 6465718518899530335901859)
      ·
        refine ⟨9698577778349295503852789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6465718518899530335901859 9698577778349295503852789)
        ·
          refine ⟨909241666720246453486199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9698577778349295503852789 909241666720246453486199)
          ·
            refine ⟨1363862500080369680229299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 909241666720246453486199 1363862500080369680229299)
            ·
              refine ⟨2045793750120554520343949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1363862500080369680229299 2045793750120554520343949)
              ·
                refine ⟨767172656295207945128981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2045793750120554520343949 767172656295207945128981)
                ·
                  refine ⟨35961218263837872427921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 767172656295207945128981 35961218263837872427921)
                  ·
                    rfl

theorem cell21_157577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 3, 6].length) (baseStart_157577 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_157577 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_157577 prefixEnd_157577 := by exact prefixLift 157577
  have htrace : WordTrace (prefixWord ++ tailWord_157577) baseStart_157577 baseEnd_157577 := by
    simpa [prefixWord, tailWord_157577, baseEnd_157577] using wordTrace_append hprefix tailTrace_157577
  have hstable : (prefixWord ++ tailWord_157577).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157577).length < 2 ^ (prefixWord ++ tailWord_157577).sum := by decide
  have hdescent : baseEnd_157577 < baseStart_157577 := by decide
  rcases family_descends (prefixWord ++ tailWord_157577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157628 : List Nat := [2, 2, 2, 5, 1, 1, 2, 2, 4]
def baseStart_157628 : Nat := 118140960795 + 157628 * 2 ^ 59
def prefixEnd_157628 : Nat := 4983230072969 + 3 ^ 40 * 157628 * 2
def baseEnd_157628 : Nat := 35972857158673117077817

theorem tailTrace_157628 : CollatzResearch.WordTrace tailWord_157628 prefixEnd_157628 35972857158673117077817 := by
  unfold tailWord_157628
  simp only [CollatzResearch.WordTrace]
  refine ⟨2874582736474075782120769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3832776981965434376161025 2874582736474075782120769)
  ·
    refine ⟨2155937052355556836590577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2874582736474075782120769 2155937052355556836590577)
    ·
      refine ⟨1616952789266667627442933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2155937052355556836590577 1616952789266667627442933)
      ·
        refine ⟨151589323993750090072775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1616952789266667627442933 151589323993750090072775)
        ·
          refine ⟨227383985990625135109163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151589323993750090072775 227383985990625135109163)
          ·
            refine ⟨341075978985937702663745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227383985990625135109163 341075978985937702663745)
            ·
              refine ⟨255806984239453276997809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 341075978985937702663745 255806984239453276997809)
              ·
                refine ⟨191855238179589957748357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 255806984239453276997809 191855238179589957748357)
                ·
                  refine ⟨35972857158673117077817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 191855238179589957748357 35972857158673117077817)
                  ·
                    rfl

theorem cell21_157628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 2, 4].length) (baseStart_157628 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_157628 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_157628 prefixEnd_157628 := by exact prefixLift 157628
  have htrace : WordTrace (prefixWord ++ tailWord_157628) baseStart_157628 baseEnd_157628 := by
    simpa [prefixWord, tailWord_157628, baseEnd_157628] using wordTrace_append hprefix tailTrace_157628
  have hstable : (prefixWord ++ tailWord_157628).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157628).length < 2 ^ (prefixWord ++ tailWord_157628).sum := by decide
  have hdescent : baseEnd_157628 < baseStart_157628 := by decide
  rcases family_descends (prefixWord ++ tailWord_157628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157760 : List Nat := [2, 1, 1, 2, 2, 5, 2, 6]
def baseStart_157760 : Nat := 118140960795 + 157760 * 2 ^ 59
def prefixEnd_157760 : Nat := 4983230072969 + 3 ^ 40 * 157760 * 2
def baseEnd_157760 : Nat := 12000993785690073625849

theorem tailTrace_157760 : CollatzResearch.WordTrace tailWord_157760 prefixEnd_157760 12000993785690073625849 := by
  unfold tailWord_157760
  simp only [CollatzResearch.WordTrace]
  refine ⟨2876989954234969054023367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3835986605646625405364489 2876989954234969054023367)
  ·
    refine ⟨4315484931352453581035051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2876989954234969054023367 4315484931352453581035051)
    ·
      refine ⟨6473227397028680371552577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4315484931352453581035051 6473227397028680371552577)
      ·
        refine ⟨4854920547771510278664433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6473227397028680371552577 4854920547771510278664433)
        ·
          refine ⟨3641190410828632708998325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4854920547771510278664433 3641190410828632708998325)
          ·
            refine ⟨341361601015184316468593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3641190410828632708998325 341361601015184316468593)
            ·
              refine ⟨256021200761388237351445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 341361601015184316468593 256021200761388237351445)
              ·
                refine ⟨12000993785690073625849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 256021200761388237351445 12000993785690073625849)
                ·
                  rfl

theorem cell21_157760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 6].length) (baseStart_157760 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_157760 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_157760 prefixEnd_157760 := by exact prefixLift 157760
  have htrace : WordTrace (prefixWord ++ tailWord_157760) baseStart_157760 baseEnd_157760 := by
    simpa [prefixWord, tailWord_157760, baseEnd_157760] using wordTrace_append hprefix tailTrace_157760
  have hstable : (prefixWord ++ tailWord_157760).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157760).length < 2 ^ (prefixWord ++ tailWord_157760).sum := by decide
  have hdescent : baseEnd_157760 < baseStart_157760 := by decide
  rcases family_descends (prefixWord ++ tailWord_157760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157808 : List Nat := [2, 1, 1, 1, 5, 3, 1, 4, 3]
def baseStart_157808 : Nat := 118140960795 + 157808 * 2 ^ 59
def prefixEnd_157808 : Nat := 4983230072969 + 3 ^ 40 * 157808 * 2
def baseEnd_157808 : Nat := 36013935611032804077449

theorem tailTrace_157808 : CollatzResearch.WordTrace tailWord_157808 prefixEnd_157808 36013935611032804077449 := by
  unfold tailWord_157808
  simp only [CollatzResearch.WordTrace]
  refine ⟨2877865306148021152897039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3837153741530694870529385 2877865306148021152897039)
  ·
    refine ⟨4316797959222031729345559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2877865306148021152897039 4316797959222031729345559)
    ·
      refine ⟨6475196938833047594018339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4316797959222031729345559 6475196938833047594018339)
      ·
        refine ⟨9712795408249571391027509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6475196938833047594018339 9712795408249571391027509)
        ·
          refine ⟨910574569523397317908829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9712795408249571391027509 910574569523397317908829)
          ·
            refine ⟨341465463571273994215811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 910574569523397317908829 341465463571273994215811)
            ·
              refine ⟨512198195356910991323717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 341465463571273994215811 512198195356910991323717)
              ·
                refine ⟨96037161629420810873197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 512198195356910991323717 96037161629420810873197)
                ·
                  refine ⟨36013935611032804077449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 96037161629420810873197 36013935611032804077449)
                  ·
                    rfl

theorem cell21_157808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 4, 3].length) (baseStart_157808 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_157808 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_157808 prefixEnd_157808 := by exact prefixLift 157808
  have htrace : WordTrace (prefixWord ++ tailWord_157808) baseStart_157808 baseEnd_157808 := by
    simpa [prefixWord, tailWord_157808, baseEnd_157808] using wordTrace_append hprefix tailTrace_157808
  have hstable : (prefixWord ++ tailWord_157808).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157808).length < 2 ^ (prefixWord ++ tailWord_157808).sum := by decide
  have hdescent : baseEnd_157808 < baseStart_157808 := by decide
  rcases family_descends (prefixWord ++ tailWord_157808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157912 : List Nat := [2, 1, 2, 2, 4, 3, 7]
def baseStart_157912 : Nat := 118140960795 + 157912 * 2 ^ 59
def prefixEnd_157912 : Nat := 4983230072969 + 3 ^ 40 * 157912 * 2
def baseEnd_157912 : Nat := 4004185536439081593767

theorem tailTrace_157912 : CollatzResearch.WordTrace tailWord_157912 prefixEnd_157912 4004185536439081593767 := by
  unfold tailWord_157912
  simp only [CollatzResearch.WordTrace]
  refine ⟨2879761901959634033789995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3839682535946178711719993 2879761901959634033789995)
  ·
    refine ⟨4319642852939451050684993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2879761901959634033789995 4319642852939451050684993)
    ·
      refine ⟨3239732139704588288013745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4319642852939451050684993 3239732139704588288013745)
      ·
        refine ⟨2429799104778441216010309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3239732139704588288013745 2429799104778441216010309)
        ·
          refine ⟨455587332145957728001933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2429799104778441216010309 455587332145957728001933)
          ·
            refine ⟨170845249554734148000725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 455587332145957728001933 170845249554734148000725)
            ·
              refine ⟨4004185536439081593767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 170845249554734148000725 4004185536439081593767)
              ·
                rfl

theorem cell21_157912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 7].length) (baseStart_157912 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_157912 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_157912 prefixEnd_157912 := by exact prefixLift 157912
  have htrace : WordTrace (prefixWord ++ tailWord_157912) baseStart_157912 baseEnd_157912 := by
    simpa [prefixWord, tailWord_157912, baseEnd_157912] using wordTrace_append hprefix tailTrace_157912
  have hstable : (prefixWord ++ tailWord_157912).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157912).length < 2 ^ (prefixWord ++ tailWord_157912).sum := by decide
  have hdescent : baseEnd_157912 < baseStart_157912 := by decide
  rcases family_descends (prefixWord ++ tailWord_157912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157988 : List Nat := [2, 3, 1, 3, 1, 2, 3, 6]
def baseStart_157988 : Nat := 118140960795 + 157988 * 2 ^ 59
def prefixEnd_157988 : Nat := 4983230072969 + 3 ^ 40 * 157988 * 2
def baseEnd_157988 : Nat := 12018338021130830359027

theorem tailTrace_157988 : CollatzResearch.WordTrace tailWord_157988 prefixEnd_157988 12018338021130830359027 := by
  unfold tailWord_157988
  simp only [CollatzResearch.WordTrace]
  refine ⟨2881147875821966523673309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3841530501095955364897745 2881147875821966523673309)
  ·
    refine ⟨1080430453433237446377491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2881147875821966523673309 1080430453433237446377491)
    ·
      refine ⟨1620645680149856169566237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1080430453433237446377491 1620645680149856169566237)
      ·
        refine ⟨607742130056196063587339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1620645680149856169566237 607742130056196063587339)
        ·
          refine ⟨911613195084294095381009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 607742130056196063587339 911613195084294095381009)
          ·
            refine ⟨683709896313220571535757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 911613195084294095381009 683709896313220571535757)
            ·
              refine ⟨256391211117457714325909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 683709896313220571535757 256391211117457714325909)
              ·
                refine ⟨12018338021130830359027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 256391211117457714325909 12018338021130830359027)
                ·
                  rfl

theorem cell21_157988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 6].length) (baseStart_157988 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_157988 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_157988 prefixEnd_157988 := by exact prefixLift 157988
  have htrace : WordTrace (prefixWord ++ tailWord_157988) baseStart_157988 baseEnd_157988 := by
    simpa [prefixWord, tailWord_157988, baseEnd_157988] using wordTrace_append hprefix tailTrace_157988
  have hstable : (prefixWord ++ tailWord_157988).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157988).length < 2 ^ (prefixWord ++ tailWord_157988).sum := by decide
  have hdescent : baseEnd_157988 < baseStart_157988 := by decide
  rcases family_descends (prefixWord ++ tailWord_157988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158019 : List Nat := [1, 1, 1, 3, 1, 3, 3, 5, 3]
def baseStart_158019 : Nat := 118140960795 + 158019 * 2 ^ 59
def prefixEnd_158019 : Nat := 4983230072969 + 3 ^ 40 * 158019 * 2
def baseEnd_158019 : Nat := 36062088685743326060351

theorem tailTrace_158019 : CollatzResearch.WordTrace tailWord_158019 prefixEnd_158019 36062088685743326060351 := by
  unfold tailWord_158019
  simp only [CollatzResearch.WordTrace]
  refine ⟨5763426414531625341725111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3842284276354416894483407 5763426414531625341725111)
  ·
    refine ⟨8645139621797438012587667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5763426414531625341725111 8645139621797438012587667)
    ·
      refine ⟨12967709432696157018881501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8645139621797438012587667 12967709432696157018881501)
      ·
        refine ⟨4862891037261058882080563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12967709432696157018881501 4862891037261058882080563)
        ·
          refine ⟨7294336555891588323120845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4862891037261058882080563 7294336555891588323120845)
          ·
            refine ⟨2735376208459345621170317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7294336555891588323120845 2735376208459345621170317)
            ·
              refine ⟨1025766078172254607938869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2735376208459345621170317 1025766078172254607938869)
              ·
                refine ⟨96165569828648869494269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1025766078172254607938869 96165569828648869494269)
                ·
                  refine ⟨36062088685743326060351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 96165569828648869494269 36062088685743326060351)
                  ·
                    rfl

theorem cell21_158019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 5, 3].length) (baseStart_158019 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_158019 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_158019 prefixEnd_158019 := by exact prefixLift 158019
  have htrace : WordTrace (prefixWord ++ tailWord_158019) baseStart_158019 baseEnd_158019 := by
    simpa [prefixWord, tailWord_158019, baseEnd_158019] using wordTrace_append hprefix tailTrace_158019
  have hstable : (prefixWord ++ tailWord_158019).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158019).length < 2 ^ (prefixWord ++ tailWord_158019).sum := by decide
  have hdescent : baseEnd_158019 < baseStart_158019 := by decide
  rcases family_descends (prefixWord ++ tailWord_158019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158033 : List Nat := [1, 2, 2, 1, 4, 3, 1, 1, 6]
def baseStart_158033 : Nat := 118140960795 + 158033 * 2 ^ 59
def prefixEnd_158033 : Nat := 4983230072969 + 3 ^ 40 * 158033 * 2
def baseEnd_158033 : Nat := 36065283676482412826989

theorem tailTrace_158033 : CollatzResearch.WordTrace tailWord_158033 prefixEnd_158033 36065283676482412826989 := by
  unfold tailWord_158033
  simp only [CollatzResearch.WordTrace]
  refine ⟨5763937036480905732734753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3842624690987270488489835 5763937036480905732734753)
  ·
    refine ⟨4322952777360679299551065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5763937036480905732734753 4322952777360679299551065)
    ·
      refine ⟨3242214583020509474663299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4322952777360679299551065 3242214583020509474663299)
      ·
        refine ⟨4863321874530764211994949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3242214583020509474663299 4863321874530764211994949)
        ·
          refine ⟨911872851474518289749053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4863321874530764211994949 911872851474518289749053)
          ·
            refine ⟨341952319302944358655895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 911872851474518289749053 341952319302944358655895)
            ·
              refine ⟨512928478954416537983843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 341952319302944358655895 512928478954416537983843)
              ·
                refine ⟨769392718431624806975765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 512928478954416537983843 769392718431624806975765)
                ·
                  refine ⟨36065283676482412826989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 769392718431624806975765 36065283676482412826989)
                  ·
                    rfl

theorem cell21_158033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 1, 6].length) (baseStart_158033 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_158033 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_158033 prefixEnd_158033 := by exact prefixLift 158033
  have htrace : WordTrace (prefixWord ++ tailWord_158033) baseStart_158033 baseEnd_158033 := by
    simpa [prefixWord, tailWord_158033, baseEnd_158033] using wordTrace_append hprefix tailTrace_158033
  have hstable : (prefixWord ++ tailWord_158033).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158033).length < 2 ^ (prefixWord ++ tailWord_158033).sum := by decide
  have hdescent : baseEnd_158033 < baseStart_158033 := by decide
  rcases family_descends (prefixWord ++ tailWord_158033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158036 : List Nat := [2, 4, 1, 1, 2, 2, 2, 4, 3]
def baseStart_158036 : Nat := 118140960795 + 158036 * 2 ^ 59
def prefixEnd_158036 : Nat := 4983230072969 + 3 ^ 40 * 158036 * 2
def baseEnd_158036 : Nat := 36065968317355074276983

theorem tailTrace_158036 : CollatzResearch.WordTrace tailWord_158036 prefixEnd_158036 36065968317355074276983 := by
  unfold tailWord_158036
  simp only [CollatzResearch.WordTrace]
  refine ⟨2882023227735018622546981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3842697636980024830062641 2882023227735018622546981)
  ·
    refine ⟨540379355200315991727559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2882023227735018622546981 540379355200315991727559)
    ·
      refine ⟨810569032800473987591339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 540379355200315991727559 810569032800473987591339)
      ·
        refine ⟨1215853549200710981387009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 810569032800473987591339 1215853549200710981387009)
        ·
          refine ⟨911890161900533236040257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1215853549200710981387009 911890161900533236040257)
          ·
            refine ⟨683917621425399927030193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 911890161900533236040257 683917621425399927030193)
            ·
              refine ⟨512938216069049945272645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 683917621425399927030193 512938216069049945272645)
              ·
                refine ⟨96175915512946864738621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 512938216069049945272645 96175915512946864738621)
                ·
                  refine ⟨36065968317355074276983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 96175915512946864738621 36065968317355074276983)
                  ·
                    rfl

theorem cell21_158036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 4, 3].length) (baseStart_158036 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_158036 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_158036 prefixEnd_158036 := by exact prefixLift 158036
  have htrace : WordTrace (prefixWord ++ tailWord_158036) baseStart_158036 baseEnd_158036 := by
    simpa [prefixWord, tailWord_158036, baseEnd_158036] using wordTrace_append hprefix tailTrace_158036
  have hstable : (prefixWord ++ tailWord_158036).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158036).length < 2 ^ (prefixWord ++ tailWord_158036).sum := by decide
  have hdescent : baseEnd_158036 < baseStart_158036 := by decide
  rcases family_descends (prefixWord ++ tailWord_158036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158064 : List Nat := [2, 1, 1, 1, 4, 3, 4, 5]
def baseStart_158064 : Nat := 118140960795 + 158064 * 2 ^ 59
def prefixEnd_158064 : Nat := 4983230072969 + 3 ^ 40 * 158064 * 2
def baseEnd_158064 : Nat := 12024119432944415936753

theorem tailTrace_158064 : CollatzResearch.WordTrace tailWord_158064 prefixEnd_158064 12024119432944415936753 := by
  unfold tailWord_158064
  simp only [CollatzResearch.WordTrace]
  refine ⟨2882533849684299013556623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3843378466245732018075497 2882533849684299013556623)
  ·
    refine ⟨4323800774526448520334935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2882533849684299013556623 4323800774526448520334935)
    ·
      refine ⟨6485701161789672780502403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4323800774526448520334935 6485701161789672780502403)
      ·
        refine ⟨9728551742684509170753605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6485701161789672780502403 9728551742684509170753605)
        ·
          refine ⟨1824103451753345469516301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9728551742684509170753605 1824103451753345469516301)
          ·
            refine ⟨684038794407504551068613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1824103451753345469516301 684038794407504551068613)
            ·
              refine ⟨128257273951407103325365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 684038794407504551068613 128257273951407103325365)
              ·
                refine ⟨12024119432944415936753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 128257273951407103325365 12024119432944415936753)
                ·
                  rfl

theorem cell21_158064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 4, 5].length) (baseStart_158064 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_158064 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_158064 prefixEnd_158064 := by exact prefixLift 158064
  have htrace : WordTrace (prefixWord ++ tailWord_158064) baseStart_158064 baseEnd_158064 := by
    simpa [prefixWord, tailWord_158064, baseEnd_158064] using wordTrace_append hprefix tailTrace_158064
  have hstable : (prefixWord ++ tailWord_158064).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158064).length < 2 ^ (prefixWord ++ tailWord_158064).sum := by decide
  have hdescent : baseEnd_158064 < baseStart_158064 := by decide
  rcases family_descends (prefixWord ++ tailWord_158064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158154 : List Nat := [3, 1, 2, 1, 2, 2, 2, 3, 5]
def baseStart_158154 : Nat := 118140960795 + 158154 * 2 ^ 59
def prefixEnd_158154 : Nat := 4983230072969 + 3 ^ 40 * 158154 * 2
def baseEnd_158154 : Nat := 36092897525013091310075

theorem tailTrace_158154 : CollatzResearch.WordTrace tailWord_158154 prefixEnd_158154 36092897525013091310075 := by
  unfold tailWord_158154
  simp only [CollatzResearch.WordTrace]
  refine ⟨1442087567260635849472379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3845566846028362265259677 1442087567260635849472379)
  ·
    refine ⟨2163131350890953774208569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1442087567260635849472379 2163131350890953774208569)
    ·
      refine ⟨1622348513168215330656427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2163131350890953774208569 1622348513168215330656427)
      ·
        refine ⟨2433522769752322995984641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1622348513168215330656427 2433522769752322995984641)
        ·
          refine ⟨1825142077314242246988481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2433522769752322995984641 1825142077314242246988481)
          ·
            refine ⟨1368856557985681685241361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1825142077314242246988481 1368856557985681685241361)
            ·
              refine ⟨1026642418489261263931021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1368856557985681685241361 1026642418489261263931021)
              ·
                refine ⟨384990906933472973974133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1026642418489261263931021 384990906933472973974133)
                ·
                  refine ⟨36092897525013091310075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 384990906933472973974133 36092897525013091310075)
                  ·
                    rfl

theorem cell21_158154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 3, 5].length) (baseStart_158154 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_158154 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_158154 prefixEnd_158154 := by exact prefixLift 158154
  have htrace : WordTrace (prefixWord ++ tailWord_158154) baseStart_158154 baseEnd_158154 := by
    simpa [prefixWord, tailWord_158154, baseEnd_158154] using wordTrace_append hprefix tailTrace_158154
  have hstable : (prefixWord ++ tailWord_158154).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158154).length < 2 ^ (prefixWord ++ tailWord_158154).sum := by decide
  have hdescent : baseEnd_158154 < baseStart_158154 := by decide
  rcases family_descends (prefixWord ++ tailWord_158154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158168 : List Nat := [2, 1, 2, 2, 2, 1, 1, 2, 8]
def baseStart_158168 : Nat := 118140960795 + 158168 * 2 ^ 59
def prefixEnd_158168 : Nat := 4983230072969 + 3 ^ 40 * 158168 * 2
def baseEnd_158168 : Nat := 36096092515752178076713

theorem tailTrace_158168 : CollatzResearch.WordTrace tailWord_158168 prefixEnd_158168 36096092515752178076713 := by
  unfold tailWord_158168
  simp only [CollatzResearch.WordTrace]
  refine ⟨2884430445495911894449579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3845907260661215859266105 2884430445495911894449579)
  ·
    refine ⟨4326645668243867841674369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2884430445495911894449579 4326645668243867841674369)
    ·
      refine ⟨3244984251182900881255777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4326645668243867841674369 3244984251182900881255777)
      ·
        refine ⟨2433738188387175660941833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3244984251182900881255777 2433738188387175660941833)
        ·
          refine ⟨1825303641290381745706375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2433738188387175660941833 1825303641290381745706375)
          ·
            refine ⟨2737955461935572618559563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1825303641290381745706375 2737955461935572618559563)
            ·
              refine ⟨4106933192903358927839345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2737955461935572618559563 4106933192903358927839345)
              ·
                refine ⟨3080199894677519195879509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4106933192903358927839345 3080199894677519195879509)
                ·
                  refine ⟨36096092515752178076713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3080199894677519195879509 36096092515752178076713)
                  ·
                    rfl

theorem cell21_158168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 8].length) (baseStart_158168 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_158168 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_158168 prefixEnd_158168 := by exact prefixLift 158168
  have htrace : WordTrace (prefixWord ++ tailWord_158168) baseStart_158168 baseEnd_158168 := by
    simpa [prefixWord, tailWord_158168, baseEnd_158168] using wordTrace_append hprefix tailTrace_158168
  have hstable : (prefixWord ++ tailWord_158168).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158168).length < 2 ^ (prefixWord ++ tailWord_158168).sum := by decide
  have hdescent : baseEnd_158168 < baseStart_158168 := by decide
  rcases family_descends (prefixWord ++ tailWord_158168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158261 : List Nat := [1, 3, 3, 1, 1, 2, 2, 4, 4]
def baseStart_158261 : Nat := 118140960795 + 158261 * 2 ^ 59
def prefixEnd_158261 : Nat := 4983230072969 + 3 ^ 40 * 158261 * 2
def baseEnd_158261 : Nat := 36117316382804683026523

theorem tailTrace_158261 : CollatzResearch.WordTrace tailWord_158261 prefixEnd_158261 36117316382804683026523 := by
  unfold tailWord_158261
  simp only [CollatzResearch.WordTrace]
  refine ⟨5772252879654900672034637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3848168586436600448023091 5772252879654900672034637)
  ·
    refine ⟨2164594829870587752012989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5772252879654900672034637 2164594829870587752012989)
    ·
      refine ⟨811723061201470407004871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2164594829870587752012989 811723061201470407004871)
      ·
        refine ⟨1217584591802205610507307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 811723061201470407004871 1217584591802205610507307)
        ·
          refine ⟨1826376887703308415760961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1217584591802205610507307 1826376887703308415760961)
          ·
            refine ⟨1369782665777481311820721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1826376887703308415760961 1369782665777481311820721)
            ·
              refine ⟨1027336999333110983865541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1369782665777481311820721 1027336999333110983865541)
              ·
                refine ⟨192625687374958309474789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1027336999333110983865541 192625687374958309474789)
                ·
                  refine ⟨36117316382804683026523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 192625687374958309474789 36117316382804683026523)
                  ·
                    rfl

theorem cell21_158261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 4, 4].length) (baseStart_158261 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_158261 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_158261 prefixEnd_158261 := by exact prefixLift 158261
  have htrace : WordTrace (prefixWord ++ tailWord_158261) baseStart_158261 baseEnd_158261 := by
    simpa [prefixWord, tailWord_158261, baseEnd_158261] using wordTrace_append hprefix tailTrace_158261
  have hstable : (prefixWord ++ tailWord_158261).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158261).length < 2 ^ (prefixWord ++ tailWord_158261).sum := by decide
  have hdescent : baseEnd_158261 < baseStart_158261 := by decide
  rcases family_descends (prefixWord ++ tailWord_158261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158264 : List Nat := [2, 1, 2, 1, 4, 1, 5, 2, 3]
def baseStart_158264 : Nat := 118140960795 + 158264 * 2 ^ 59
def prefixEnd_158264 : Nat := 4983230072969 + 3 ^ 40 * 158264 * 2
def baseEnd_158264 : Nat := 36118001023677344476517

theorem tailTrace_158264 : CollatzResearch.WordTrace tailWord_158264 prefixEnd_158264 36118001023677344476517 := by
  unfold tailWord_158264
  simp only [CollatzResearch.WordTrace]
  refine ⟨2886181149322016092196923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3848241532429354789595897 2886181149322016092196923)
  ·
    refine ⟨4329271723983024138295385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2886181149322016092196923 4329271723983024138295385)
    ·
      refine ⟨3246953792987268103721539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4329271723983024138295385 3246953792987268103721539)
      ·
        refine ⟨4870430689480902155582309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3246953792987268103721539 4870430689480902155582309)
        ·
          refine ⟨913205754277669154171683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4870430689480902155582309 913205754277669154171683)
          ·
            refine ⟨1369808631416503731257525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 913205754277669154171683 1369808631416503731257525)
            ·
              refine ⟨128419559195297224805393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1369808631416503731257525 128419559195297224805393)
              ·
                refine ⟨96314669396472918604045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 128419559195297224805393 96314669396472918604045)
                ·
                  refine ⟨36118001023677344476517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 96314669396472918604045 36118001023677344476517)
                  ·
                    rfl

theorem cell21_158264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 5, 2, 3].length) (baseStart_158264 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_158264 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_158264 prefixEnd_158264 := by exact prefixLift 158264
  have htrace : WordTrace (prefixWord ++ tailWord_158264) baseStart_158264 baseEnd_158264 := by
    simpa [prefixWord, tailWord_158264, baseEnd_158264] using wordTrace_append hprefix tailTrace_158264
  have hstable : (prefixWord ++ tailWord_158264).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158264).length < 2 ^ (prefixWord ++ tailWord_158264).sum := by decide
  have hdescent : baseEnd_158264 < baseStart_158264 := by decide
  rcases family_descends (prefixWord ++ tailWord_158264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158326 : List Nat := [5, 1, 1, 2, 4, 1, 1, 6]
def baseStart_158326 : Nat := 118140960795 + 158326 * 2 ^ 59
def prefixEnd_158326 : Nat := 4983230072969 + 3 ^ 40 * 158326 * 2
def baseEnd_158326 : Nat := 12044050089459671481019

theorem tailTrace_158326 : CollatzResearch.WordTrace tailWord_158326 prefixEnd_158326 12044050089459671481019 := by
  unfold tailWord_158326
  simp only [CollatzResearch.WordTrace]
  refine ⟨360913976526213548321927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3849749082946277848767221 360913976526213548321927)
  ·
    refine ⟨541370964789320322482891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 360913976526213548321927 541370964789320322482891)
    ·
      refine ⟨812056447183980483724337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 541370964789320322482891 812056447183980483724337)
      ·
        refine ⟨609042335387985362793253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 812056447183980483724337 609042335387985362793253)
        ·
          refine ⟨114195437885247255523735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 609042335387985362793253 114195437885247255523735)
          ·
            refine ⟨171293156827870883285603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114195437885247255523735 171293156827870883285603)
            ·
              refine ⟨256939735241806324928405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 171293156827870883285603 256939735241806324928405)
              ·
                refine ⟨12044050089459671481019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 256939735241806324928405 12044050089459671481019)
                ·
                  rfl

theorem cell21_158326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 6].length) (baseStart_158326 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_158326 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_158326 prefixEnd_158326 := by exact prefixLift 158326
  have htrace : WordTrace (prefixWord ++ tailWord_158326) baseStart_158326 baseEnd_158326 := by
    simpa [prefixWord, tailWord_158326, baseEnd_158326] using wordTrace_append hprefix tailTrace_158326
  have hstable : (prefixWord ++ tailWord_158326).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158326).length < 2 ^ (prefixWord ++ tailWord_158326).sum := by decide
  have hdescent : baseEnd_158326 < baseStart_158326 := by decide
  rcases family_descends (prefixWord ++ tailWord_158326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158337 : List Nat := [1, 2, 4, 2, 1, 1, 1, 5, 4]
def baseStart_158337 : Nat := 118140960795 + 158337 * 2 ^ 59
def prefixEnd_158337 : Nat := 4983230072969 + 3 ^ 40 * 158337 * 2
def baseEnd_158337 : Nat := 36134660618245439759701

theorem tailTrace_158337 : CollatzResearch.WordTrace tailWord_158337 prefixEnd_158337 36134660618245439759701 := by
  unfold tailWord_158337
  simp only [CollatzResearch.WordTrace]
  refine ⟨5775024827379565651801265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3850016551586377101200843 5775024827379565651801265)
  ·
    refine ⟨4331268620534674238850949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5775024827379565651801265 4331268620534674238850949)
    ·
      refine ⟨812112866350251419784553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4331268620534674238850949 812112866350251419784553)
      ·
        refine ⟨609084649762688564838415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 812112866350251419784553 609084649762688564838415)
        ·
          refine ⟨913626974644032847257623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 609084649762688564838415 913626974644032847257623)
          ·
            refine ⟨1370440461966049270886435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 913626974644032847257623 1370440461966049270886435)
            ·
              refine ⟨2055660692949073906329653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1370440461966049270886435 2055660692949073906329653)
              ·
                refine ⟨192718189963975678718405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2055660692949073906329653 192718189963975678718405)
                ·
                  refine ⟨36134660618245439759701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 192718189963975678718405 36134660618245439759701)
                  ·
                    rfl

theorem cell21_158337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 5, 4].length) (baseStart_158337 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_158337 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_158337 prefixEnd_158337 := by exact prefixLift 158337
  have htrace : WordTrace (prefixWord ++ tailWord_158337) baseStart_158337 baseEnd_158337 := by
    simpa [prefixWord, tailWord_158337, baseEnd_158337] using wordTrace_append hprefix tailTrace_158337
  have hstable : (prefixWord ++ tailWord_158337).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158337).length < 2 ^ (prefixWord ++ tailWord_158337).sum := by decide
  have hdescent : baseEnd_158337 < baseStart_158337 := by decide
  rcases family_descends (prefixWord ++ tailWord_158337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158492 : List Nat := [2, 2, 3, 1, 1, 3, 4, 2, 3]
def baseStart_158492 : Nat := 118140960795 + 158492 * 2 ^ 59
def prefixEnd_158492 : Nat := 4983230072969 + 3 ^ 40 * 158492 * 2
def baseEnd_158492 : Nat := 36170033729999614676051

theorem tailTrace_158492 : CollatzResearch.WordTrace tailWord_158492 prefixEnd_158492 36170033729999614676051 := by
  unfold tailWord_158492
  simp only [CollatzResearch.WordTrace]
  refine ⟨2890339070909013561846865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3853785427878684749129153 2890339070909013561846865)
  ·
    refine ⟨2167754303181760171385149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2890339070909013561846865 2167754303181760171385149)
    ·
      refine ⟨812907863693160064269431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2167754303181760171385149 812907863693160064269431)
      ·
        refine ⟨1219361795539740096404147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 812907863693160064269431 1219361795539740096404147)
        ·
          refine ⟨1829042693309610144606221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1219361795539740096404147 1829042693309610144606221)
          ·
            refine ⟨685891009991103804227333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1829042693309610144606221 685891009991103804227333)
            ·
              refine ⟨128604564373331963292625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 685891009991103804227333 128604564373331963292625)
              ·
                refine ⟨96453423279998972469469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 128604564373331963292625 96453423279998972469469)
                ·
                  refine ⟨36170033729999614676051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 96453423279998972469469 36170033729999614676051)
                  ·
                    rfl

theorem cell21_158492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 4, 2, 3].length) (baseStart_158492 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_158492 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_158492 prefixEnd_158492 := by exact prefixLift 158492
  have htrace : WordTrace (prefixWord ++ tailWord_158492) baseStart_158492 baseEnd_158492 := by
    simpa [prefixWord, tailWord_158492, baseEnd_158492] using wordTrace_append hprefix tailTrace_158492
  have hstable : (prefixWord ++ tailWord_158492).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158492).length < 2 ^ (prefixWord ++ tailWord_158492).sum := by decide
  have hdescent : baseEnd_158492 < baseStart_158492 := by decide
  rcases family_descends (prefixWord ++ tailWord_158492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158551 : List Nat := [1, 1, 3, 2, 4, 1, 2, 4, 3]
def baseStart_158551 : Nat := 118140960795 + 158551 * 2 ^ 59
def prefixEnd_158551 : Nat := 4983230072969 + 3 ^ 40 * 158551 * 2
def baseEnd_158551 : Nat := 36183498333828623192597

theorem tailTrace_158551 : CollatzResearch.WordTrace tailWord_158551 prefixEnd_158551 36183498333828623192597 := by
  unfold tailWord_158551
  simp only [CollatzResearch.WordTrace]
  refine ⟨5782830048604280200091507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3855220032402853466727671 5782830048604280200091507)
  ·
    refine ⟨8674245072906420300137261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5782830048604280200091507 8674245072906420300137261)
    ·
      refine ⟨3252841902339907612551473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8674245072906420300137261 3252841902339907612551473)
      ·
        refine ⟨2439631426754930709413605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3252841902339907612551473 2439631426754930709413605)
        ·
          refine ⟨457430892516549508015051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2439631426754930709413605 457430892516549508015051)
          ·
            refine ⟨686146338774824262022577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 457430892516549508015051 686146338774824262022577)
            ·
              refine ⟨514609754081118196516933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 686146338774824262022577 514609754081118196516933)
              ·
                refine ⟨96489328890209661846925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 514609754081118196516933 96489328890209661846925)
                ·
                  refine ⟨36183498333828623192597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 96489328890209661846925 36183498333828623192597)
                  ·
                    rfl

theorem cell21_158551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 4, 3].length) (baseStart_158551 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_158551 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_158551 prefixEnd_158551 := by exact prefixLift 158551
  have htrace : WordTrace (prefixWord ++ tailWord_158551) baseStart_158551 baseEnd_158551 := by
    simpa [prefixWord, tailWord_158551, baseEnd_158551] using wordTrace_append hprefix tailTrace_158551
  have hstable : (prefixWord ++ tailWord_158551).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158551).length < 2 ^ (prefixWord ++ tailWord_158551).sum := by decide
  have hdescent : baseEnd_158551 < baseStart_158551 := by decide
  rcases family_descends (prefixWord ++ tailWord_158551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158579 : List Nat := [1, 1, 1, 2, 2, 1, 8, 5]
def baseStart_158579 : Nat := 118140960795 + 158579 * 2 ^ 59
def prefixEnd_158579 : Nat := 4983230072969 + 3 ^ 40 * 158579 * 2
def baseEnd_158579 : Nat := 12063296105102265575291

theorem tailTrace_158579 : CollatzResearch.WordTrace tailWord_158579 prefixEnd_158579 12063296105102265575291 := by
  unfold tailWord_158579
  simp only [CollatzResearch.WordTrace]
  refine ⟨5783851292502840982110791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3855900861668560654740527 5783851292502840982110791)
  ·
    refine ⟨8675776938754261473166187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5783851292502840982110791 8675776938754261473166187)
    ·
      refine ⟨13013665408131392209749281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8675776938754261473166187 13013665408131392209749281)
      ·
        refine ⟨9760249056098544157311961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13013665408131392209749281 9760249056098544157311961)
        ·
          refine ⟨7320186792073908117983971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9760249056098544157311961 7320186792073908117983971)
          ·
            refine ⟨10980280188110862176975957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7320186792073908117983971 10980280188110862176975957)
            ·
              refine ⟨128675158454424166136437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 10980280188110862176975957 128675158454424166136437)
              ·
                refine ⟨12063296105102265575291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 128675158454424166136437 12063296105102265575291)
                ·
                  rfl

theorem cell21_158579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 8, 5].length) (baseStart_158579 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_158579 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_158579 prefixEnd_158579 := by exact prefixLift 158579
  have htrace : WordTrace (prefixWord ++ tailWord_158579) baseStart_158579 baseEnd_158579 := by
    simpa [prefixWord, tailWord_158579, baseEnd_158579] using wordTrace_append hprefix tailTrace_158579
  have hstable : (prefixWord ++ tailWord_158579).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158579).length < 2 ^ (prefixWord ++ tailWord_158579).sum := by decide
  have hdescent : baseEnd_158579 < baseStart_158579 := by decide
  rcases family_descends (prefixWord ++ tailWord_158579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158703 : List Nat := [1, 1, 2, 1, 4, 4, 2, 3, 3]
def baseStart_158703 : Nat := 118140960795 + 158703 * 2 ^ 59
def prefixEnd_158703 : Nat := 4983230072969 + 3 ^ 40 * 158703 * 2
def baseEnd_158703 : Nat := 36218186804710136658953

theorem tailTrace_158703 : CollatzResearch.WordTrace tailWord_158703 prefixEnd_158703 36218186804710136658953 := by
  unfold tailWord_158703
  simp only [CollatzResearch.WordTrace]
  refine ⟨5788373944053610159624763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3858915962702406773083175 5788373944053610159624763)
  ·
    refine ⟨8682560916080415239437145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5788373944053610159624763 8682560916080415239437145)
    ·
      refine ⟨6511920687060311429577859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8682560916080415239437145 6511920687060311429577859)
      ·
        refine ⟨9767881030590467144366789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6511920687060311429577859 9767881030590467144366789)
        ·
          refine ⟨1831477693235712589568773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9767881030590467144366789 1831477693235712589568773)
          ·
            refine ⟨343402067481696110544145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1831477693235712589568773 343402067481696110544145)
            ·
              refine ⟨257551550611272082908109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 343402067481696110544145 257551550611272082908109)
              ·
                refine ⟨96581831479227031090541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 257551550611272082908109 96581831479227031090541)
                ·
                  refine ⟨36218186804710136658953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 96581831479227031090541 36218186804710136658953)
                  ·
                    rfl

theorem cell21_158703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 3, 3].length) (baseStart_158703 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_158703 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_158703 prefixEnd_158703 := by exact prefixLift 158703
  have htrace : WordTrace (prefixWord ++ tailWord_158703) baseStart_158703 baseEnd_158703 := by
    simpa [prefixWord, tailWord_158703, baseEnd_158703] using wordTrace_append hprefix tailTrace_158703
  have hstable : (prefixWord ++ tailWord_158703).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158703).length < 2 ^ (prefixWord ++ tailWord_158703).sum := by decide
  have hdescent : baseEnd_158703 < baseStart_158703 := by decide
  rcases family_descends (prefixWord ++ tailWord_158703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158734 : List Nat := [4, 1, 1, 2, 2, 3, 3, 1, 4]
def baseStart_158734 : Nat := 118140960795 + 158734 * 2 ^ 59
def prefixEnd_158734 : Nat := 4983230072969 + 3 ^ 40 * 158734 * 2
def baseEnd_158734 : Nat := 36225261427060971642223

theorem tailTrace_158734 : CollatzResearch.WordTrace tailWord_158734 prefixEnd_158734 36225261427060971642223 := by
  unfold tailWord_158734
  simp only [CollatzResearch.WordTrace]
  refine ⟨723688075867662806750407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3859669737960868302668837 723688075867662806750407)
  ·
    refine ⟨1085532113801494210125611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 723688075867662806750407 1085532113801494210125611)
    ·
      refine ⟨1628298170702241315188417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1085532113801494210125611 1628298170702241315188417)
      ·
        refine ⟨1221223628026680986391313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1628298170702241315188417 1221223628026680986391313)
        ·
          refine ⟨915917721020010739793485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1221223628026680986391313 915917721020010739793485)
          ·
            refine ⟨343469145382504027422557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 915917721020010739793485 343469145382504027422557)
            ·
              refine ⟨128800929518439010283459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 343469145382504027422557 128800929518439010283459)
              ·
                refine ⟨193201394277658515425189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128800929518439010283459 193201394277658515425189)
                ·
                  refine ⟨36225261427060971642223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 193201394277658515425189 36225261427060971642223)
                  ·
                    rfl

theorem cell21_158734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 3, 1, 4].length) (baseStart_158734 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_158734 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_158734 prefixEnd_158734 := by exact prefixLift 158734
  have htrace : WordTrace (prefixWord ++ tailWord_158734) baseStart_158734 baseEnd_158734 := by
    simpa [prefixWord, tailWord_158734, baseEnd_158734] using wordTrace_append hprefix tailTrace_158734
  have hstable : (prefixWord ++ tailWord_158734).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158734).length < 2 ^ (prefixWord ++ tailWord_158734).sum := by decide
  have hdescent : baseEnd_158734 < baseStart_158734 := by decide
  rcases family_descends (prefixWord ++ tailWord_158734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158745 : List Nat := [1, 2, 1, 2, 1, 1, 6, 2, 5]
def baseStart_158745 : Nat := 118140960795 + 158745 * 2 ^ 59
def prefixEnd_158745 : Nat := 4983230072969 + 3 ^ 40 * 158745 * 2
def baseEnd_158745 : Nat := 36227771776927396958867

theorem tailTrace_158745 : CollatzResearch.WordTrace tailWord_158745 prefixEnd_158745 36227771776927396958867 := by
  unfold tailWord_158745
  simp only [CollatzResearch.WordTrace]
  refine ⟨5789905809901451332653689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3859937206600967555102459 5789905809901451332653689)
  ·
    refine ⟨4342429357426088499490267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5789905809901451332653689 4342429357426088499490267)
    ·
      refine ⟨6513644036139132749235401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4342429357426088499490267 6513644036139132749235401)
      ·
        refine ⟨4885233027104349561926551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6513644036139132749235401 4885233027104349561926551)
        ·
          refine ⟨7327849540656524342889827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4885233027104349561926551 7327849540656524342889827)
          ·
            refine ⟨10991774310984786514334741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7327849540656524342889827 10991774310984786514334741)
            ·
              refine ⟨515239420827411867859441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10991774310984786514334741 515239420827411867859441)
              ·
                refine ⟨386429565620558900894581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 515239420827411867859441 386429565620558900894581)
                ·
                  refine ⟨36227771776927396958867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 386429565620558900894581 36227771776927396958867)
                  ·
                    rfl

theorem cell21_158745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 2, 5].length) (baseStart_158745 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_158745 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_158745 prefixEnd_158745 := by exact prefixLift 158745
  have htrace : WordTrace (prefixWord ++ tailWord_158745) baseStart_158745 baseEnd_158745 := by
    simpa [prefixWord, tailWord_158745, baseEnd_158745] using wordTrace_append hprefix tailTrace_158745
  have hstable : (prefixWord ++ tailWord_158745).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158745).length < 2 ^ (prefixWord ++ tailWord_158745).sum := by decide
  have hdescent : baseEnd_158745 < baseStart_158745 := by decide
  rcases family_descends (prefixWord ++ tailWord_158745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158776 : List Nat := [2, 1, 2, 1, 5, 1, 2, 1, 6]
def baseStart_158776 : Nat := 118140960795 + 158776 * 2 ^ 59
def prefixEnd_158776 : Nat := 4983230072969 + 3 ^ 40 * 158776 * 2
def baseEnd_158776 : Nat := 36234846399278231942137

theorem tailTrace_158776 : CollatzResearch.WordTrace tailWord_158776 prefixEnd_158776 36234846399278231942137 := by
  unfold tailWord_158776
  simp only [CollatzResearch.WordTrace]
  refine ⟨2895518236394571813516091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3860690981859429084688121 2895518236394571813516091)
  ·
    refine ⟨4343277354591857720274137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2895518236394571813516091 4343277354591857720274137)
    ·
      refine ⟨3257458015943893290205603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4343277354591857720274137 3257458015943893290205603)
      ·
        refine ⟨4886187023915839935308405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3257458015943893290205603 4886187023915839935308405)
        ·
          refine ⟨458080033492109993935163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4886187023915839935308405 458080033492109993935163)
          ·
            refine ⟨687120050238164990902745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 458080033492109993935163 687120050238164990902745)
            ·
              refine ⟨515340037678623743177059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 687120050238164990902745 515340037678623743177059)
              ·
                refine ⟨773010056517935614765589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 515340037678623743177059 773010056517935614765589)
                ·
                  refine ⟨36234846399278231942137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 773010056517935614765589 36234846399278231942137)
                  ·
                    rfl

theorem cell21_158776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 1, 6].length) (baseStart_158776 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_158776 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_158776 prefixEnd_158776 := by exact prefixLift 158776
  have htrace : WordTrace (prefixWord ++ tailWord_158776) baseStart_158776 baseEnd_158776 := by
    simpa [prefixWord, tailWord_158776, baseEnd_158776] using wordTrace_append hprefix tailTrace_158776
  have hstable : (prefixWord ++ tailWord_158776).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158776).length < 2 ^ (prefixWord ++ tailWord_158776).sum := by decide
  have hdescent : baseEnd_158776 < baseStart_158776 := by decide
  rcases family_descends (prefixWord ++ tailWord_158776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158824 : List Nat := [2, 1, 4, 4, 2, 8]
def baseStart_158824 : Nat := 118140960795 + 158824 * 2 ^ 59
def prefixEnd_158824 : Nat := 4983230072969 + 3 ^ 40 * 158824 * 2
def baseEnd_158824 : Nat := 1342437061231141301557

theorem tailTrace_158824 : CollatzResearch.WordTrace tailWord_158824 prefixEnd_158824 1342437061231141301557 := by
  unfold tailWord_158824
  simp only [CollatzResearch.WordTrace]
  refine ⟨2896393588307623912389763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3861858117743498549853017 2896393588307623912389763)
  ·
    refine ⟨4344590382461435868584645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2896393588307623912389763 4344590382461435868584645)
    ·
      refine ⟨814610696711519225359621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4344590382461435868584645 814610696711519225359621)
      ·
        refine ⟨152739505633409854754929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 814610696711519225359621 152739505633409854754929)
        ·
          refine ⟨114554629225057391066197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152739505633409854754929 114554629225057391066197)
          ·
            refine ⟨1342437061231141301557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 114554629225057391066197 1342437061231141301557)
            ·
              rfl

theorem cell21_158824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 8].length) (baseStart_158824 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_158824 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_158824 prefixEnd_158824 := by exact prefixLift 158824
  have htrace : WordTrace (prefixWord ++ tailWord_158824) baseStart_158824 baseEnd_158824 := by
    simpa [prefixWord, tailWord_158824, baseEnd_158824] using wordTrace_append hprefix tailTrace_158824
  have hstable : (prefixWord ++ tailWord_158824).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158824).length < 2 ^ (prefixWord ++ tailWord_158824).sum := by decide
  have hdescent : baseEnd_158824 < baseStart_158824 := by decide
  rcases family_descends (prefixWord ++ tailWord_158824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158838 : List Nat := [5, 1, 1, 2, 1, 1, 2, 3, 5]
def baseStart_158838 : Nat := 118140960795 + 158838 * 2 ^ 59
def prefixEnd_158838 : Nat := 4983230072969 + 3 ^ 40 * 158838 * 2
def baseEnd_158838 : Nat := 36248995643979901908677

theorem tailTrace_158838 : CollatzResearch.WordTrace tailWord_158838 prefixEnd_158838 36248995643979901908677 := by
  unfold tailWord_158838
  simp only [CollatzResearch.WordTrace]
  refine ⟨362081112410283013486823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3862198532376352143859445 362081112410283013486823)
  ·
    refine ⟨543121668615424520230235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 362081112410283013486823 543121668615424520230235)
    ·
      refine ⟨814682502923136780345353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 543121668615424520230235 814682502923136780345353)
      ·
        refine ⟨611011877192352585259015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 814682502923136780345353 611011877192352585259015)
        ·
          refine ⟨916517815788528877888523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 611011877192352585259015 916517815788528877888523)
          ·
            refine ⟨1374776723682793316832785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 916517815788528877888523 1374776723682793316832785)
            ·
              refine ⟨1031082542762094987624589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1374776723682793316832785 1031082542762094987624589)
              ·
                refine ⟨386655953535785620359221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1031082542762094987624589 386655953535785620359221)
                ·
                  refine ⟨36248995643979901908677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 386655953535785620359221 36248995643979901908677)
                  ·
                    rfl

theorem cell21_158838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_158838 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_158838 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_158838 prefixEnd_158838 := by exact prefixLift 158838
  have htrace : WordTrace (prefixWord ++ tailWord_158838) baseStart_158838 baseEnd_158838 := by
    simpa [prefixWord, tailWord_158838, baseEnd_158838] using wordTrace_append hprefix tailTrace_158838
  have hstable : (prefixWord ++ tailWord_158838).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158838).length < 2 ^ (prefixWord ++ tailWord_158838).sum := by decide
  have hdescent : baseEnd_158838 < baseStart_158838 := by decide
  rcases family_descends (prefixWord ++ tailWord_158838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158959 : List Nat := [1, 1, 2, 1, 7, 1, 2, 6]
def baseStart_158959 : Nat := 118140960795 + 158959 * 2 ^ 59
def prefixEnd_158959 : Nat := 4983230072969 + 3 ^ 40 * 158959 * 2
def baseEnd_158959 : Nat := 12092203164170193463921

theorem tailTrace_158959 : CollatzResearch.WordTrace tailWord_158959 prefixEnd_158959 12092203164170193463921 := by
  unfold tailWord_158959
  simp only [CollatzResearch.WordTrace]
  refine ⟨5797711031126165880943931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3865140687417443920629287 5797711031126165880943931)
  ·
    refine ⟨8696566546689248821415897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5797711031126165880943931 8696566546689248821415897)
    ·
      refine ⟨6522424910016936616061923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8696566546689248821415897 6522424910016936616061923)
      ·
        refine ⟨9783637365025404924092885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6522424910016936616061923 9783637365025404924092885)
        ·
          refine ⟨229304000742782927908427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 9783637365025404924092885 229304000742782927908427)
          ·
            refine ⟨343956001114174391862641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 229304000742782927908427 343956001114174391862641)
            ·
              refine ⟨257967000835630793896981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 343956001114174391862641 257967000835630793896981)
              ·
                refine ⟨12092203164170193463921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 257967000835630793896981 12092203164170193463921)
                ·
                  rfl

theorem cell21_158959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 6].length) (baseStart_158959 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_158959 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_158959 prefixEnd_158959 := by exact prefixLift 158959
  have htrace : WordTrace (prefixWord ++ tailWord_158959) baseStart_158959 baseEnd_158959 := by
    simpa [prefixWord, tailWord_158959, baseEnd_158959] using wordTrace_append hprefix tailTrace_158959
  have hstable : (prefixWord ++ tailWord_158959).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158959).length < 2 ^ (prefixWord ++ tailWord_158959).sum := by decide
  have hdescent : baseEnd_158959 < baseStart_158959 := by decide
  rcases family_descends (prefixWord ++ tailWord_158959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159004 : List Nat := [2, 2, 3, 1, 1, 1, 3, 4, 4]
def baseStart_159004 : Nat := 118140960795 + 159004 * 2 ^ 59
def prefixEnd_159004 : Nat := 4983230072969 + 3 ^ 40 * 159004 * 2
def baseEnd_159004 : Nat := 36286879105600502141671

theorem tailTrace_159004 : CollatzResearch.WordTrace tailWord_159004 prefixEnd_159004 36286879105600502141671 := by
  unfold tailWord_159004
  simp only [CollatzResearch.WordTrace]
  refine ⟨2899676157981569283166033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3866234877308759044221377 2899676157981569283166033)
  ·
    refine ⟨2174757118486176962374525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2899676157981569283166033 2174757118486176962374525)
    ·
      refine ⟨815533919432316360890447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2174757118486176962374525 815533919432316360890447)
      ·
        refine ⟨1223300879148474541335671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 815533919432316360890447 1223300879148474541335671)
        ·
          refine ⟨1834951318722711812003507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1223300879148474541335671 1834951318722711812003507)
          ·
            refine ⟨2752426978084067718005261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1834951318722711812003507 2752426978084067718005261)
            ·
              refine ⟨1032160116781525394251973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2752426978084067718005261 1032160116781525394251973)
              ·
                refine ⟨193530021896536011422245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1032160116781525394251973 193530021896536011422245)
                ·
                  refine ⟨36286879105600502141671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 193530021896536011422245 36286879105600502141671)
                  ·
                    rfl

theorem cell21_159004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 4, 4].length) (baseStart_159004 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_159004 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_159004 prefixEnd_159004 := by exact prefixLift 159004
  have htrace : WordTrace (prefixWord ++ tailWord_159004) baseStart_159004 baseEnd_159004 := by
    simpa [prefixWord, tailWord_159004, baseEnd_159004] using wordTrace_append hprefix tailTrace_159004
  have hstable : (prefixWord ++ tailWord_159004).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159004).length < 2 ^ (prefixWord ++ tailWord_159004).sum := by decide
  have hdescent : baseEnd_159004 < baseStart_159004 := by decide
  rcases family_descends (prefixWord ++ tailWord_159004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159007 : List Nat := [1, 1, 2, 4, 4, 1, 1, 4, 3]
def baseStart_159007 : Nat := 118140960795 + 159007 * 2 ^ 59
def prefixEnd_159007 : Nat := 4983230072969 + 3 ^ 40 * 159007 * 2
def baseEnd_159007 : Nat := 36287563746473163591665

theorem tailTrace_159007 : CollatzResearch.WordTrace tailWord_159007 prefixEnd_159007 36287563746473163591665 := by
  unfold tailWord_159007
  simp only [CollatzResearch.WordTrace]
  refine ⟨5799461734952270078691275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3866307823301513385794183 5799461734952270078691275)
  ·
    refine ⟨8699192602428405118036913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5799461734952270078691275 8699192602428405118036913)
    ·
      refine ⟨6524394451821303838527685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8699192602428405118036913 6524394451821303838527685)
      ·
        refine ⟨1223323959716494469723941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6524394451821303838527685 1223323959716494469723941)
        ·
          refine ⟨229373242446842713073239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1223323959716494469723941 229373242446842713073239)
          ·
            refine ⟨344059863670264069609859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 229373242446842713073239 344059863670264069609859)
            ·
              refine ⟨516089795505396104414789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 344059863670264069609859 516089795505396104414789)
              ·
                refine ⟨96766836657261769577773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 516089795505396104414789 96766836657261769577773)
                ·
                  refine ⟨36287563746473163591665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 96766836657261769577773 36287563746473163591665)
                  ·
                    rfl

theorem cell21_159007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 4, 3].length) (baseStart_159007 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_159007 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_159007 prefixEnd_159007 := by exact prefixLift 159007
  have htrace : WordTrace (prefixWord ++ tailWord_159007) baseStart_159007 baseEnd_159007 := by
    simpa [prefixWord, tailWord_159007, baseEnd_159007] using wordTrace_append hprefix tailTrace_159007
  have hstable : (prefixWord ++ tailWord_159007).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159007).length < 2 ^ (prefixWord ++ tailWord_159007).sum := by decide
  have hdescent : baseEnd_159007 < baseStart_159007 := by decide
  rcases family_descends (prefixWord ++ tailWord_159007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159066 : List Nat := [3, 1, 1, 2, 1, 2, 4, 4, 3]
def baseStart_159066 : Nat := 118140960795 + 159066 * 2 ^ 59
def prefixEnd_159066 : Nat := 4983230072969 + 3 ^ 40 * 159066 * 2
def baseEnd_159066 : Nat := 36301028350302172108211

theorem tailTrace_159066 : CollatzResearch.WordTrace tailWord_159066 prefixEnd_159066 36301028350302172108211 := by
  unfold tailWord_159066
  simp only [CollatzResearch.WordTrace]
  refine ⟨1450403410434630788772263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3867742427825682103392701 1450403410434630788772263)
  ·
    refine ⟨2175605115651946183158395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1450403410434630788772263 2175605115651946183158395)
    ·
      refine ⟨3263407673477919274737593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2175605115651946183158395 3263407673477919274737593)
      ·
        refine ⟨2447555755108439456053195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3263407673477919274737593 2447555755108439456053195)
        ·
          refine ⟨3671333632662659184079793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2447555755108439456053195 3671333632662659184079793)
          ·
            refine ⟨2753500224496994388059845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3671333632662659184079793 2753500224496994388059845)
            ·
              refine ⟨516281292093186447761221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2753500224496994388059845 516281292093186447761221)
              ·
                refine ⟨96802742267472458955229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 516281292093186447761221 96802742267472458955229)
                ·
                  refine ⟨36301028350302172108211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 96802742267472458955229 36301028350302172108211)
                  ·
                    rfl

theorem cell21_159066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 4, 3].length) (baseStart_159066 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_159066 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_159066 prefixEnd_159066 := by exact prefixLift 159066
  have htrace : WordTrace (prefixWord ++ tailWord_159066) baseStart_159066 baseEnd_159066 := by
    simpa [prefixWord, tailWord_159066, baseEnd_159066] using wordTrace_append hprefix tailTrace_159066
  have hstable : (prefixWord ++ tailWord_159066).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159066).length < 2 ^ (prefixWord ++ tailWord_159066).sum := by decide
  have hdescent : baseEnd_159066 < baseStart_159066 := by decide
  rcases family_descends (prefixWord ++ tailWord_159066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159086 : List Nat := [4, 1, 2, 4, 2, 1, 2, 5]
def baseStart_159086 : Nat := 118140960795 + 159086 * 2 ^ 59
def prefixEnd_159086 : Nat := 4983230072969 + 3 ^ 40 * 159086 * 2
def baseEnd_159086 : Nat := 12101864207595527258279

theorem tailTrace_159086 : CollatzResearch.WordTrace tailWord_159086 prefixEnd_159086 12101864207595527258279 := by
  unfold tailWord_159086
  simp only [CollatzResearch.WordTrace]
  refine ⟨725292887708258321352139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3868228734444044380544741 725292887708258321352139)
  ·
    refine ⟨1087939331562387482028209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 725292887708258321352139 1087939331562387482028209)
    ·
      refine ⟨815954498671790611521157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1087939331562387482028209 815954498671790611521157)
      ·
        refine ⟨152991468500960739660217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 815954498671790611521157 152991468500960739660217)
        ·
          refine ⟨114743601375720554745163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152991468500960739660217 114743601375720554745163)
          ·
            refine ⟨172115402063580832117745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114743601375720554745163 172115402063580832117745)
            ·
              refine ⟨129086551547685624088309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 172115402063580832117745 129086551547685624088309)
              ·
                refine ⟨12101864207595527258279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 129086551547685624088309 12101864207595527258279)
                ·
                  rfl

theorem cell21_159086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 2, 5].length) (baseStart_159086 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_159086 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_159086 prefixEnd_159086 := by exact prefixLift 159086
  have htrace : WordTrace (prefixWord ++ tailWord_159086) baseStart_159086 baseEnd_159086 := by
    simpa [prefixWord, tailWord_159086, baseEnd_159086] using wordTrace_append hprefix tailTrace_159086
  have hstable : (prefixWord ++ tailWord_159086).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159086).length < 2 ^ (prefixWord ++ tailWord_159086).sum := by decide
  have hdescent : baseEnd_159086 < baseStart_159086 := by decide
  rcases family_descends (prefixWord ++ tailWord_159086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159125 : List Nat := [1, 3, 2, 1, 1, 2, 5, 1, 5]
def baseStart_159125 : Nat := 118140960795 + 159125 * 2 ^ 59
def prefixEnd_159125 : Nat := 4983230072969 + 3 ^ 40 * 159125 * 2
def baseEnd_159125 : Nat := 36314492954131180624757

theorem tailTrace_159125 : CollatzResearch.WordTrace tailWord_159125 prefixEnd_159125 36314492954131180624757 := by
  unfold tailWord_159125
  simp only [CollatzResearch.WordTrace]
  refine ⟨5803765548524776231486829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3869177032349850820991219 5803765548524776231486829)
  ·
    refine ⟨2176412080696791086807561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5803765548524776231486829 2176412080696791086807561)
    ·
      refine ⟨1632309060522593315105671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2176412080696791086807561 1632309060522593315105671)
      ·
        refine ⟨2448463590783889972658507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1632309060522593315105671 2448463590783889972658507)
        ·
          refine ⟨3672695386175834958987761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2448463590783889972658507 3672695386175834958987761)
          ·
            refine ⟨2754521539631876219240821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3672695386175834958987761 2754521539631876219240821)
            ·
              refine ⟨258236394340488395553827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2754521539631876219240821 258236394340488395553827)
              ·
                refine ⟨387354591510732593330741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 258236394340488395553827 387354591510732593330741)
                ·
                  refine ⟨36314492954131180624757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 387354591510732593330741 36314492954131180624757)
                  ·
                    rfl

theorem cell21_159125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 1, 5].length) (baseStart_159125 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_159125 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_159125 prefixEnd_159125 := by exact prefixLift 159125
  have htrace : WordTrace (prefixWord ++ tailWord_159125) baseStart_159125 baseEnd_159125 := by
    simpa [prefixWord, tailWord_159125, baseEnd_159125] using wordTrace_append hprefix tailTrace_159125
  have hstable : (prefixWord ++ tailWord_159125).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159125).length < 2 ^ (prefixWord ++ tailWord_159125).sum := by decide
  have hdescent : baseEnd_159125 < baseStart_159125 := by decide
  rcases family_descends (prefixWord ++ tailWord_159125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159201 : List Nat := [1, 2, 3, 1, 2, 4, 1, 2, 5]
def baseStart_159201 : Nat := 118140960795 + 159201 * 2 ^ 59
def prefixEnd_159201 : Nat := 4983230072969 + 3 ^ 40 * 159201 * 2
def baseEnd_159201 : Nat := 36331837189571937357935

theorem tailTrace_159201 : CollatzResearch.WordTrace tailWord_159201 prefixEnd_159201 36331837189571937357935 := by
  unfold tailWord_159201
  simp only [CollatzResearch.WordTrace]
  refine ⟨5806537496249441211253457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3871024997499627474168971 5806537496249441211253457)
  ·
    refine ⟨4354903122187080908440093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5806537496249441211253457 4354903122187080908440093)
    ·
      refine ⟨1633088670820155340665035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4354903122187080908440093 1633088670820155340665035)
      ·
        refine ⟨2449633006230233010997553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1633088670820155340665035 2449633006230233010997553)
        ·
          refine ⟨1837224754672674758248165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2449633006230233010997553 1837224754672674758248165)
          ·
            refine ⟨344479641501126517171531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1837224754672674758248165 344479641501126517171531)
            ·
              refine ⟨516719462251689775757297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 344479641501126517171531 516719462251689775757297)
              ·
                refine ⟨387539596688767331817973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 516719462251689775757297 387539596688767331817973)
                ·
                  refine ⟨36331837189571937357935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 387539596688767331817973 36331837189571937357935)
                  ·
                    rfl

theorem cell21_159201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 2, 5].length) (baseStart_159201 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_159201 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_159201 prefixEnd_159201 := by exact prefixLift 159201
  have htrace : WordTrace (prefixWord ++ tailWord_159201) baseStart_159201 baseEnd_159201 := by
    simpa [prefixWord, tailWord_159201, baseEnd_159201] using wordTrace_append hprefix tailTrace_159201
  have hstable : (prefixWord ++ tailWord_159201).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159201).length < 2 ^ (prefixWord ++ tailWord_159201).sum := by decide
  have hdescent : baseEnd_159201 < baseStart_159201 := by decide
  rcases family_descends (prefixWord ++ tailWord_159201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159308 : List Nat := [2, 2, 1, 3, 1, 4, 1, 3, 4]
def baseStart_159308 : Nat := 118140960795 + 159308 * 2 ^ 59
def prefixEnd_159308 : Nat := 4983230072969 + 3 ^ 40 * 159308 * 2
def baseEnd_159308 : Nat := 36356256047363529074383

theorem tailTrace_159308 : CollatzResearch.WordTrace tailWord_159308 prefixEnd_159308 36356256047363529074383 := by
  unfold tailWord_159308
  simp only [CollatzResearch.WordTrace]
  refine ⟨2905220053430899242699289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3873626737907865656932385 2905220053430899242699289)
  ·
    refine ⟨2178915040073174432024467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2905220053430899242699289 2178915040073174432024467)
    ·
      refine ⟨3268372560109761648036701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2178915040073174432024467 3268372560109761648036701)
      ·
        refine ⟨1225639710041160618013763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3268372560109761648036701 1225639710041160618013763)
        ·
          refine ⟨1838459565061740927020645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1225639710041160618013763 1838459565061740927020645)
          ·
            refine ⟨344711168449076423816371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1838459565061740927020645 344711168449076423816371)
            ·
              refine ⟨517066752673614635724557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 344711168449076423816371 517066752673614635724557)
              ·
                refine ⟨193900032252605488396709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 517066752673614635724557 193900032252605488396709)
                ·
                  refine ⟨36356256047363529074383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 193900032252605488396709 36356256047363529074383)
                  ·
                    rfl

theorem cell21_159308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 3, 4].length) (baseStart_159308 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_159308 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_159308 prefixEnd_159308 := by exact prefixLift 159308
  have htrace : WordTrace (prefixWord ++ tailWord_159308) baseStart_159308 baseEnd_159308 := by
    simpa [prefixWord, tailWord_159308, baseEnd_159308] using wordTrace_append hprefix tailTrace_159308
  have hstable : (prefixWord ++ tailWord_159308).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159308).length < 2 ^ (prefixWord ++ tailWord_159308).sum := by decide
  have hdescent : baseEnd_159308 < baseStart_159308 := by decide
  rcases family_descends (prefixWord ++ tailWord_159308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159381 : List Nat := [1, 3, 2, 1, 1, 1, 1, 11]
def baseStart_159381 : Nat := 118140960795 + 159381 * 2 ^ 59
def prefixEnd_159381 : Nat := 4983230072969 + 3 ^ 40 * 159381 * 2
def baseEnd_159381 : Nat := 12124305213977208119189

theorem tailTrace_159381 : CollatzResearch.WordTrace tailWord_159381 prefixEnd_159381 12124305213977208119189 := by
  unfold tailWord_159381
  simp only [CollatzResearch.WordTrace]
  refine ⟨5813102635597331952805997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3875401757064887968537331 5813102635597331952805997)
  ·
    refine ⟨2179913488348999482302249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5813102635597331952805997 2179913488348999482302249)
    ·
      refine ⟨1634935116261749611726687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2179913488348999482302249 1634935116261749611726687)
      ·
        refine ⟨2452402674392624417590031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1634935116261749611726687 2452402674392624417590031)
        ·
          refine ⟨3678604011588936626385047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2452402674392624417590031 3678604011588936626385047)
          ·
            refine ⟨5517906017383404939577571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3678604011588936626385047 5517906017383404939577571)
            ·
              refine ⟨8276859026075107409366357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5517906017383404939577571 8276859026075107409366357)
              ·
                refine ⟨12124305213977208119189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 8276859026075107409366357 12124305213977208119189)
                ·
                  rfl

theorem cell21_159381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 11].length) (baseStart_159381 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_159381 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_159381 prefixEnd_159381 := by exact prefixLift 159381
  have htrace : WordTrace (prefixWord ++ tailWord_159381) baseStart_159381 baseEnd_159381 := by
    simpa [prefixWord, tailWord_159381, baseEnd_159381] using wordTrace_append hprefix tailTrace_159381
  have hstable : (prefixWord ++ tailWord_159381).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159381).length < 2 ^ (prefixWord ++ tailWord_159381).sum := by decide
  have hdescent : baseEnd_159381 < baseStart_159381 := by decide
  rcases family_descends (prefixWord ++ tailWord_159381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159463 : List Nat := [1, 1, 5, 4, 1, 2, 1, 1, 5]
def baseStart_159463 : Nat := 118140960795 + 159463 * 2 ^ 59
def prefixEnd_159463 : Nat := 4983230072969 + 3 ^ 40 * 159463 * 2
def baseEnd_159463 : Nat := 36391629159117703990733

theorem tailTrace_159463 : CollatzResearch.WordTrace tailWord_159463 prefixEnd_159463 36391629159117703990733 := by
  unfold tailWord_159463
  simp only [CollatzResearch.WordTrace]
  refine ⟨5816093421300259957291043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3877395614200173304860695 5816093421300259957291043)
  ·
    refine ⟨8724140131950389935936565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5816093421300259957291043 8724140131950389935936565)
    ·
      refine ⟨817888137370349056494053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8724140131950389935936565 817888137370349056494053)
      ·
        refine ⟨153354025756940448092635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 817888137370349056494053 153354025756940448092635)
        ·
          refine ⟨230031038635410672138953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153354025756940448092635 230031038635410672138953)
          ·
            refine ⟨172523278976558004104215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 230031038635410672138953 172523278976558004104215)
            ·
              refine ⟨258784918464837006156323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 172523278976558004104215 258784918464837006156323)
              ·
                refine ⟨388177377697255509234485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 258784918464837006156323 388177377697255509234485)
                ·
                  refine ⟨36391629159117703990733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 388177377697255509234485 36391629159117703990733)
                  ·
                    rfl

theorem cell21_159463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 1, 5].length) (baseStart_159463 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_159463 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_159463 prefixEnd_159463 := by exact prefixLift 159463
  have htrace : WordTrace (prefixWord ++ tailWord_159463) baseStart_159463 baseEnd_159463 := by
    simpa [prefixWord, tailWord_159463, baseEnd_159463] using wordTrace_append hprefix tailTrace_159463
  have hstable : (prefixWord ++ tailWord_159463).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159463).length < 2 ^ (prefixWord ++ tailWord_159463).sum := by decide
  have hdescent : baseEnd_159463 < baseStart_159463 := by decide
  rcases family_descends (prefixWord ++ tailWord_159463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159474 : List Nat := [3, 2, 1, 3, 1, 1, 4, 6]
def baseStart_159474 : Nat := 118140960795 + 159474 * 2 ^ 59
def prefixEnd_159474 : Nat := 4983230072969 + 3 ^ 40 * 159474 * 2
def baseEnd_159474 : Nat := 12131379836328043102459

theorem tailTrace_159474 : CollatzResearch.WordTrace tailWord_159474 prefixEnd_159474 12131379836328043102459 := by
  unfold tailWord_159474
  simp only [CollatzResearch.WordTrace]
  refine ⟨1454123656065102208985369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3877663082840272557294317 1454123656065102208985369)
  ·
    refine ⟨1090592742048826656739027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1454123656065102208985369 1090592742048826656739027)
    ·
      refine ⟨1635889113073239985108541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1090592742048826656739027 1635889113073239985108541)
      ·
        refine ⟨613458417402464994415703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1635889113073239985108541 613458417402464994415703)
        ·
          refine ⟨920187626103697491623555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 613458417402464994415703 920187626103697491623555)
          ·
            refine ⟨1380281439155546237435333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 920187626103697491623555 1380281439155546237435333)
            ·
              refine ⟨258802769841664919519125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1380281439155546237435333 258802769841664919519125)
              ·
                refine ⟨12131379836328043102459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 258802769841664919519125 12131379836328043102459)
                ·
                  rfl

theorem cell21_159474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 6].length) (baseStart_159474 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_159474 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_159474 prefixEnd_159474 := by exact prefixLift 159474
  have htrace : WordTrace (prefixWord ++ tailWord_159474) baseStart_159474 baseEnd_159474 := by
    simpa [prefixWord, tailWord_159474, baseEnd_159474] using wordTrace_append hprefix tailTrace_159474
  have hstable : (prefixWord ++ tailWord_159474).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159474).length < 2 ^ (prefixWord ++ tailWord_159474).sum := by decide
  have hdescent : baseEnd_159474 < baseStart_159474 := by decide
  rcases family_descends (prefixWord ++ tailWord_159474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159505 : List Nat := [1, 2, 2, 1, 1, 3, 1, 7, 3]
def baseStart_159505 : Nat := 118140960795 + 159505 * 2 ^ 59
def prefixEnd_159505 : Nat := 4983230072969 + 3 ^ 40 * 159505 * 2
def baseEnd_159505 : Nat := 36401214131334964290647

theorem tailTrace_159505 : CollatzResearch.WordTrace tailWord_159505 prefixEnd_159505 36401214131334964290647 := by
  unfold tailWord_159505
  simp only [CollatzResearch.WordTrace]
  refine ⟨5817625287148101130319969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3878416858098734086879979 5817625287148101130319969)
  ·
    refine ⟨4363218965361075847739977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5817625287148101130319969 4363218965361075847739977)
    ·
      refine ⟨3272414224020806885804983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4363218965361075847739977 3272414224020806885804983)
      ·
        refine ⟨4908621336031210328707475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3272414224020806885804983 4908621336031210328707475)
        ·
          refine ⟨7362932004046815493061213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4908621336031210328707475 7362932004046815493061213)
          ·
            refine ⟨2761099501517555809897955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7362932004046815493061213 2761099501517555809897955)
            ·
              refine ⟨4141649252276333714846933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2761099501517555809897955 4141649252276333714846933)
              ·
                refine ⟨97069904350226571441725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4141649252276333714846933 97069904350226571441725)
                ·
                  refine ⟨36401214131334964290647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 97069904350226571441725 36401214131334964290647)
                  ·
                    rfl

theorem cell21_159505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 7, 3].length) (baseStart_159505 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_159505 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_159505 prefixEnd_159505 := by exact prefixLift 159505
  have htrace : WordTrace (prefixWord ++ tailWord_159505) baseStart_159505 baseEnd_159505 := by
    simpa [prefixWord, tailWord_159505, baseEnd_159505] using wordTrace_append hprefix tailTrace_159505
  have hstable : (prefixWord ++ tailWord_159505).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159505).length < 2 ^ (prefixWord ++ tailWord_159505).sum := by decide
  have hdescent : baseEnd_159505 < baseStart_159505 := by decide
  rcases family_descends (prefixWord ++ tailWord_159505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159508 : List Nat := [2, 4, 4, 1, 1, 9]
def baseStart_159508 : Nat := 118140960795 + 159508 * 2 ^ 59
def prefixEnd_159508 : Nat := 4983230072969 + 3 ^ 40 * 159508 * 2
def baseEnd_159508 : Nat := 1348218473044726879283

theorem tailTrace_159508 : CollatzResearch.WordTrace tailWord_159508 prefixEnd_159508 1348218473044726879283 := by
  unfold tailWord_159508
  simp only [CollatzResearch.WordTrace]
  refine ⟨2908867353068616321339589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3878489804091488428452785 2908867353068616321339589)
  ·
    refine ⟨545412628700365560251173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2908867353068616321339589 545412628700365560251173)
    ·
      refine ⟨102264867881318542547095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 545412628700365560251173 102264867881318542547095)
      ·
        refine ⟨153397301821977813820643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102264867881318542547095 153397301821977813820643)
        ·
          refine ⟨230095952732966720730965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153397301821977813820643 230095952732966720730965)
          ·
            refine ⟨1348218473044726879283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 230095952732966720730965 1348218473044726879283)
            ·
              rfl

theorem cell21_159508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 9].length) (baseStart_159508 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_159508 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_159508 prefixEnd_159508 := by exact prefixLift 159508
  have htrace : WordTrace (prefixWord ++ tailWord_159508) baseStart_159508 baseEnd_159508 := by
    simpa [prefixWord, tailWord_159508, baseEnd_159508] using wordTrace_append hprefix tailTrace_159508
  have hstable : (prefixWord ++ tailWord_159508).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159508).length < 2 ^ (prefixWord ++ tailWord_159508).sum := by decide
  have hdescent : baseEnd_159508 < baseStart_159508 := by decide
  rcases family_descends (prefixWord ++ tailWord_159508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159522 : List Nat := [3, 3, 1, 1, 2, 1, 3, 4, 3]
def baseStart_159522 : Nat := 118140960795 + 159522 * 2 ^ 59
def prefixEnd_159522 : Nat := 4983230072969 + 3 ^ 40 * 159522 * 2
def baseEnd_159522 : Nat := 36405093762946712507279

theorem tailTrace_159522 : CollatzResearch.WordTrace tailWord_159522 prefixEnd_159522 36405093762946712507279 := by
  unfold tailWord_159522
  simp only [CollatzResearch.WordTrace]
  refine ⟨1454561332021628258422205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3878830218724342022459213 1454561332021628258422205)
  ·
    refine ⟨545460499508110596908327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1454561332021628258422205 545460499508110596908327)
    ·
      refine ⟨818190749262165895362491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 545460499508110596908327 818190749262165895362491)
      ·
        refine ⟨1227286123893248843043737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 818190749262165895362491 1227286123893248843043737)
        ·
          refine ⟨920464592919936632282803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1227286123893248843043737 920464592919936632282803)
          ·
            refine ⟨1380696889379904948424205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 920464592919936632282803 1380696889379904948424205)
            ·
              refine ⟨517761333517464355659077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1380696889379904948424205 517761333517464355659077)
              ·
                refine ⟨97080250034524566686077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 517761333517464355659077 97080250034524566686077)
                ·
                  refine ⟨36405093762946712507279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 97080250034524566686077 36405093762946712507279)
                  ·
                    rfl

theorem cell21_159522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 4, 3].length) (baseStart_159522 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_159522 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_159522 prefixEnd_159522 := by exact prefixLift 159522
  have htrace : WordTrace (prefixWord ++ tailWord_159522) baseStart_159522 baseEnd_159522 := by
    simpa [prefixWord, tailWord_159522, baseEnd_159522] using wordTrace_append hprefix tailTrace_159522
  have hstable : (prefixWord ++ tailWord_159522).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159522).length < 2 ^ (prefixWord ++ tailWord_159522).sum := by decide
  have hdescent : baseEnd_159522 < baseStart_159522 := by decide
  rcases family_descends (prefixWord ++ tailWord_159522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159609 : List Nat := [1, 2, 1, 3, 2, 2, 3, 7]
def baseStart_159609 : Nat := 118140960795 + 159609 * 2 ^ 59
def prefixEnd_159609 : Nat := 4983230072969 + 3 ^ 40 * 159609 * 2
def baseEnd_159609 : Nat := 12141649449417964852367

theorem tailTrace_159609 : CollatzResearch.WordTrace tailWord_159609 prefixEnd_159609 12141649449417964852367 := by
  unfold tailWord_159609
  simp only [CollatzResearch.WordTrace]
  refine ⟨5821418478771326892105881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3880945652514217928070587 5821418478771326892105881)
  ·
    refine ⟨4366063859078495169079411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5821418478771326892105881 4366063859078495169079411)
    ·
      refine ⟨6549095788617742753619117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4366063859078495169079411 6549095788617742753619117)
      ·
        refine ⟨2455910920731653532607169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6549095788617742753619117 2455910920731653532607169)
        ·
          refine ⟨1841933190548740149455377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2455910920731653532607169 1841933190548740149455377)
          ·
            refine ⟨1381449892911555112091533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1841933190548740149455377 1381449892911555112091533)
            ·
              refine ⟨518043709841833167034325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1381449892911555112091533 518043709841833167034325)
              ·
                refine ⟨12141649449417964852367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 518043709841833167034325 12141649449417964852367)
                ·
                  rfl

theorem cell21_159609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 7].length) (baseStart_159609 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_159609 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_159609 prefixEnd_159609 := by exact prefixLift 159609
  have htrace : WordTrace (prefixWord ++ tailWord_159609) baseStart_159609 baseEnd_159609 := by
    simpa [prefixWord, tailWord_159609, baseEnd_159609] using wordTrace_append hprefix tailTrace_159609
  have hstable : (prefixWord ++ tailWord_159609).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159609).length < 2 ^ (prefixWord ++ tailWord_159609).sum := by decide
  have hdescent : baseEnd_159609 < baseStart_159609 := by decide
  rcases family_descends (prefixWord ++ tailWord_159609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159646 : List Nat := [4, 3, 1, 3, 1, 1, 1, 3, 4]
def baseStart_159646 : Nat := 118140960795 + 159646 * 2 ^ 59
def prefixEnd_159646 : Nat := 4983230072969 + 3 ^ 40 * 159646 * 2
def baseEnd_159646 : Nat := 36433392252350052440359

theorem tailTrace_159646 : CollatzResearch.WordTrace tailWord_159646 prefixEnd_159646 36433392252350052440359 := by
  unfold tailWord_159646
  simp only [CollatzResearch.WordTrace]
  refine ⟨727845997454660276400349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3881845319758188140801861 727845997454660276400349)
  ·
    refine ⟨272942249045497603650131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 727845997454660276400349 272942249045497603650131)
    ·
      refine ⟨409413373568246405475197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272942249045497603650131 409413373568246405475197)
      ·
        refine ⟨153530015088092402053199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 409413373568246405475197 153530015088092402053199)
        ·
          refine ⟨230295022632138603079799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153530015088092402053199 230295022632138603079799)
          ·
            refine ⟨345442533948207904619699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 230295022632138603079799 345442533948207904619699)
            ·
              refine ⟨518163800922311856929549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 345442533948207904619699 518163800922311856929549)
              ·
                refine ⟨194311425345866946348581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 518163800922311856929549 194311425345866946348581)
                ·
                  refine ⟨36433392252350052440359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 194311425345866946348581 36433392252350052440359)
                  ·
                    rfl

theorem cell21_159646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_159646 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_159646 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_159646 prefixEnd_159646 := by exact prefixLift 159646
  have htrace : WordTrace (prefixWord ++ tailWord_159646) baseStart_159646 baseEnd_159646 := by
    simpa [prefixWord, tailWord_159646, baseEnd_159646] using wordTrace_append hprefix tailTrace_159646
  have hstable : (prefixWord ++ tailWord_159646).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159646).length < 2 ^ (prefixWord ++ tailWord_159646).sum := by decide
  have hdescent : baseEnd_159646 < baseStart_159646 := by decide
  rcases family_descends (prefixWord ++ tailWord_159646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159688 : List Nat := [2, 1, 3, 1, 4, 2, 2, 2, 4]
def baseStart_159688 : Nat := 118140960795 + 159688 * 2 ^ 59
def prefixEnd_159688 : Nat := 4983230072969 + 3 ^ 40 * 159688 * 2
def baseEnd_159688 : Nat := 36442977224567312740273

theorem tailTrace_159688 : CollatzResearch.WordTrace tailWord_159688 prefixEnd_159688 36442977224567312740273 := by
  unfold tailWord_159688
  simp only [CollatzResearch.WordTrace]
  refine ⟨2912149922742561692115859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3882866563656748922821145 2912149922742561692115859)
  ·
    refine ⟨4368224884113842538173789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2912149922742561692115859 4368224884113842538173789)
    ·
      refine ⟨1638084331542690951815171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4368224884113842538173789 1638084331542690951815171)
      ·
        refine ⟨2457126497314036427722757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1638084331542690951815171 2457126497314036427722757)
        ·
          refine ⟨460711218246381830198017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2457126497314036427722757 460711218246381830198017)
          ·
            refine ⟨345533413684786372648513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 460711218246381830198017 345533413684786372648513)
            ·
              refine ⟨259150060263589779486385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 345533413684786372648513 259150060263589779486385)
              ·
                refine ⟨194362545197692334614789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 259150060263589779486385 194362545197692334614789)
                ·
                  refine ⟨36442977224567312740273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 194362545197692334614789 36442977224567312740273)
                  ·
                    rfl

theorem cell21_159688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 2, 4].length) (baseStart_159688 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_159688 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_159688 prefixEnd_159688 := by exact prefixLift 159688
  have htrace : WordTrace (prefixWord ++ tailWord_159688) baseStart_159688 baseEnd_159688 := by
    simpa [prefixWord, tailWord_159688, baseEnd_159688] using wordTrace_append hprefix tailTrace_159688
  have hstable : (prefixWord ++ tailWord_159688).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159688).length < 2 ^ (prefixWord ++ tailWord_159688).sum := by decide
  have hdescent : baseEnd_159688 < baseStart_159688 := by decide
  rcases family_descends (prefixWord ++ tailWord_159688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159716 : List Nat := [2, 3, 1, 1, 1, 1, 5, 2, 5]
def baseStart_159716 : Nat := 118140960795 + 159716 * 2 ^ 59
def prefixEnd_159716 : Nat := 4983230072969 + 3 ^ 40 * 159716 * 2
def baseEnd_159716 : Nat := 36449367206045486273549

theorem tailTrace_159716 : CollatzResearch.WordTrace tailWord_159716 prefixEnd_159716 36449367206045486273549 := by
  unfold tailWord_159716
  simp only [CollatzResearch.WordTrace]
  refine ⟨2912660544691842083125501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3883547392922456110834001 2912660544691842083125501)
  ·
    refine ⟨1092247704259440781172063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2912660544691842083125501 1092247704259440781172063)
    ·
      refine ⟨1638371556389161171758095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1092247704259440781172063 1638371556389161171758095)
      ·
        refine ⟨2457557334583741757637143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1638371556389161171758095 2457557334583741757637143)
        ·
          refine ⟨3686336001875612636455715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2457557334583741757637143 3686336001875612636455715)
          ·
            refine ⟨5529504002813418954683573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3686336001875612636455715 5529504002813418954683573)
            ·
              refine ⟨518391000263758027001585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5529504002813418954683573 518391000263758027001585)
              ·
                refine ⟨388793250197818520251189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 518391000263758027001585 388793250197818520251189)
                ·
                  refine ⟨36449367206045486273549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 388793250197818520251189 36449367206045486273549)
                  ·
                    rfl

theorem cell21_159716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 2, 5].length) (baseStart_159716 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_159716 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_159716 prefixEnd_159716 := by exact prefixLift 159716
  have htrace : WordTrace (prefixWord ++ tailWord_159716) baseStart_159716 baseEnd_159716 := by
    simpa [prefixWord, tailWord_159716, baseEnd_159716] using wordTrace_append hprefix tailTrace_159716
  have hstable : (prefixWord ++ tailWord_159716).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159716).length < 2 ^ (prefixWord ++ tailWord_159716).sum := by decide
  have hdescent : baseEnd_159716 < baseStart_159716 := by decide
  rcases family_descends (prefixWord ++ tailWord_159716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159719 : List Nat := [1, 1, 5, 2, 3, 1, 3, 5]
def baseStart_159719 : Nat := 118140960795 + 159719 * 2 ^ 59
def prefixEnd_159719 : Nat := 4983230072969 + 3 ^ 40 * 159719 * 2
def baseEnd_159719 : Nat := 12150017282306049241181

theorem tailTrace_159719 : CollatzResearch.WordTrace tailWord_159719 prefixEnd_159719 12150017282306049241181 := by
  unfold tailWord_159719
  simp only [CollatzResearch.WordTrace]
  refine ⟨5825430508372815678610211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3883620338915210452406807 5825430508372815678610211)
  ·
    refine ⟨8738145762559223517915317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5825430508372815678610211 8738145762559223517915317)
    ·
      refine ⟨819201165239927204804561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8738145762559223517915317 819201165239927204804561)
      ·
        refine ⟨614400873929945403603421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 819201165239927204804561 614400873929945403603421)
        ·
          refine ⟨230400327723729526351283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 614400873929945403603421 230400327723729526351283)
          ·
            refine ⟨345600491585594289526925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 230400327723729526351283 345600491585594289526925)
            ·
              refine ⟨129600184344597858572597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 345600491585594289526925 129600184344597858572597)
              ·
                refine ⟨12150017282306049241181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 129600184344597858572597 12150017282306049241181)
                ·
                  rfl

theorem cell21_159719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 3, 5].length) (baseStart_159719 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_159719 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_159719 prefixEnd_159719 := by exact prefixLift 159719
  have htrace : WordTrace (prefixWord ++ tailWord_159719) baseStart_159719 baseEnd_159719 := by
    simpa [prefixWord, tailWord_159719, baseEnd_159719] using wordTrace_append hprefix tailTrace_159719
  have hstable : (prefixWord ++ tailWord_159719).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159719).length < 2 ^ (prefixWord ++ tailWord_159719).sum := by decide
  have hdescent : baseEnd_159719 < baseStart_159719 := by decide
  rcases family_descends (prefixWord ++ tailWord_159719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159784 : List Nat := [2, 1, 5, 3, 1, 2, 1, 3, 3]
def baseStart_159784 : Nat := 118140960795 + 159784 * 2 ^ 59
def prefixEnd_159784 : Nat := 4983230072969 + 3 ^ 40 * 159784 * 2
def baseEnd_159784 : Nat := 36464885732492479140077

theorem tailTrace_159784 : CollatzResearch.WordTrace tailWord_159784 prefixEnd_159784 36464885732492479140077 := by
  unfold tailWord_159784
  simp only [CollatzResearch.WordTrace]
  refine ⟨2913900626568665889863203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3885200835424887853150937 2913900626568665889863203)
  ·
    refine ⟨4370850939852998834794805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2913900626568665889863203 4370850939852998834794805)
    ·
      refine ⟨409767275611218640762013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4370850939852998834794805 409767275611218640762013)
      ·
        refine ⟨153662728354206990285755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 409767275611218640762013 153662728354206990285755)
        ·
          refine ⟨230494092531310485428633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153662728354206990285755 230494092531310485428633)
          ·
            refine ⟨172870569398482864071475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 230494092531310485428633 172870569398482864071475)
            ·
              refine ⟨259305854097724296107213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 172870569398482864071475 259305854097724296107213)
              ·
                refine ⟨97239695286646611040205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 259305854097724296107213 97239695286646611040205)
                ·
                  refine ⟨36464885732492479140077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 97239695286646611040205 36464885732492479140077)
                  ·
                    rfl

theorem cell21_159784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 3, 3].length) (baseStart_159784 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_159784 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_159784 prefixEnd_159784 := by exact prefixLift 159784
  have htrace : WordTrace (prefixWord ++ tailWord_159784) baseStart_159784 baseEnd_159784 := by
    simpa [prefixWord, tailWord_159784, baseEnd_159784] using wordTrace_append hprefix tailTrace_159784
  have hstable : (prefixWord ++ tailWord_159784).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159784).length < 2 ^ (prefixWord ++ tailWord_159784).sum := by decide
  have hdescent : baseEnd_159784 < baseStart_159784 := by decide
  rcases family_descends (prefixWord ++ tailWord_159784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159809 : List Nat := [1, 2, 5, 1, 2, 1, 3, 1, 5]
def baseStart_159809 : Nat := 118140960795 + 159809 * 2 ^ 59
def prefixEnd_159809 : Nat := 4983230072969 + 3 ^ 40 * 159809 * 2
def baseEnd_159809 : Nat := 36470591073097991223359

theorem tailTrace_159809 : CollatzResearch.WordTrace tailWord_159809 prefixEnd_159809 36470591073097991223359 := by
  unfold tailWord_159809
  simp only [CollatzResearch.WordTrace]
  refine ⟨5828713078046761049386481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3885808718697840699590987 5828713078046761049386481)
  ·
    refine ⟨4371534808535070787039861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5828713078046761049386481 4371534808535070787039861)
    ·
      refine ⟨409831388300162886284987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4371534808535070787039861 409831388300162886284987)
      ·
        refine ⟨614747082450244329427481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 409831388300162886284987 614747082450244329427481)
        ·
          refine ⟨461060311837683247070611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 614747082450244329427481 461060311837683247070611)
          ·
            refine ⟨691590467756524870605917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 461060311837683247070611 691590467756524870605917)
            ·
              refine ⟨259346425408696826477219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 691590467756524870605917 259346425408696826477219)
              ·
                refine ⟨389019638113045239715829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 259346425408696826477219 389019638113045239715829)
                ·
                  refine ⟨36470591073097991223359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 389019638113045239715829 36470591073097991223359)
                  ·
                    rfl

theorem cell21_159809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 1, 5].length) (baseStart_159809 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_159809 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_159809 prefixEnd_159809 := by exact prefixLift 159809
  have htrace : WordTrace (prefixWord ++ tailWord_159809) baseStart_159809 baseEnd_159809 := by
    simpa [prefixWord, tailWord_159809, baseEnd_159809] using wordTrace_append hprefix tailTrace_159809
  have hstable : (prefixWord ++ tailWord_159809).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159809).length < 2 ^ (prefixWord ++ tailWord_159809).sum := by decide
  have hdescent : baseEnd_159809 < baseStart_159809 := by decide
  rcases family_descends (prefixWord ++ tailWord_159809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159894 : List Nat := [5, 3, 2, 1, 1, 1, 2, 3, 3]
def baseStart_159894 : Nat := 118140960795 + 159894 * 2 ^ 59
def prefixEnd_159894 : Nat := 4983230072969 + 3 ^ 40 * 159894 * 2
def baseEnd_159894 : Nat := 36489989231156732306519

theorem tailTrace_159894 : CollatzResearch.WordTrace tailWord_159894 prefixEnd_159894 36489989231156732306519 := by
  unfold tailWord_159894
  simp only [CollatzResearch.WordTrace]
  refine ⟨364488330171176285389421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3887875521825880377487157 364488330171176285389421)
  ·
    refine ⟨136683123814191107021033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 364488330171176285389421 136683123814191107021033)
    ·
      refine ⟨102512342860643330265775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136683123814191107021033 102512342860643330265775)
      ·
        refine ⟨153768514290964995398663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102512342860643330265775 153768514290964995398663)
        ·
          refine ⟨230652771436447493097995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153768514290964995398663 230652771436447493097995)
          ·
            refine ⟨345979157154671239646993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 230652771436447493097995 345979157154671239646993)
            ·
              refine ⟨259484367866003429735245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 345979157154671239646993 259484367866003429735245)
              ·
                refine ⟨97306637949751286150717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 259484367866003429735245 97306637949751286150717)
                ·
                  refine ⟨36489989231156732306519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 97306637949751286150717 36489989231156732306519)
                  ·
                    rfl

theorem cell21_159894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_159894 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_159894 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_159894 prefixEnd_159894 := by exact prefixLift 159894
  have htrace : WordTrace (prefixWord ++ tailWord_159894) baseStart_159894 baseEnd_159894 := by
    simpa [prefixWord, tailWord_159894, baseEnd_159894] using wordTrace_append hprefix tailTrace_159894
  have hstable : (prefixWord ++ tailWord_159894).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159894).length < 2 ^ (prefixWord ++ tailWord_159894).sum := by decide
  have hdescent : baseEnd_159894 < baseStart_159894 := by decide
  rcases family_descends (prefixWord ++ tailWord_159894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159961 : List Nat := [1, 2, 1, 2, 3, 1, 5, 3, 3]
def baseStart_159961 : Nat := 118140960795 + 159961 * 2 ^ 59
def prefixEnd_159961 : Nat := 4983230072969 + 3 ^ 40 * 159961 * 2
def baseEnd_159961 : Nat := 36505279543979504689715

theorem tailTrace_159961 : CollatzResearch.WordTrace tailWord_159961 prefixEnd_159961 36505279543979504689715 := by
  unfold tailWord_159961
  simp only [CollatzResearch.WordTrace]
  refine ⟨5834256973496091008919737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3889504648997394005946491 5834256973496091008919737)
  ·
    refine ⟨4375692730122068256689803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5834256973496091008919737 4375692730122068256689803)
    ·
      refine ⟨6563539095183102385034705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4375692730122068256689803 6563539095183102385034705)
      ·
        refine ⟨4922654321387326788776029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6563539095183102385034705 4922654321387326788776029)
        ·
          refine ⟨1845995370520247545791011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4922654321387326788776029 1845995370520247545791011)
          ·
            refine ⟨2768993055780371318686517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1845995370520247545791011 2768993055780371318686517)
            ·
              refine ⟨259593098979409811126861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2768993055780371318686517 259593098979409811126861)
              ·
                refine ⟨97347412117278679172573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 259593098979409811126861 97347412117278679172573)
                ·
                  refine ⟨36505279543979504689715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 97347412117278679172573 36505279543979504689715)
                  ·
                    rfl

theorem cell21_159961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 3, 3].length) (baseStart_159961 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_159961 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_159961 prefixEnd_159961 := by exact prefixLift 159961
  have htrace : WordTrace (prefixWord ++ tailWord_159961) baseStart_159961 baseEnd_159961 := by
    simpa [prefixWord, tailWord_159961, baseEnd_159961] using wordTrace_append hprefix tailTrace_159961
  have hstable : (prefixWord ++ tailWord_159961).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159961).length < 2 ^ (prefixWord ++ tailWord_159961).sum := by decide
  have hdescent : baseEnd_159961 < baseStart_159961 := by decide
  rcases family_descends (prefixWord ++ tailWord_159961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159964 : List Nat := [2, 2, 5, 2, 2, 1, 7]
def baseStart_159964 : Nat := 118140960795 + 159964 * 2 ^ 59
def prefixEnd_159964 : Nat := 4983230072969 + 3 ^ 40 * 159964 * 2
def baseEnd_159964 : Nat := 4056218242761351793301

theorem tailTrace_159964 : CollatzResearch.WordTrace tailWord_159964 prefixEnd_159964 4056218242761351793301 := by
  unfold tailWord_159964
  simp only [CollatzResearch.WordTrace]
  refine ⟨2917183196242611260639473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3889577594990148347519297 2917183196242611260639473)
  ·
    refine ⟨2187887397181958445479605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2917183196242611260639473 2187887397181958445479605)
    ·
      refine ⟨205114443485808604263713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2187887397181958445479605 205114443485808604263713)
      ·
        refine ⟨153835832614356453197785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205114443485808604263713 153835832614356453197785)
        ·
          refine ⟨115376874460767339898339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153835832614356453197785 115376874460767339898339)
          ·
            refine ⟨173065311691151009847509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115376874460767339898339 173065311691151009847509)
            ·
              refine ⟨4056218242761351793301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 173065311691151009847509 4056218242761351793301)
              ·
                rfl

theorem cell21_159964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 7].length) (baseStart_159964 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_159964 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_159964 prefixEnd_159964 := by exact prefixLift 159964
  have htrace : WordTrace (prefixWord ++ tailWord_159964) baseStart_159964 baseEnd_159964 := by
    simpa [prefixWord, tailWord_159964, baseEnd_159964] using wordTrace_append hprefix tailTrace_159964
  have hstable : (prefixWord ++ tailWord_159964).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159964).length < 2 ^ (prefixWord ++ tailWord_159964).sum := by decide
  have hdescent : baseEnd_159964 < baseStart_159964 := by decide
  rcases family_descends (prefixWord ++ tailWord_159964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159975 : List Nat := [1, 1, 5, 3, 1, 1, 2, 1, 6]
def baseStart_159975 : Nat := 118140960795 + 159975 * 2 ^ 59
def prefixEnd_159975 : Nat := 4983230072969 + 3 ^ 40 * 159975 * 2
def baseEnd_159975 : Nat := 36508474534718591456353

theorem tailTrace_159975 : CollatzResearch.WordTrace tailWord_159975 prefixEnd_159975 36508474534718591456353 := by
  unfold tailWord_159975
  simp only [CollatzResearch.WordTrace]
  refine ⟨5834767595445371399929379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3889845063630247599952919 5834767595445371399929379)
  ·
    refine ⟨8752151393168057099894069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5834767595445371399929379 8752151393168057099894069)
    ·
      refine ⟨820514193109505353115069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8752151393168057099894069 820514193109505353115069)
      ·
        refine ⟨307692822416064507418151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 820514193109505353115069 307692822416064507418151)
        ·
          refine ⟨461539233624096761127227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 307692822416064507418151 461539233624096761127227)
          ·
            refine ⟨692308850436145141690841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 461539233624096761127227 692308850436145141690841)
            ·
              refine ⟨519231637827108856268131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 692308850436145141690841 519231637827108856268131)
              ·
                refine ⟨778847456740663284402197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 519231637827108856268131 778847456740663284402197)
                ·
                  refine ⟨36508474534718591456353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 778847456740663284402197 36508474534718591456353)
                  ·
                    rfl

theorem cell21_159975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 1, 6].length) (baseStart_159975 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_159975 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_159975 prefixEnd_159975 := by exact prefixLift 159975
  have htrace : WordTrace (prefixWord ++ tailWord_159975) baseStart_159975 baseEnd_159975 := by
    simpa [prefixWord, tailWord_159975, baseEnd_159975] using wordTrace_append hprefix tailTrace_159975
  have hstable : (prefixWord ++ tailWord_159975).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159975).length < 2 ^ (prefixWord ++ tailWord_159975).sum := by decide
  have hdescent : baseEnd_159975 < baseStart_159975 := by decide
  rcases family_descends (prefixWord ++ tailWord_159975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159978 : List Nat := [3, 1, 3, 1, 1, 2, 5, 2, 3]
def baseStart_159978 : Nat := 118140960795 + 159978 * 2 ^ 59
def prefixEnd_159978 : Nat := 4983230072969 + 3 ^ 40 * 159978 * 2
def baseEnd_159978 : Nat := 36509159175591252906347

theorem tailTrace_159978 : CollatzResearch.WordTrace tailWord_159978 prefixEnd_159978 36509159175591252906347 := by
  unfold tailWord_159978
  simp only [CollatzResearch.WordTrace]
  refine ⟨1458719253608625728072147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3889918009623001941525725 1458719253608625728072147)
  ·
    refine ⟨2188078880412938592108221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1458719253608625728072147 2188078880412938592108221)
    ·
      refine ⟨820529580154851972040583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2188078880412938592108221 820529580154851972040583)
      ·
        refine ⟨1230794370232277958060875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 820529580154851972040583 1230794370232277958060875)
        ·
          refine ⟨1846191555348416937091313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1230794370232277958060875 1846191555348416937091313)
          ·
            refine ⟨1384643666511312702818485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1846191555348416937091313 1384643666511312702818485)
            ·
              refine ⟨129810343735435565889233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1384643666511312702818485 129810343735435565889233)
              ·
                refine ⟨97357757801576674416925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 129810343735435565889233 97357757801576674416925)
                ·
                  refine ⟨36509159175591252906347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 97357757801576674416925 36509159175591252906347)
                  ·
                    rfl

theorem cell21_159978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 5, 2, 3].length) (baseStart_159978 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_159978 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_159978 prefixEnd_159978 := by exact prefixLift 159978
  have htrace : WordTrace (prefixWord ++ tailWord_159978) baseStart_159978 baseEnd_159978 := by
    simpa [prefixWord, tailWord_159978, baseEnd_159978] using wordTrace_append hprefix tailTrace_159978
  have hstable : (prefixWord ++ tailWord_159978).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159978).length < 2 ^ (prefixWord ++ tailWord_159978).sum := by decide
  have hdescent : baseEnd_159978 < baseStart_159978 := by decide
  rcases family_descends (prefixWord ++ tailWord_159978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160003 : List Nat := [1, 1, 1, 3, 2, 3, 2, 1, 7]
def baseStart_160003 : Nat := 118140960795 + 160003 * 2 ^ 59
def prefixEnd_160003 : Nat := 4983230072969 + 3 ^ 40 * 160003 * 2
def baseEnd_160003 : Nat := 36514864516196764989629

theorem tailTrace_160003 : CollatzResearch.WordTrace tailWord_160003 prefixEnd_160003 36514864516196764989629 := by
  unfold tailWord_160003
  simp only [CollatzResearch.WordTrace]
  refine ⟨5835788839343932181948663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3890525892895954787965775 5835788839343932181948663)
  ·
    refine ⟨8753683259015898272922995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5835788839343932181948663 8753683259015898272922995)
    ·
      refine ⟨13130524888523847409384493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8753683259015898272922995 13130524888523847409384493)
      ·
        refine ⟨4923946833196442778519185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13130524888523847409384493 4923946833196442778519185)
        ·
          refine ⟨3692960124897332083889389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4923946833196442778519185 3692960124897332083889389)
          ·
            refine ⟨1384860046836499531458521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3692960124897332083889389 1384860046836499531458521)
            ·
              refine ⟨1038645035127374648593891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1384860046836499531458521 1038645035127374648593891)
              ·
                refine ⟨1557967552691061972890837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1038645035127374648593891 1557967552691061972890837)
                ·
                  refine ⟨36514864516196764989629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1557967552691061972890837 36514864516196764989629)
                  ·
                    rfl

theorem cell21_160003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 7].length) (baseStart_160003 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_160003 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_160003 prefixEnd_160003 := by exact prefixLift 160003
  have htrace : WordTrace (prefixWord ++ tailWord_160003) baseStart_160003 baseEnd_160003 := by
    simpa [prefixWord, tailWord_160003, baseEnd_160003] using wordTrace_append hprefix tailTrace_160003
  have hstable : (prefixWord ++ tailWord_160003).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160003).length < 2 ^ (prefixWord ++ tailWord_160003).sum := by decide
  have hdescent : baseEnd_160003 < baseStart_160003 := by decide
  rcases family_descends (prefixWord ++ tailWord_160003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160048 : List Nat := [2, 1, 1, 1, 2, 2, 2, 10]
def baseStart_160048 : Nat := 118140960795 + 160048 * 2 ^ 59
def prefixEnd_160048 : Nat := 4983230072969 + 3 ^ 40 * 160048 * 2
def baseEnd_160048 : Nat := 12175044709762228913179

theorem tailTrace_160048 : CollatzResearch.WordTrace tailWord_160048 prefixEnd_160048 12175044709762228913179 := by
  unfold tailWord_160048
  simp only [CollatzResearch.WordTrace]
  refine ⟨2918715062090452433668399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3891620082787269911557865 2918715062090452433668399)
  ·
    refine ⟨4378072593135678650502599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2918715062090452433668399 4378072593135678650502599)
    ·
      refine ⟨6567108889703517975753899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4378072593135678650502599 6567108889703517975753899)
      ·
        refine ⟨9850663334555276963630849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6567108889703517975753899 9850663334555276963630849)
        ·
          refine ⟨7387997500916457722723137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9850663334555276963630849 7387997500916457722723137)
          ·
            refine ⟨5540998125687343292042353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7387997500916457722723137 5540998125687343292042353)
            ·
              refine ⟨4155748594265507469031765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5540998125687343292042353 4155748594265507469031765)
              ·
                refine ⟨12175044709762228913179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 4155748594265507469031765 12175044709762228913179)
                ·
                  rfl

theorem cell21_160048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 10].length) (baseStart_160048 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_160048 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_160048 prefixEnd_160048 := by exact prefixLift 160048
  have htrace : WordTrace (prefixWord ++ tailWord_160048) baseStart_160048 baseEnd_160048 := by
    simpa [prefixWord, tailWord_160048, baseEnd_160048] using wordTrace_append hprefix tailTrace_160048
  have hstable : (prefixWord ++ tailWord_160048).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160048).length < 2 ^ (prefixWord ++ tailWord_160048).sum := by decide
  have hdescent : baseEnd_160048 < baseStart_160048 := by decide
  rcases family_descends (prefixWord ++ tailWord_160048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160085 : List Nat := [1, 3, 2, 2, 5, 1, 1, 2, 4]
def baseStart_160085 : Nat := 118140960795 + 160085 * 2 ^ 59
def prefixEnd_160085 : Nat := 4983230072969 + 3 ^ 40 * 160085 * 2
def baseEnd_160085 : Nat := 36533578033382844622795

theorem tailTrace_160085 : CollatzResearch.WordTrace tailWord_160085 prefixEnd_160085 36533578033382844622795 := by
  unfold tailWord_160085
  simp only [CollatzResearch.WordTrace]
  refine ⟨5838779625046860186433709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3892519750031240124289139 5838779625046860186433709)
  ·
    refine ⟨2189542359392572569912641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5838779625046860186433709 2189542359392572569912641)
    ·
      refine ⟨1642156769544429427434481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2189542359392572569912641 1642156769544429427434481)
      ·
        refine ⟨1231617577158322070575861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1642156769544429427434481 1231617577158322070575861)
        ·
          refine ⟨115464147858592694116487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1231617577158322070575861 115464147858592694116487)
          ·
            refine ⟨173196221787889041174731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115464147858592694116487 173196221787889041174731)
            ·
              refine ⟨259794332681833561762097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173196221787889041174731 259794332681833561762097)
              ·
                refine ⟨194845749511375171321573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 259794332681833561762097 194845749511375171321573)
                ·
                  refine ⟨36533578033382844622795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 194845749511375171321573 36533578033382844622795)
                  ·
                    rfl

theorem cell21_160085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 2, 4].length) (baseStart_160085 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_160085 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_160085 prefixEnd_160085 := by exact prefixLift 160085
  have htrace : WordTrace (prefixWord ++ tailWord_160085) baseStart_160085 baseEnd_160085 := by
    simpa [prefixWord, tailWord_160085, baseEnd_160085] using wordTrace_append hprefix tailTrace_160085
  have hstable : (prefixWord ++ tailWord_160085).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160085).length < 2 ^ (prefixWord ++ tailWord_160085).sum := by decide
  have hdescent : baseEnd_160085 < baseStart_160085 := by decide
  rcases family_descends (prefixWord ++ tailWord_160085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160158 : List Nat := [4, 3, 1, 2, 1, 1, 1, 8]
def baseStart_160158 : Nat := 118140960795 + 160158 * 2 ^ 59
def prefixEnd_160158 : Nat := 4983230072969 + 3 ^ 40 * 160158 * 2
def baseEnd_160158 : Nat := 12183412542650313301993

theorem tailTrace_160158 : CollatzResearch.WordTrace tailWord_160158 prefixEnd_160158 12183412542650313301993 := by
  unfold tailWord_160158
  simp only [CollatzResearch.WordTrace]
  refine ⟨730180269222799206730141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3894294769188262435894085 730180269222799206730141)
  ·
    refine ⟨273817600958549702523803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 730180269222799206730141 273817600958549702523803)
    ·
      refine ⟨410726401437824553785705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273817600958549702523803 410726401437824553785705)
      ·
        refine ⟨308044801078368415339279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 410726401437824553785705 308044801078368415339279)
        ·
          refine ⟨462067201617552623008919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 308044801078368415339279 462067201617552623008919)
          ·
            refine ⟨693100802426328934513379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 462067201617552623008919 693100802426328934513379)
            ·
              refine ⟨1039651203639493401770069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 693100802426328934513379 1039651203639493401770069)
              ·
                refine ⟨12183412542650313301993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1039651203639493401770069 12183412542650313301993)
                ·
                  rfl

theorem cell21_160158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 8].length) (baseStart_160158 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_160158 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_160158 prefixEnd_160158 := by exact prefixLift 160158
  have htrace : WordTrace (prefixWord ++ tailWord_160158) baseStart_160158 baseEnd_160158 := by
    simpa [prefixWord, tailWord_160158, baseEnd_160158] using wordTrace_append hprefix tailTrace_160158
  have hstable : (prefixWord ++ tailWord_160158).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160158).length < 2 ^ (prefixWord ++ tailWord_160158).sum := by decide
  have hdescent : baseEnd_160158 < baseStart_160158 := by decide
  rcases family_descends (prefixWord ++ tailWord_160158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160200 : List Nat := [2, 1, 3, 1, 3, 11]
def baseStart_160200 : Nat := 118140960795 + 160200 * 2 ^ 59
def prefixEnd_160200 : Nat := 4983230072969 + 3 ^ 40 * 160200 * 2
def baseEnd_160200 : Nat := 1354067503709933340959

theorem tailTrace_160200 : CollatzResearch.WordTrace tailWord_160200 prefixEnd_160200 1354067503709933340959 := by
  unfold tailWord_160200
  simp only [CollatzResearch.WordTrace]
  refine ⟨2921487009815117413435027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3895316013086823217913369 2921487009815117413435027)
  ·
    refine ⟨4382230514722676120152541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2921487009815117413435027 4382230514722676120152541)
    ·
      refine ⟨1643336443021003545057203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4382230514722676120152541 1643336443021003545057203)
      ·
        refine ⟨2465004664531505317585805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1643336443021003545057203 2465004664531505317585805)
        ·
          refine ⟨924376749199314494094677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2465004664531505317585805 924376749199314494094677)
          ·
            refine ⟨1354067503709933340959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 924376749199314494094677 1354067503709933340959)
            ·
              rfl

theorem cell21_160200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 11].length) (baseStart_160200 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_160200 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_160200 prefixEnd_160200 := by exact prefixLift 160200
  have htrace : WordTrace (prefixWord ++ tailWord_160200) baseStart_160200 baseEnd_160200 := by
    simpa [prefixWord, tailWord_160200, baseEnd_160200] using wordTrace_append hprefix tailTrace_160200
  have hstable : (prefixWord ++ tailWord_160200).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160200).length < 2 ^ (prefixWord ++ tailWord_160200).sum := by decide
  have hdescent : baseEnd_160200 < baseStart_160200 := by decide
  rcases family_descends (prefixWord ++ tailWord_160200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160234 : List Nat := [3, 1, 3, 1, 3, 2, 3, 5]
def baseStart_160234 : Nat := 118140960795 + 160234 * 2 ^ 59
def prefixEnd_160234 : Nat := 4983230072969 + 3 ^ 40 * 160234 * 2
def baseEnd_160234 : Nat := 12189193954463898879719

theorem tailTrace_160234 : CollatzResearch.WordTrace tailWord_160234 prefixEnd_160234 12189193954463898879719 := by
  unfold tailWord_160234
  simp only [CollatzResearch.WordTrace]
  refine ⟨1461053525376764658401939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3896142734338039089071837 1461053525376764658401939)
  ·
    refine ⟨2191580288065146987602909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1461053525376764658401939 2191580288065146987602909)
    ·
      refine ⟨821842608024430120351091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2191580288065146987602909 821842608024430120351091)
      ·
        refine ⟨1232763912036645180526637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 821842608024430120351091 1232763912036645180526637)
        ·
          refine ⟨462286467013741942697489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1232763912036645180526637 462286467013741942697489)
          ·
            refine ⟨346714850260306457023117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 462286467013741942697489 346714850260306457023117)
            ·
              refine ⟨130018068847614921383669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 346714850260306457023117 130018068847614921383669)
              ·
                refine ⟨12189193954463898879719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 130018068847614921383669 12189193954463898879719)
                ·
                  rfl

theorem cell21_160234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 3, 5].length) (baseStart_160234 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_160234 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_160234 prefixEnd_160234 := by exact prefixLift 160234
  have htrace : WordTrace (prefixWord ++ tailWord_160234) baseStart_160234 baseEnd_160234 := by
    simpa [prefixWord, tailWord_160234, baseEnd_160234] using wordTrace_append hprefix tailTrace_160234
  have hstable : (prefixWord ++ tailWord_160234).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160234).length < 2 ^ (prefixWord ++ tailWord_160234).sum := by decide
  have hdescent : baseEnd_160234 < baseStart_160234 := by decide
  rcases family_descends (prefixWord ++ tailWord_160234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160293 : List Nat := [1, 3, 1, 2, 2, 1, 6, 5]
def baseStart_160293 : Nat := 118140960795 + 160293 * 2 ^ 59
def prefixEnd_160293 : Nat := 4983230072969 + 3 ^ 40 * 160293 * 2
def baseEnd_160293 : Nat := 12193682155740235051901

theorem tailTrace_160293 : CollatzResearch.WordTrace tailWord_160293 prefixEnd_160293 12193682155740235051901 := by
  unfold tailWord_160293
  simp only [CollatzResearch.WordTrace]
  refine ⟨5846366008293311710005533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3897577338862207806670355 5846366008293311710005533)
  ·
    refine ⟨2192387253109991891252075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5846366008293311710005533 2192387253109991891252075)
    ·
      refine ⟨3288580879664987836878113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2192387253109991891252075 3288580879664987836878113)
      ·
        refine ⟨2466435659748740877658585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3288580879664987836878113 2466435659748740877658585)
        ·
          refine ⟨1849826744811555658243939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2466435659748740877658585 1849826744811555658243939)
          ·
            refine ⟨2774740117217333487365909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1849826744811555658243939 2774740117217333487365909)
            ·
              refine ⟨130065942994562507220277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2774740117217333487365909 130065942994562507220277)
              ·
                refine ⟨12193682155740235051901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 130065942994562507220277 12193682155740235051901)
                ·
                  rfl

theorem cell21_160293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 6, 5].length) (baseStart_160293 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_160293 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_160293 prefixEnd_160293 := by exact prefixLift 160293
  have htrace : WordTrace (prefixWord ++ tailWord_160293) baseStart_160293 baseEnd_160293 := by
    simpa [prefixWord, tailWord_160293, baseEnd_160293] using wordTrace_append hprefix tailTrace_160293
  have hstable : (prefixWord ++ tailWord_160293).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160293).length < 2 ^ (prefixWord ++ tailWord_160293).sum := by decide
  have hdescent : baseEnd_160293 < baseStart_160293 := by decide
  rcases family_descends (prefixWord ++ tailWord_160293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160310 : List Nat := [5, 1, 2, 1, 2, 3, 7]
def baseStart_160310 : Nat := 118140960795 + 160310 * 2 ^ 59
def prefixEnd_160310 : Nat := 4983230072969 + 3 ^ 40 * 160310 * 2
def baseEnd_160310 : Nat := 4064991788759161485815

theorem tailTrace_160310 : CollatzResearch.WordTrace tailWord_160310 prefixEnd_160310 4064991788759161485815 := by
  unfold tailWord_160310
  simp only [CollatzResearch.WordTrace]
  refine ⟨365436628076982725835899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3897990699487815742249589 365436628076982725835899)
  ·
    refine ⟨548154942115474088753849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 365436628076982725835899 548154942115474088753849)
    ·
      refine ⟨411116206586605566565387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 548154942115474088753849 411116206586605566565387)
      ·
        refine ⟨616674309879908349848081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 411116206586605566565387 616674309879908349848081)
        ·
          refine ⟨462505732409931262386061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 616674309879908349848081 462505732409931262386061)
          ·
            refine ⟨173439649653724223394773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 462505732409931262386061 173439649653724223394773)
            ·
              refine ⟨4064991788759161485815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 173439649653724223394773 4064991788759161485815)
              ·
                rfl

theorem cell21_160310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 7].length) (baseStart_160310 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_160310 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_160310 prefixEnd_160310 := by exact prefixLift 160310
  have htrace : WordTrace (prefixWord ++ tailWord_160310) baseStart_160310 baseEnd_160310 := by
    simpa [prefixWord, tailWord_160310, baseEnd_160310] using wordTrace_append hprefix tailTrace_160310
  have hstable : (prefixWord ++ tailWord_160310).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160310).length < 2 ^ (prefixWord ++ tailWord_160310).sum := by decide
  have hdescent : baseEnd_160310 < baseStart_160310 := by decide
  rcases family_descends (prefixWord ++ tailWord_160310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160352 : List Nat := [2, 1, 1, 3, 2, 1, 4, 7]
def baseStart_160352 : Nat := 118140960795 + 160352 * 2 ^ 59
def prefixEnd_160352 : Nat := 4983230072969 + 3 ^ 40 * 160352 * 2
def baseEnd_160352 : Nat := 12198170357016571224083

theorem tailTrace_160352 : CollatzResearch.WordTrace tailWord_160352 prefixEnd_160352 12198170357016571224083 := by
  unfold tailWord_160352
  simp only [CollatzResearch.WordTrace]
  refine ⟨2924258957539782393201655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3899011943386376524268873 2924258957539782393201655)
  ·
    refine ⟨4386388436309673589802483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2924258957539782393201655 4386388436309673589802483)
    ·
      refine ⟨6579582654464510384703725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4386388436309673589802483 6579582654464510384703725)
      ·
        refine ⟨2467343495424191394263897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6579582654464510384703725 2467343495424191394263897)
        ·
          refine ⟨1850507621568143545697923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2467343495424191394263897 1850507621568143545697923)
          ·
            refine ⟨2775761432352215318546885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1850507621568143545697923 2775761432352215318546885)
            ·
              refine ⟨520455268566040372227541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2775761432352215318546885 520455268566040372227541)
              ·
                refine ⟨12198170357016571224083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 520455268566040372227541 12198170357016571224083)
                ·
                  rfl

theorem cell21_160352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 7].length) (baseStart_160352 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_160352 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_160352 prefixEnd_160352 := by exact prefixLift 160352
  have htrace : WordTrace (prefixWord ++ tailWord_160352) baseStart_160352 baseEnd_160352 := by
    simpa [prefixWord, tailWord_160352, baseEnd_160352] using wordTrace_append hprefix tailTrace_160352
  have hstable : (prefixWord ++ tailWord_160352).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160352).length < 2 ^ (prefixWord ++ tailWord_160352).sum := by decide
  have hdescent : baseEnd_160352 < baseStart_160352 := by decide
  rcases family_descends (prefixWord ++ tailWord_160352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160431 : List Nat := [1, 1, 2, 1, 2, 7, 1, 2, 4]
def baseStart_160431 : Nat := 118140960795 + 160431 * 2 ^ 59
def prefixEnd_160431 : Nat := 4983230072969 + 3 ^ 40 * 160431 * 2
def baseEnd_160431 : Nat := 36612539947363131855421

theorem tailTrace_160431 : CollatzResearch.WordTrace tailWord_160431 prefixEnd_160431 36612539947363131855421 := by
  unfold tailWord_160431
  simp only [CollatzResearch.WordTrace]
  refine ⟨5851399281793361278529147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3900932854528907519019431 5851399281793361278529147)
  ·
    refine ⟨8777098922690041917793721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5851399281793361278529147 8777098922690041917793721)
    ·
      refine ⟨6582824192017531438345291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8777098922690041917793721 6582824192017531438345291)
      ·
        refine ⟨9874236288026297157517937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6582824192017531438345291 9874236288026297157517937)
        ·
          refine ⟨7405677216019722868138453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9874236288026297157517937 7405677216019722868138453)
          ·
            refine ⟨173570559750462254721995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 7405677216019722868138453 173570559750462254721995)
            ·
              refine ⟨260355839625693382082993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173570559750462254721995 260355839625693382082993)
              ·
                refine ⟨195266879719270036562245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 260355839625693382082993 195266879719270036562245)
                ·
                  refine ⟨36612539947363131855421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 195266879719270036562245 36612539947363131855421)
                  ·
                    rfl

theorem cell21_160431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 2, 4].length) (baseStart_160431 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_160431 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_160431 prefixEnd_160431 := by exact prefixLift 160431
  have htrace : WordTrace (prefixWord ++ tailWord_160431) baseStart_160431 baseEnd_160431 := by
    simpa [prefixWord, tailWord_160431, baseEnd_160431] using wordTrace_append hprefix tailTrace_160431
  have hstable : (prefixWord ++ tailWord_160431).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160431).length < 2 ^ (prefixWord ++ tailWord_160431).sum := by decide
  have hdescent : baseEnd_160431 < baseStart_160431 := by decide
  rcases family_descends (prefixWord ++ tailWord_160431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160462 : List Nat := [4, 1, 1, 1, 3, 4, 2, 5]
def baseStart_160462 : Nat := 118140960795 + 160462 * 2 ^ 59
def prefixEnd_160462 : Nat := 4983230072969 + 3 ^ 40 * 160462 * 2
def baseEnd_160462 : Nat := 12206538189904655612897

theorem tailTrace_160462 : CollatzResearch.WordTrace tailWord_160462 prefixEnd_160462 12206538189904655612897 := by
  unfold tailWord_160462
  simp only [CollatzResearch.WordTrace]
  refine ⟨731566243085131696613455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3901686629787369048605093 731566243085131696613455)
  ·
    refine ⟨1097349364627697544920183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 731566243085131696613455 1097349364627697544920183)
    ·
      refine ⟨1646024046941546317380275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1097349364627697544920183 1646024046941546317380275)
      ·
        refine ⟨2469036070412319476070413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1646024046941546317380275 2469036070412319476070413)
        ·
          refine ⟨925888526404619803526405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2469036070412319476070413 925888526404619803526405)
          ·
            refine ⟨173604098700866213161201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 925888526404619803526405 173604098700866213161201)
            ·
              refine ⟨130203074025649659870901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 173604098700866213161201 130203074025649659870901)
              ·
                refine ⟨12206538189904655612897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 130203074025649659870901 12206538189904655612897)
                ·
                  rfl

theorem cell21_160462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 2, 5].length) (baseStart_160462 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_160462 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_160462 prefixEnd_160462 := by exact prefixLift 160462
  have htrace : WordTrace (prefixWord ++ tailWord_160462) baseStart_160462 baseEnd_160462 := by
    simpa [prefixWord, tailWord_160462, baseEnd_160462] using wordTrace_append hprefix tailTrace_160462
  have hstable : (prefixWord ++ tailWord_160462).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160462).length < 2 ^ (prefixWord ++ tailWord_160462).sum := by decide
  have hdescent : baseEnd_160462 < baseStart_160462 := by decide
  rcases family_descends (prefixWord ++ tailWord_160462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160473 : List Nat := [1, 2, 1, 2, 3, 2, 1, 1, 8]
def baseStart_160473 : Nat := 118140960795 + 160473 * 2 ^ 59
def prefixEnd_160473 : Nat := 4983230072969 + 3 ^ 40 * 160473 * 2
def baseEnd_160473 : Nat := 36622124919580392155335

theorem tailTrace_160473 : CollatzResearch.WordTrace tailWord_160473 prefixEnd_160473 36622124919580392155335 := by
  unfold tailWord_160473
  simp only [CollatzResearch.WordTrace]
  refine ⟨5852931147641202451558073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3901954098427468301038715 5852931147641202451558073)
  ·
    refine ⟨4389698360730901838668555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5852931147641202451558073 4389698360730901838668555)
    ·
      refine ⟨6584547541096352758002833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4389698360730901838668555 6584547541096352758002833)
      ·
        refine ⟨4938410655822264568502125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6584547541096352758002833 4938410655822264568502125)
        ·
          refine ⟨1851903995933349213188297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4938410655822264568502125 1851903995933349213188297)
          ·
            refine ⟨1388927996950011909891223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1851903995933349213188297 1388927996950011909891223)
            ·
              refine ⟨2083391995425017864836835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1388927996950011909891223 2083391995425017864836835)
              ·
                refine ⟨3125087993137526797255253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2083391995425017864836835 3125087993137526797255253)
                ·
                  refine ⟨36622124919580392155335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3125087993137526797255253 36622124919580392155335)
                  ·
                    rfl

theorem cell21_160473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 8].length) (baseStart_160473 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_160473 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_160473 prefixEnd_160473 := by exact prefixLift 160473
  have htrace : WordTrace (prefixWord ++ tailWord_160473) baseStart_160473 baseEnd_160473 := by
    simpa [prefixWord, tailWord_160473, baseEnd_160473] using wordTrace_append hprefix tailTrace_160473
  have hstable : (prefixWord ++ tailWord_160473).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160473).length < 2 ^ (prefixWord ++ tailWord_160473).sum := by decide
  have hdescent : baseEnd_160473 < baseStart_160473 := by decide
  rcases family_descends (prefixWord ++ tailWord_160473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160490 : List Nat := [3, 1, 3, 1, 1, 1, 1, 6, 4]
def baseStart_160490 : Nat := 118140960795 + 160490 * 2 ^ 59
def prefixEnd_160490 : Nat := 4983230072969 + 3 ^ 40 * 160490 * 2
def baseEnd_160490 : Nat := 36626004551192140371967

theorem tailTrace_160490 : CollatzResearch.WordTrace tailWord_160490 prefixEnd_160490 36626004551192140371967 := by
  unfold tailWord_160490
  simp only [CollatzResearch.WordTrace]
  refine ⟨1463387797144903588731731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3902367459053076236617949 1463387797144903588731731)
  ·
    refine ⟨2195081695717355383097597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1463387797144903588731731 2195081695717355383097597)
    ·
      refine ⟨823155635894008268661599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2195081695717355383097597 823155635894008268661599)
      ·
        refine ⟨1234733453841012402992399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 823155635894008268661599 1234733453841012402992399)
        ·
          refine ⟨1852100180761518604488599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1234733453841012402992399 1852100180761518604488599)
          ·
            refine ⟨2778150271142277906732899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1852100180761518604488599 2778150271142277906732899)
            ·
              refine ⟨4167225406713416860099349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2778150271142277906732899 4167225406713416860099349)
              ·
                refine ⟨195338690939691415317157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4167225406713416860099349 195338690939691415317157)
                ·
                  refine ⟨36626004551192140371967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 195338690939691415317157 36626004551192140371967)
                  ·
                    rfl

theorem cell21_160490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 6, 4].length) (baseStart_160490 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_160490 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_160490 prefixEnd_160490 := by exact prefixLift 160490
  have htrace : WordTrace (prefixWord ++ tailWord_160490) baseStart_160490 baseEnd_160490 := by
    simpa [prefixWord, tailWord_160490, baseEnd_160490] using wordTrace_append hprefix tailTrace_160490
  have hstable : (prefixWord ++ tailWord_160490).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160490).length < 2 ^ (prefixWord ++ tailWord_160490).sum := by decide
  have hdescent : baseEnd_160490 < baseStart_160490 := by decide
  rcases family_descends (prefixWord ++ tailWord_160490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160504 : List Nat := [2, 1, 2, 1, 1, 2, 6, 6]
def baseStart_160504 : Nat := 118140960795 + 160504 * 2 ^ 59
def prefixEnd_160504 : Nat := 4983230072969 + 3 ^ 40 * 160504 * 2
def baseEnd_160504 : Nat := 12209733180643742379535

theorem tailTrace_160504 : CollatzResearch.WordTrace tailWord_160504 prefixEnd_160504 12209733180643742379535 := by
  unfold tailWord_160504
  simp only [CollatzResearch.WordTrace]
  refine ⟨2927030905264447372968283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3902707873685929830624377 2927030905264447372968283)
  ·
    refine ⟨4390546357896671059452425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2927030905264447372968283 4390546357896671059452425)
    ·
      refine ⟨3292909768422503294589319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4390546357896671059452425 3292909768422503294589319)
      ·
        refine ⟨4939364652633754941883979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3292909768422503294589319 4939364652633754941883979)
        ·
          refine ⟨7409046978950632412825969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4939364652633754941883979 7409046978950632412825969)
          ·
            refine ⟨5556785234212974309619477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7409046978950632412825969 5556785234212974309619477)
            ·
              refine ⟨260474307853733170763413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5556785234212974309619477 260474307853733170763413)
              ·
                refine ⟨12209733180643742379535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 260474307853733170763413 12209733180643742379535)
                ·
                  rfl

theorem cell21_160504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 6].length) (baseStart_160504 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_160504 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_160504 prefixEnd_160504 := by exact prefixLift 160504
  have htrace : WordTrace (prefixWord ++ tailWord_160504) baseStart_160504 baseEnd_160504 := by
    simpa [prefixWord, tailWord_160504, baseEnd_160504] using wordTrace_append hprefix tailTrace_160504
  have hstable : (prefixWord ++ tailWord_160504).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160504).length < 2 ^ (prefixWord ++ tailWord_160504).sum := by decide
  have hdescent : baseEnd_160504 < baseStart_160504 := by decide
  rcases family_descends (prefixWord ++ tailWord_160504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160611 : List Nat := [1, 1, 1, 5, 3, 1, 1, 3, 5]
def baseStart_160611 : Nat := 118140960795 + 160611 * 2 ^ 59
def prefixEnd_160611 : Nat := 4983230072969 + 3 ^ 40 * 160611 * 2
def baseEnd_160611 : Nat := 36653618399722818855053

theorem tailTrace_160611 : CollatzResearch.WordTrace tailWord_160611 prefixEnd_160611 36653618399722818855053 := by
  unfold tailWord_160611
  simp only [CollatzResearch.WordTrace]
  refine ⟨5857964421141252020081687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3905309614094168013387791 5857964421141252020081687)
  ·
    refine ⟨8786946631711878030122531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5857964421141252020081687 8786946631711878030122531)
    ·
      refine ⟨13180419947567817045183797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8786946631711878030122531 13180419947567817045183797)
      ·
        refine ⟨1235664370084482847985981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13180419947567817045183797 1235664370084482847985981)
        ·
          refine ⟨463374138781681067994743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1235664370084482847985981 463374138781681067994743)
          ·
            refine ⟨695061208172521601992115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 463374138781681067994743 695061208172521601992115)
            ·
              refine ⟨1042591812258782402988173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 695061208172521601992115 1042591812258782402988173)
              ·
                refine ⟨390971929597043401120565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1042591812258782402988173 390971929597043401120565)
                ·
                  refine ⟨36653618399722818855053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 390971929597043401120565 36653618399722818855053)
                  ·
                    rfl

theorem cell21_160611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 3, 5].length) (baseStart_160611 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_160611 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_160611 prefixEnd_160611 := by exact prefixLift 160611
  have htrace : WordTrace (prefixWord ++ tailWord_160611) baseStart_160611 baseEnd_160611 := by
    simpa [prefixWord, tailWord_160611, baseEnd_160611] using wordTrace_append hprefix tailTrace_160611
  have hstable : (prefixWord ++ tailWord_160611).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160611).length < 2 ^ (prefixWord ++ tailWord_160611).sum := by decide
  have hdescent : baseEnd_160611 < baseStart_160611 := by decide
  rcases family_descends (prefixWord ++ tailWord_160611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160645 : List Nat := [1, 3, 1, 1, 3, 5, 1, 3, 3]
def baseStart_160645 : Nat := 118140960795 + 160645 * 2 ^ 59
def prefixEnd_160645 : Nat := 4983230072969 + 3 ^ 40 * 160645 * 2
def baseEnd_160645 : Nat := 36661377662946315288317

theorem tailTrace_160645 : CollatzResearch.WordTrace tailWord_160645 prefixEnd_160645 36661377662946315288317 := by
  unfold tailWord_160645
  simp only [CollatzResearch.WordTrace]
  refine ⟨5859204503018075826819389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3906136335345383884546259 5859204503018075826819389)
  ·
    refine ⟨2197201688631778435057271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5859204503018075826819389 2197201688631778435057271)
    ·
      refine ⟨3295802532947667652585907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2197201688631778435057271 3295802532947667652585907)
      ·
        refine ⟨4943703799421501478878861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3295802532947667652585907 4943703799421501478878861)
        ·
          refine ⟨1853888924783063054579573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4943703799421501478878861 1853888924783063054579573)
          ·
            refine ⟨173802086698412161366835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1853888924783063054579573 173802086698412161366835)
            ·
              refine ⟨260703130047618242050253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173802086698412161366835 260703130047618242050253)
              ·
                refine ⟨97763673767856840768845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 260703130047618242050253 97763673767856840768845)
                ·
                  refine ⟨36661377662946315288317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 97763673767856840768845 36661377662946315288317)
                  ·
                    rfl

theorem cell21_160645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 3, 3].length) (baseStart_160645 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_160645 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_160645 prefixEnd_160645 := by exact prefixLift 160645
  have htrace : WordTrace (prefixWord ++ tailWord_160645) baseStart_160645 baseEnd_160645 := by
    simpa [prefixWord, tailWord_160645, baseEnd_160645] using wordTrace_append hprefix tailTrace_160645
  have hstable : (prefixWord ++ tailWord_160645).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160645).length < 2 ^ (prefixWord ++ tailWord_160645).sum := by decide
  have hdescent : baseEnd_160645 < baseStart_160645 := by decide
  rcases family_descends (prefixWord ++ tailWord_160645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160662 : List Nat := [5, 3, 1, 1, 1, 1, 3, 1, 5]
def baseStart_160662 : Nat := 118140960795 + 160662 * 2 ^ 59
def prefixEnd_160662 : Nat := 4983230072969 + 3 ^ 40 * 160662 * 2
def baseEnd_160662 : Nat := 36665257294558063504949

theorem tailTrace_160662 : CollatzResearch.WordTrace tailWord_160662 prefixEnd_160662 36665257294558063504949 := by
  unfold tailWord_160662
  simp only [CollatzResearch.WordTrace]
  refine ⟨366239033997280483136765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3906549695970991820125493 366239033997280483136765)
  ·
    refine ⟨137339637748980181176287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 366239033997280483136765 137339637748980181176287)
    ·
      refine ⟨206009456623470271764431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137339637748980181176287 206009456623470271764431)
      ·
        refine ⟨309014184935205407646647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206009456623470271764431 309014184935205407646647)
        ·
          refine ⟨463521277402808111469971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 309014184935205407646647 463521277402808111469971)
          ·
            refine ⟨695281916104212167204957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 463521277402808111469971 695281916104212167204957)
            ·
              refine ⟨260730718539079562701859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 695281916104212167204957 260730718539079562701859)
              ·
                refine ⟨391096077808619344052789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 260730718539079562701859 391096077808619344052789)
                ·
                  refine ⟨36665257294558063504949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 391096077808619344052789 36665257294558063504949)
                  ·
                    rfl

theorem cell21_160662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_160662 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_160662 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_160662 prefixEnd_160662 := by exact prefixLift 160662
  have htrace : WordTrace (prefixWord ++ tailWord_160662) baseStart_160662 baseEnd_160662 := by
    simpa [prefixWord, tailWord_160662, baseEnd_160662] using wordTrace_append hprefix tailTrace_160662
  have hstable : (prefixWord ++ tailWord_160662).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160662).length < 2 ^ (prefixWord ++ tailWord_160662).sum := by decide
  have hdescent : baseEnd_160662 < baseStart_160662 := by decide
  rcases family_descends (prefixWord ++ tailWord_160662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160673 : List Nat := [1, 2, 3, 4, 1, 2, 2, 6]
def baseStart_160673 : Nat := 118140960795 + 160673 * 2 ^ 59
def prefixEnd_160673 : Nat := 4983230072969 + 3 ^ 40 * 160673 * 2
def baseEnd_160673 : Nat := 12222589214808162940531

theorem tailTrace_160673 : CollatzResearch.WordTrace tailWord_160673 prefixEnd_160673 12222589214808162940531 := by
  unfold tailWord_160673
  simp only [CollatzResearch.WordTrace]
  refine ⟨5860225746916636608838673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3906817164611091072559115 5860225746916636608838673)
  ·
    refine ⟨4395169310187477456629005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5860225746916636608838673 4395169310187477456629005)
    ·
      refine ⟨1648188491320304046235877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4395169310187477456629005 1648188491320304046235877)
      ·
        refine ⟨309035342122557008669227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1648188491320304046235877 309035342122557008669227)
        ·
          refine ⟨463553013183835513003841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 309035342122557008669227 463553013183835513003841)
          ·
            refine ⟨347664759887876634752881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 463553013183835513003841 347664759887876634752881)
            ·
              refine ⟨260748569915907476064661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 347664759887876634752881 260748569915907476064661)
              ·
                refine ⟨12222589214808162940531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 260748569915907476064661 12222589214808162940531)
                ·
                  rfl

theorem cell21_160673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 6].length) (baseStart_160673 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_160673 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_160673 prefixEnd_160673 := by exact prefixLift 160673
  have htrace : WordTrace (prefixWord ++ tailWord_160673) baseStart_160673 baseEnd_160673 := by
    simpa [prefixWord, tailWord_160673, baseEnd_160673] using wordTrace_append hprefix tailTrace_160673
  have hstable : (prefixWord ++ tailWord_160673).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160673).length < 2 ^ (prefixWord ++ tailWord_160673).sum := by decide
  have hdescent : baseEnd_160673 < baseStart_160673 := by decide
  rcases family_descends (prefixWord ++ tailWord_160673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160715 : List Nat := [1, 1, 1, 1, 3, 14]
def baseStart_160715 : Nat := 118140960795 + 160715 * 2 ^ 59
def prefixEnd_160715 : Nat := 4983230072969 + 3 ^ 40 * 160715 * 2
def baseEnd_160715 : Nat := 1358420467283027745241

theorem tailTrace_160715 : CollatzResearch.WordTrace tailWord_160715 prefixEnd_160715 1358420467283027745241 := by
  unfold tailWord_160715
  simp only [CollatzResearch.WordTrace]
  refine ⟨5861757612764477781867599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3907838408509651854578399 5861757612764477781867599)
  ·
    refine ⟨8792636419146716672801399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5861757612764477781867599 8792636419146716672801399)
    ·
      refine ⟨13188954628720075009202099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8792636419146716672801399 13188954628720075009202099)
      ·
        refine ⟨19783431943080112513803149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13188954628720075009202099 19783431943080112513803149)
        ·
          refine ⟨7418786978655042192676181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19783431943080112513803149 7418786978655042192676181)
          ·
            refine ⟨1358420467283027745241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 7418786978655042192676181 1358420467283027745241)
            ·
              rfl

theorem cell21_160715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 14].length) (baseStart_160715 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_160715 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_160715 prefixEnd_160715 := by exact prefixLift 160715
  have htrace : WordTrace (prefixWord ++ tailWord_160715) baseStart_160715 baseEnd_160715 := by
    simpa [prefixWord, tailWord_160715, baseEnd_160715] using wordTrace_append hprefix tailTrace_160715
  have hstable : (prefixWord ++ tailWord_160715).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160715).length < 2 ^ (prefixWord ++ tailWord_160715).sum := by decide
  have hdescent : baseEnd_160715 < baseStart_160715 := by decide
  rcases family_descends (prefixWord ++ tailWord_160715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160718 : List Nat := [4, 1, 1, 1, 2, 3, 1, 4, 4]
def baseStart_160718 : Nat := 118140960795 + 160718 * 2 ^ 59
def prefixEnd_160718 : Nat := 4983230072969 + 3 ^ 40 * 160718 * 2
def baseEnd_160718 : Nat := 36678037257514410571501

theorem tailTrace_160718 : CollatzResearch.WordTrace tailWord_160718 prefixEnd_160718 36678037257514410571501 := by
  unfold tailWord_160718
  simp only [CollatzResearch.WordTrace]
  refine ⟨732733378969201161778351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3907911354502406196151205 732733378969201161778351)
  ·
    refine ⟨1099100068453801742667527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 732733378969201161778351 1099100068453801742667527)
    ·
      refine ⟨1648650102680702614001291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1099100068453801742667527 1648650102680702614001291)
      ·
        refine ⟨2472975154021053921001937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1648650102680702614001291 2472975154021053921001937)
        ·
          refine ⟨1854731365515790440751453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2472975154021053921001937 1854731365515790440751453)
          ·
            refine ⟨695524262068421415281795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1854731365515790440751453 695524262068421415281795)
            ·
              refine ⟨1043286393102632122922693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 695524262068421415281795 1043286393102632122922693)
              ·
                refine ⟨195616198706743523048005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1043286393102632122922693 195616198706743523048005)
                ·
                  refine ⟨36678037257514410571501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 195616198706743523048005 36678037257514410571501)
                  ·
                    rfl

theorem cell21_160718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 4, 4].length) (baseStart_160718 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_160718 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_160718 prefixEnd_160718 := by exact prefixLift 160718
  have htrace : WordTrace (prefixWord ++ tailWord_160718) baseStart_160718 baseEnd_160718 := by
    simpa [prefixWord, tailWord_160718, baseEnd_160718] using wordTrace_append hprefix tailTrace_160718
  have hstable : (prefixWord ++ tailWord_160718).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160718).length < 2 ^ (prefixWord ++ tailWord_160718).sum := by decide
  have hdescent : baseEnd_160718 < baseStart_160718 := by decide
  rcases family_descends (prefixWord ++ tailWord_160718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160780 : List Nat := [2, 2, 1, 2, 3, 2, 2, 4, 3]
def baseStart_160780 : Nat := 118140960795 + 160780 * 2 ^ 59
def prefixEnd_160780 : Nat := 4983230072969 + 3 ^ 40 * 160780 * 2
def baseEnd_160780 : Nat := 36692186502216080538041

theorem tailTrace_160780 : CollatzResearch.WordTrace tailWord_160780 prefixEnd_160780 36692186502216080538041 := by
  unfold tailWord_160780
  simp only [CollatzResearch.WordTrace]
  refine ⟨2932064178764496941491897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3909418905019329255322529 2932064178764496941491897)
  ·
    refine ⟨2199048134073372706118923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2932064178764496941491897 2199048134073372706118923)
    ·
      refine ⟨3298572201110059059178385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2199048134073372706118923 3298572201110059059178385)
      ·
        refine ⟨2473929150832544294383789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3298572201110059059178385 2473929150832544294383789)
        ·
          refine ⟨927723431562204110393921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2473929150832544294383789 927723431562204110393921)
          ·
            refine ⟨695792573671653082795441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 927723431562204110393921 695792573671653082795441)
            ·
              refine ⟨521844430253739812096581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 695792573671653082795441 521844430253739812096581)
              ·
                refine ⟨97845830672576214768109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 521844430253739812096581 97845830672576214768109)
                ·
                  refine ⟨36692186502216080538041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 97845830672576214768109 36692186502216080538041)
                  ·
                    rfl

theorem cell21_160780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 4, 3].length) (baseStart_160780 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_160780 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_160780 prefixEnd_160780 := by exact prefixLift 160780
  have htrace : WordTrace (prefixWord ++ tailWord_160780) baseStart_160780 baseEnd_160780 := by
    simpa [prefixWord, tailWord_160780, baseEnd_160780] using wordTrace_append hprefix tailTrace_160780
  have hstable : (prefixWord ++ tailWord_160780).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160780).length < 2 ^ (prefixWord ++ tailWord_160780).sum := by decide
  have hdescent : baseEnd_160780 < baseStart_160780 := by decide
  rcases family_descends (prefixWord ++ tailWord_160780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160786 : List Nat := [3, 2, 5, 1, 1, 1, 3, 1, 4]
def baseStart_160786 : Nat := 118140960795 + 160786 * 2 ^ 59
def prefixEnd_160786 : Nat := 4983230072969 + 3 ^ 40 * 160786 * 2
def baseEnd_160786 : Nat := 36693555783961403438029

theorem tailTrace_160786 : CollatzResearch.WordTrace tailWord_160786 prefixEnd_160786 36693555783961403438029 := by
  unfold tailWord_160786
  simp only [CollatzResearch.WordTrace]
  refine ⟨1466086798876814226925553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3909564797004837938468141 1466086798876814226925553)
  ·
    refine ⟨1099565099157610670194165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1466086798876814226925553 1099565099157610670194165)
    ·
      refine ⟨103084228046026000330703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1099565099157610670194165 103084228046026000330703)
      ·
        refine ⟨154626342069039000496055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103084228046026000330703 154626342069039000496055)
        ·
          refine ⟨231939513103558500744083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154626342069039000496055 231939513103558500744083)
          ·
            refine ⟨347909269655337751116125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231939513103558500744083 347909269655337751116125)
            ·
              refine ⟨130465976120751656668547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 347909269655337751116125 130465976120751656668547)
              ·
                refine ⟨195698964181127485002821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130465976120751656668547 195698964181127485002821)
                ·
                  refine ⟨36693555783961403438029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 195698964181127485002821 36693555783961403438029)
                  ·
                    rfl

theorem cell21_160786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 3, 1, 4].length) (baseStart_160786 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_160786 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_160786 prefixEnd_160786 := by exact prefixLift 160786
  have htrace : WordTrace (prefixWord ++ tailWord_160786) baseStart_160786 baseEnd_160786 := by
    simpa [prefixWord, tailWord_160786, baseEnd_160786] using wordTrace_append hprefix tailTrace_160786
  have hstable : (prefixWord ++ tailWord_160786).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160786).length < 2 ^ (prefixWord ++ tailWord_160786).sum := by decide
  have hdescent : baseEnd_160786 < baseStart_160786 := by decide
  rcases family_descends (prefixWord ++ tailWord_160786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160839 : List Nat := [1, 1, 4, 1, 3, 2, 3, 1, 5]
def baseStart_160839 : Nat := 118140960795 + 160839 * 2 ^ 59
def prefixEnd_160839 : Nat := 4983230072969 + 3 ^ 40 * 160839 * 2
def baseEnd_160839 : Nat := 36705651106045089054587

theorem tailTrace_160839 : CollatzResearch.WordTrace tailWord_160839 prefixEnd_160839 36705651106045089054587 := by
  unfold tailWord_160839
  simp only [CollatzResearch.WordTrace]
  refine ⟨5866280264315246959381571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3910853509543497972921047 5866280264315246959381571)
  ·
    refine ⟨8799420396472870439072357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5866280264315246959381571 8799420396472870439072357)
    ·
      refine ⟨1649891324338663207326067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8799420396472870439072357 1649891324338663207326067)
      ·
        refine ⟨2474836986507994810989101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1649891324338663207326067 2474836986507994810989101)
        ·
          refine ⟨928063869940498054120913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2474836986507994810989101 928063869940498054120913)
          ·
            refine ⟨696047902455373540590685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 928063869940498054120913 696047902455373540590685)
            ·
              refine ⟨261017963420765077721507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 696047902455373540590685 261017963420765077721507)
              ·
                refine ⟨391526945131147616582261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 261017963420765077721507 391526945131147616582261)
                ·
                  refine ⟨36705651106045089054587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 391526945131147616582261 36705651106045089054587)
                  ·
                    rfl

theorem cell21_160839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 1, 5].length) (baseStart_160839 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_160839 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_160839 prefixEnd_160839 := by exact prefixLift 160839
  have htrace : WordTrace (prefixWord ++ tailWord_160839) baseStart_160839 baseEnd_160839 := by
    simpa [prefixWord, tailWord_160839, baseEnd_160839] using wordTrace_append hprefix tailTrace_160839
  have hstable : (prefixWord ++ tailWord_160839).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160839).length < 2 ^ (prefixWord ++ tailWord_160839).sum := by decide
  have hdescent : baseEnd_160839 < baseStart_160839 := by decide
  rcases family_descends (prefixWord ++ tailWord_160839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160901 : List Nat := [1, 3, 1, 1, 6, 2, 1, 6]
def baseStart_160901 : Nat := 118140960795 + 160901 * 2 ^ 59
def prefixEnd_160901 : Nat := 4983230072969 + 3 ^ 40 * 160901 * 2
def baseEnd_160901 : Nat := 12239933450248919673709

theorem tailTrace_160901 : CollatzResearch.WordTrace tailWord_160901 prefixEnd_160901 12239933450248919673709 := by
  unfold tailWord_160901
  simp only [CollatzResearch.WordTrace]
  refine ⟨5868541590090631548138557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3912361060060421032092371 5868541590090631548138557)
  ·
    refine ⟨2200703096283986830551959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5868541590090631548138557 2200703096283986830551959)
    ·
      refine ⟨3301054644425980245827939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2200703096283986830551959 3301054644425980245827939)
      ·
        refine ⟨4951581966638970368741909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3301054644425980245827939 4951581966638970368741909)
        ·
          refine ⟨232105404686201736034777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 4951581966638970368741909 232105404686201736034777)
          ·
            refine ⟨174079053514651302026083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 232105404686201736034777 174079053514651302026083)
            ·
              refine ⟨261118580271976953039125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174079053514651302026083 261118580271976953039125)
              ·
                refine ⟨12239933450248919673709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 261118580271976953039125 12239933450248919673709)
                ·
                  rfl

theorem cell21_160901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 6].length) (baseStart_160901 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_160901 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_160901 prefixEnd_160901 := by exact prefixLift 160901
  have htrace : WordTrace (prefixWord ++ tailWord_160901) baseStart_160901 baseEnd_160901 := by
    simpa [prefixWord, tailWord_160901, baseEnd_160901] using wordTrace_append hprefix tailTrace_160901
  have hstable : (prefixWord ++ tailWord_160901).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160901).length < 2 ^ (prefixWord ++ tailWord_160901).sum := by decide
  have hdescent : baseEnd_160901 < baseStart_160901 := by decide
  rcases family_descends (prefixWord ++ tailWord_160901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160929 : List Nat := [1, 2, 3, 3, 1, 1, 2, 2, 6]
def baseStart_160929 : Nat := 118140960795 + 160929 * 2 ^ 59
def prefixEnd_160929 : Nat := 4983230072969 + 3 ^ 40 * 160929 * 2
def baseEnd_160929 : Nat := 36726190332224932554403

theorem tailTrace_160929 : CollatzResearch.WordTrace tailWord_160929 prefixEnd_160929 36726190332224932554403 := by
  unfold tailWord_160929
  simp only [CollatzResearch.WordTrace]
  refine ⟨5869562833989192330157841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3913041889326128220105227 5869562833989192330157841)
  ·
    refine ⟨4402172125491894247618381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5869562833989192330157841 4402172125491894247618381)
    ·
      refine ⟨1650814547059460342856893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4402172125491894247618381 1650814547059460342856893)
      ·
        refine ⟨619055455147297628571335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1650814547059460342856893 619055455147297628571335)
        ·
          refine ⟨928583182720946442857003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 619055455147297628571335 928583182720946442857003)
          ·
            refine ⟨1392874774081419664285505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 928583182720946442857003 1392874774081419664285505)
            ·
              refine ⟨1044656080561064748214129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1392874774081419664285505 1044656080561064748214129)
              ·
                refine ⟨783492060420798561160597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1044656080561064748214129 783492060420798561160597)
                ·
                  refine ⟨36726190332224932554403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 783492060420798561160597 36726190332224932554403)
                  ·
                    rfl

theorem cell21_160929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 2, 6].length) (baseStart_160929 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_160929 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_160929 prefixEnd_160929 := by exact prefixLift 160929
  have htrace : WordTrace (prefixWord ++ tailWord_160929) baseStart_160929 baseEnd_160929 := by
    simpa [prefixWord, tailWord_160929, baseEnd_160929] using wordTrace_append hprefix tailTrace_160929
  have hstable : (prefixWord ++ tailWord_160929).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160929).length < 2 ^ (prefixWord ++ tailWord_160929).sum := by decide
  have hdescent : baseEnd_160929 < baseStart_160929 := by decide
  rcases family_descends (prefixWord ++ tailWord_160929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160932 : List Nat := [2, 3, 1, 2, 3, 1, 1, 5, 3]
def baseStart_160932 : Nat := 118140960795 + 160932 * 2 ^ 59
def prefixEnd_160932 : Nat := 4983230072969 + 3 ^ 40 * 160932 * 2
def baseEnd_160932 : Nat := 36726874973097594004397

theorem tailTrace_160932 : CollatzResearch.WordTrace tailWord_160932 prefixEnd_160932 36726874973097594004397 := by
  unfold tailWord_160932
  simp only [CollatzResearch.WordTrace]
  refine ⟨2934836126489161921258525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3913114835318882561678033 2934836126489161921258525)
  ·
    refine ⟨1100563547433435720471947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2934836126489161921258525 1100563547433435720471947)
    ·
      refine ⟨1650845321150153580707921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1100563547433435720471947 1650845321150153580707921)
      ·
        refine ⟨1238133990862615185530941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1650845321150153580707921 1238133990862615185530941)
        ·
          refine ⟨464300246573480694574103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1238133990862615185530941 464300246573480694574103)
          ·
            refine ⟨696450369860221041861155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 464300246573480694574103 696450369860221041861155)
            ·
              refine ⟨1044675554790331562791733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 696450369860221041861155 1044675554790331562791733)
              ·
                refine ⟨97938333261593584011725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1044675554790331562791733 97938333261593584011725)
                ·
                  refine ⟨36726874973097594004397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 97938333261593584011725 36726874973097594004397)
                  ·
                    rfl

theorem cell21_160932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 5, 3].length) (baseStart_160932 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_160932 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_160932 prefixEnd_160932 := by exact prefixLift 160932
  have htrace : WordTrace (prefixWord ++ tailWord_160932) baseStart_160932 baseEnd_160932 := by
    simpa [prefixWord, tailWord_160932, baseEnd_160932] using wordTrace_append hprefix tailTrace_160932
  have hstable : (prefixWord ++ tailWord_160932).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160932).length < 2 ^ (prefixWord ++ tailWord_160932).sum := by decide
  have hdescent : baseEnd_160932 < baseStart_160932 := by decide
  rcases family_descends (prefixWord ++ tailWord_160932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160946 : List Nat := [3, 2, 1, 1, 1, 4, 3, 2, 4]
def baseStart_160946 : Nat := 118140960795 + 160946 * 2 ^ 59
def prefixEnd_160946 : Nat := 4983230072969 + 3 ^ 40 * 160946 * 2
def baseEnd_160946 : Nat := 36730069963836680771035

theorem tailTrace_160946 : CollatzResearch.WordTrace tailWord_160946 prefixEnd_160946 36730069963836680771035 := by
  unfold tailWord_160946
  simp only [CollatzResearch.WordTrace]
  refine ⟨1467545718731901058381673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3913455249951736155684461 1467545718731901058381673)
  ·
    refine ⟨1100659289048925793786255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1467545718731901058381673 1100659289048925793786255)
    ·
      refine ⟨1650988933573388690679383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1100659289048925793786255 1650988933573388690679383)
      ·
        refine ⟨2476483400360083036019075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1650988933573388690679383 2476483400360083036019075)
        ·
          refine ⟨3714725100540124554028613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2476483400360083036019075 3714725100540124554028613)
          ·
            refine ⟨696510956351273353880365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3714725100540124554028613 696510956351273353880365)
            ·
              refine ⟨261191608631727507705137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 696510956351273353880365 261191608631727507705137)
              ·
                refine ⟨195893706473795630778853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 261191608631727507705137 195893706473795630778853)
                ·
                  refine ⟨36730069963836680771035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 195893706473795630778853 36730069963836680771035)
                  ·
                    rfl

theorem cell21_160946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 2, 4].length) (baseStart_160946 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_160946 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_160946 prefixEnd_160946 := by exact prefixLift 160946
  have htrace : WordTrace (prefixWord ++ tailWord_160946) baseStart_160946 baseEnd_160946 := by
    simpa [prefixWord, tailWord_160946, baseEnd_160946] using wordTrace_append hprefix tailTrace_160946
  have hstable : (prefixWord ++ tailWord_160946).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160946).length < 2 ^ (prefixWord ++ tailWord_160946).sum := by decide
  have hdescent : baseEnd_160946 < baseStart_160946 := by decide
  rcases family_descends (prefixWord ++ tailWord_160946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161160 : List Nat := [2, 1, 3, 3, 1, 2, 3, 3, 3]
def baseStart_161160 : Nat := 118140960795 + 161160 * 2 ^ 59
def prefixEnd_161160 : Nat := 4983230072969 + 3 ^ 40 * 161160 * 2
def baseEnd_161160 : Nat := 36778907679419864203931

theorem tailTrace_161160 : CollatzResearch.WordTrace tailWord_161160 prefixEnd_161160 36778907679419864203931 := by
  unfold tailWord_161160
  simp only [CollatzResearch.WordTrace]
  refine ⟨2938994048076159390908467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3918658730768212521211289 2938994048076159390908467)
  ·
    refine ⟨4408491072114239086362701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2938994048076159390908467 4408491072114239086362701)
    ·
      refine ⟨1653184152042839657386013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4408491072114239086362701 1653184152042839657386013)
      ·
        refine ⟨619944057016064871519755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1653184152042839657386013 619944057016064871519755)
        ·
          refine ⟨929916085524097307279633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 619944057016064871519755 929916085524097307279633)
          ·
            refine ⟨697437064143072980459725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 929916085524097307279633 697437064143072980459725)
            ·
              refine ⟨261538899053652367672397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 697437064143072980459725 261538899053652367672397)
              ·
                refine ⟨98077087145119637877149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 261538899053652367672397 98077087145119637877149)
                ·
                  refine ⟨36778907679419864203931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 98077087145119637877149 36778907679419864203931)
                  ·
                    rfl

theorem cell21_161160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 3, 3].length) (baseStart_161160 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_161160 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_161160 prefixEnd_161160 := by exact prefixLift 161160
  have htrace : WordTrace (prefixWord ++ tailWord_161160) baseStart_161160 baseEnd_161160 := by
    simpa [prefixWord, tailWord_161160, baseEnd_161160] using wordTrace_append hprefix tailTrace_161160
  have hstable : (prefixWord ++ tailWord_161160).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161160).length < 2 ^ (prefixWord ++ tailWord_161160).sum := by decide
  have hdescent : baseEnd_161160 < baseStart_161160 := by decide
  rcases family_descends (prefixWord ++ tailWord_161160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161216 : List Nat := [2, 1, 1, 2, 3, 1, 2, 1, 8]
def baseStart_161216 : Nat := 118140960795 + 161216 * 2 ^ 59
def prefixEnd_161216 : Nat := 4983230072969 + 3 ^ 40 * 161216 * 2
def baseEnd_161216 : Nat := 36791687642376211270483

theorem tailTrace_161216 : CollatzResearch.WordTrace tailWord_161216 prefixEnd_161216 36791687642376211270483 := by
  unfold tailWord_161216
  simp only [CollatzResearch.WordTrace]
  refine ⟨2940015291974720172927751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3920020389299626897237001 2940015291974720172927751)
  ·
    refine ⟨4410022937962080259391627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2940015291974720172927751 4410022937962080259391627)
    ·
      refine ⟨6615034406943120389087441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4410022937962080259391627 6615034406943120389087441)
      ·
        refine ⟨4961275805207340291815581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6615034406943120389087441 4961275805207340291815581)
        ·
          refine ⟨1860478426952752609430843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4961275805207340291815581 1860478426952752609430843)
          ·
            refine ⟨2790717640429128914146265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1860478426952752609430843 2790717640429128914146265)
            ·
              refine ⟨2093038230321846685609699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2790717640429128914146265 2093038230321846685609699)
              ·
                refine ⟨3139557345482770028414549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2093038230321846685609699 3139557345482770028414549)
                ·
                  refine ⟨36791687642376211270483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3139557345482770028414549 36791687642376211270483)
                  ·
                    rfl

theorem cell21_161216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 8].length) (baseStart_161216 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_161216 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_161216 prefixEnd_161216 := by exact prefixLift 161216
  have htrace : WordTrace (prefixWord ++ tailWord_161216) baseStart_161216 baseEnd_161216 := by
    simpa [prefixWord, tailWord_161216, baseEnd_161216] using wordTrace_append hprefix tailTrace_161216
  have hstable : (prefixWord ++ tailWord_161216).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161216).length < 2 ^ (prefixWord ++ tailWord_161216).sum := by decide
  have hdescent : baseEnd_161216 < baseStart_161216 := by decide
  rcases family_descends (prefixWord ++ tailWord_161216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161264 : List Nat := [2, 1, 1, 1, 3, 5, 3, 5]
def baseStart_161264 : Nat := 118140960795 + 161264 * 2 ^ 59
def prefixEnd_161264 : Nat := 4983230072969 + 3 ^ 40 * 161264 * 2
def baseEnd_161264 : Nat := 12267547298779598156795

theorem tailTrace_161264 : CollatzResearch.WordTrace tailWord_161264 prefixEnd_161264 12267547298779598156795 := by
  unfold tailWord_161264
  simp only [CollatzResearch.WordTrace]
  refine ⟨2940890643887772271801423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3921187525183696362401897 2940890643887772271801423)
  ·
    refine ⟨4411335965831658407702135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2940890643887772271801423 4411335965831658407702135)
    ·
      refine ⟨6617003948747487611553203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4411335965831658407702135 6617003948747487611553203)
      ·
        refine ⟨9925505923121231417329805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6617003948747487611553203 9925505923121231417329805)
        ·
          refine ⟨3722064721170461781498677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9925505923121231417329805 3722064721170461781498677)
          ·
            refine ⟨348943567609730792015501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3722064721170461781498677 348943567609730792015501)
            ·
              refine ⟨130853837853649047005813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 348943567609730792015501 130853837853649047005813)
              ·
                refine ⟨12267547298779598156795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 130853837853649047005813 12267547298779598156795)
                ·
                  rfl

theorem cell21_161264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 3, 5].length) (baseStart_161264 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_161264 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_161264 prefixEnd_161264 := by exact prefixLift 161264
  have htrace : WordTrace (prefixWord ++ tailWord_161264) baseStart_161264 baseEnd_161264 := by
    simpa [prefixWord, tailWord_161264, baseEnd_161264] using wordTrace_append hprefix tailTrace_161264
  have hstable : (prefixWord ++ tailWord_161264).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161264).length < 2 ^ (prefixWord ++ tailWord_161264).sum := by decide
  have hdescent : baseEnd_161264 < baseStart_161264 := by decide
  rcases family_descends (prefixWord ++ tailWord_161264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161284 : List Nat := [2, 3, 2, 3, 3, 1, 1, 2, 4]
def baseStart_161284 : Nat := 118140960795 + 161284 * 2 ^ 59
def prefixEnd_161284 : Nat := 4983230072969 + 3 ^ 40 * 161284 * 2
def baseEnd_161284 : Nat := 36807206168823204137011

theorem tailTrace_161284 : CollatzResearch.WordTrace tailWord_161284 prefixEnd_161284 36807206168823204137011 := by
  unfold tailWord_161284
  simp only [CollatzResearch.WordTrace]
  refine ⟨2941255373851543979665453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3921673831802058639553937 2941255373851543979665453)
  ·
    refine ⟨1102970765194328992374545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2941255373851543979665453 1102970765194328992374545)
    ·
      refine ⟨827228073895746744280909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1102970765194328992374545 827228073895746744280909)
      ·
        refine ⟨310210527710905029105341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 827228073895746744280909 310210527710905029105341)
        ·
          refine ⟨116328947891589385914503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 310210527710905029105341 116328947891589385914503)
          ·
            refine ⟨174493421837384078871755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116328947891589385914503 174493421837384078871755)
            ·
              refine ⟨261740132756076118307633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174493421837384078871755 261740132756076118307633)
              ·
                refine ⟨196305099567057088730725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 261740132756076118307633 196305099567057088730725)
                ·
                  refine ⟨36807206168823204137011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 196305099567057088730725 36807206168823204137011)
                  ·
                    rfl

theorem cell21_161284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 2, 4].length) (baseStart_161284 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_161284 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_161284 prefixEnd_161284 := by exact prefixLift 161284
  have htrace : WordTrace (prefixWord ++ tailWord_161284) baseStart_161284 baseEnd_161284 := by
    simpa [prefixWord, tailWord_161284, baseEnd_161284] using wordTrace_append hprefix tailTrace_161284
  have hstable : (prefixWord ++ tailWord_161284).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161284).length < 2 ^ (prefixWord ++ tailWord_161284).sum := by decide
  have hdescent : baseEnd_161284 < baseStart_161284 := by decide
  rcases family_descends (prefixWord ++ tailWord_161284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161340 : List Nat := [2, 2, 2, 2, 4, 2, 7]
def baseStart_161340 : Nat := 118140960795 + 161340 * 2 ^ 59
def prefixEnd_161340 : Nat := 4983230072969 + 3 ^ 40 * 161340 * 2
def baseEnd_161340 : Nat := 4091109570197727911507

theorem tailTrace_161340 : CollatzResearch.WordTrace tailWord_161340 prefixEnd_161340 4091109570197727911507 := by
  unfold tailWord_161340
  simp only [CollatzResearch.WordTrace]
  refine ⟨2942276617750104761684737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3923035490333473015579649 2942276617750104761684737)
  ·
    refine ⟨2206707463312578571263553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2942276617750104761684737 2206707463312578571263553)
    ·
      refine ⟨1655030597484433928447665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2206707463312578571263553 1655030597484433928447665)
      ·
        refine ⟨1241272948113325446335749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1655030597484433928447665 1241272948113325446335749)
        ·
          refine ⟨232738677771248521187953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1241272948113325446335749 232738677771248521187953)
          ·
            refine ⟨174554008328436390890965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 232738677771248521187953 174554008328436390890965)
            ·
              refine ⟨4091109570197727911507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 174554008328436390890965 4091109570197727911507)
              ·
                rfl

theorem cell21_161340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 7].length) (baseStart_161340 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_161340 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_161340 prefixEnd_161340 := by exact prefixLift 161340
  have htrace : WordTrace (prefixWord ++ tailWord_161340) baseStart_161340 baseEnd_161340 := by
    simpa [prefixWord, tailWord_161340, baseEnd_161340] using wordTrace_append hprefix tailTrace_161340
  have hstable : (prefixWord ++ tailWord_161340).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161340).length < 2 ^ (prefixWord ++ tailWord_161340).sum := by decide
  have hdescent : baseEnd_161340 < baseStart_161340 := by decide
  rcases family_descends (prefixWord ++ tailWord_161340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161357 : List Nat := [1, 6, 1, 1, 3, 1, 2, 6]
def baseStart_161357 : Nat := 118140960795 + 161357 * 2 ^ 59
def prefixEnd_161357 : Nat := 4983230072969 + 3 ^ 40 * 161357 * 2
def baseEnd_161357 : Nat := 12274621921130433140065

theorem tailTrace_161357 : CollatzResearch.WordTrace tailWord_161357 prefixEnd_161357 12274621921130433140065 := by
  unfold tailWord_161357
  simp only [CollatzResearch.WordTrace]
  refine ⟨5885173276438621426738325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3923448850959080951158883 5885173276438621426738325)
  ·
    refine ⟨275867497333060379378359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 5885173276438621426738325 275867497333060379378359)
    ·
      refine ⟨413801245999590569067539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 275867497333060379378359 413801245999590569067539)
      ·
        refine ⟨620701868999385853601309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 413801245999590569067539 620701868999385853601309)
        ·
          refine ⟨232763200874769695100491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 620701868999385853601309 232763200874769695100491)
          ·
            refine ⟨349144801312154542650737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 232763200874769695100491 349144801312154542650737)
            ·
              refine ⟨261858600984115906988053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 349144801312154542650737 261858600984115906988053)
              ·
                refine ⟨12274621921130433140065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 261858600984115906988053 12274621921130433140065)
                ·
                  rfl

theorem cell21_161357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 6].length) (baseStart_161357 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_161357 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_161357 prefixEnd_161357 := by exact prefixLift 161357
  have htrace : WordTrace (prefixWord ++ tailWord_161357) baseStart_161357 baseEnd_161357 := by
    simpa [prefixWord, tailWord_161357, baseEnd_161357] using wordTrace_append hprefix tailTrace_161357
  have hstable : (prefixWord ++ tailWord_161357).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161357).length < 2 ^ (prefixWord ++ tailWord_161357).sum := by decide
  have hdescent : baseEnd_161357 < baseStart_161357 := by decide
  rcases family_descends (prefixWord ++ tailWord_161357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161405 : List Nat := [1, 4, 1, 1, 4, 3, 2, 2, 3]
def baseStart_161405 : Nat := 118140960795 + 161405 * 2 ^ 59
def prefixEnd_161405 : Nat := 4983230072969 + 3 ^ 40 * 161405 * 2
def baseEnd_161405 : Nat := 36834820017353882620097

theorem tailTrace_161405 : CollatzResearch.WordTrace tailWord_161405 prefixEnd_161405 36834820017353882620097 := by
  unfold tailWord_161405
  simp only [CollatzResearch.WordTrace]
  refine ⟨5886923980264725624485669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3924615986843150416323779 5886923980264725624485669)
  ·
    refine ⟨1103798246299636054591063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5886923980264725624485669 1103798246299636054591063)
    ·
      refine ⟨1655697369449454081886595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1103798246299636054591063 1655697369449454081886595)
      ·
        refine ⟨2483546054174181122829893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1655697369449454081886595 2483546054174181122829893)
        ·
          refine ⟨465664885157658960530605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2483546054174181122829893 465664885157658960530605)
          ·
            refine ⟨174624331934122110198977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 465664885157658960530605 174624331934122110198977)
            ·
              refine ⟨130968248950591582649233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 174624331934122110198977 130968248950591582649233)
              ·
                refine ⟨98226186712943686986925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 130968248950591582649233 98226186712943686986925)
                ·
                  refine ⟨36834820017353882620097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 98226186712943686986925 36834820017353882620097)
                  ·
                    rfl

theorem cell21_161405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 2, 2, 3].length) (baseStart_161405 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_161405 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_161405 prefixEnd_161405 := by exact prefixLift 161405
  have htrace : WordTrace (prefixWord ++ tailWord_161405) baseStart_161405 baseEnd_161405 := by
    simpa [prefixWord, tailWord_161405, baseEnd_161405] using wordTrace_append hprefix tailTrace_161405
  have hstable : (prefixWord ++ tailWord_161405).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161405).length < 2 ^ (prefixWord ++ tailWord_161405).sum := by decide
  have hdescent : baseEnd_161405 < baseStart_161405 := by decide
  rcases family_descends (prefixWord ++ tailWord_161405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161492 : List Nat := [2, 4, 1, 3, 1, 2, 1, 7]
def baseStart_161492 : Nat := 118140960795 + 161492 * 2 ^ 59
def prefixEnd_161492 : Nat := 4983230072969 + 3 ^ 40 * 161492 * 2
def baseEnd_161492 : Nat := 12284891534220354889973

theorem tailTrace_161492 : CollatzResearch.WordTrace tailWord_161492 prefixEnd_161492 12284891534220354889973 := by
  unfold tailWord_161492
  simp only [CollatzResearch.WordTrace]
  refine ⟨2945048565474769741451365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3926731420633026321935153 2945048565474769741451365)
  ·
    refine ⟨552196606026519326522131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2945048565474769741451365 552196606026519326522131)
    ·
      refine ⟨828294909039778989783197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 552196606026519326522131 828294909039778989783197)
      ·
        refine ⟨310610590889917121168699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 828294909039778989783197 310610590889917121168699)
        ·
          refine ⟨465915886334875681753049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 310610590889917121168699 465915886334875681753049)
          ·
            refine ⟨349436914751156761314787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 465915886334875681753049 349436914751156761314787)
            ·
              refine ⟨524155372126735141972181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 349436914751156761314787 524155372126735141972181)
              ·
                refine ⟨12284891534220354889973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 524155372126735141972181 12284891534220354889973)
                ·
                  rfl

theorem cell21_161492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 7].length) (baseStart_161492 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_161492 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_161492 prefixEnd_161492 := by exact prefixLift 161492
  have htrace : WordTrace (prefixWord ++ tailWord_161492) baseStart_161492 baseEnd_161492 := by
    simpa [prefixWord, tailWord_161492, baseEnd_161492] using wordTrace_append hprefix tailTrace_161492
  have hstable : (prefixWord ++ tailWord_161492).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161492).length < 2 ^ (prefixWord ++ tailWord_161492).sum := by decide
  have hdescent : baseEnd_161492 < baseStart_161492 := by decide
  rcases family_descends (prefixWord ++ tailWord_161492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161703 : List Nat := [1, 1, 6, 1, 2, 1, 1, 8]
def baseStart_161703 : Nat := 118140960795 + 161703 * 2 ^ 59
def prefixEnd_161703 : Nat := 4983230072969 + 3 ^ 40 * 161703 * 2
def baseEnd_161703 : Nat := 12300942559123862217607

theorem tailTrace_161703 : CollatzResearch.WordTrace tailWord_161703 prefixEnd_161703 12300942559123862217607 := by
  unfold tailWord_161703
  simp only [CollatzResearch.WordTrace]
  refine ⟨5897792933185122518833763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3931861955456748345889175 5897792933185122518833763)
  ·
    refine ⟨8846689399777683778250645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5897792933185122518833763 8846689399777683778250645)
    ·
      refine ⟨414688565614578927105499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 8846689399777683778250645 414688565614578927105499)
      ·
        refine ⟨622032848421868390658249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 414688565614578927105499 622032848421868390658249)
        ·
          refine ⟨466524636316401292993687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 622032848421868390658249 466524636316401292993687)
          ·
            refine ⟨699786954474601939490531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 466524636316401292993687 699786954474601939490531)
            ·
              refine ⟨1049680431711902909235797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 699786954474601939490531 1049680431711902909235797)
              ·
                refine ⟨12300942559123862217607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1049680431711902909235797 12300942559123862217607)
                ·
                  rfl

theorem cell21_161703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 8].length) (baseStart_161703 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_161703 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_161703 prefixEnd_161703 := by exact prefixLift 161703
  have htrace : WordTrace (prefixWord ++ tailWord_161703) baseStart_161703 baseEnd_161703 := by
    simpa [prefixWord, tailWord_161703, baseEnd_161703] using wordTrace_append hprefix tailTrace_161703
  have hstable : (prefixWord ++ tailWord_161703).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161703).length < 2 ^ (prefixWord ++ tailWord_161703).sum := by decide
  have hdescent : baseEnd_161703 < baseStart_161703 := by decide
  rcases family_descends (prefixWord ++ tailWord_161703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161793 : List Nat := [1, 2, 4, 1, 2, 1, 1, 2, 7]
def baseStart_161793 : Nat := 118140960795 + 161793 * 2 ^ 59
def prefixEnd_161793 : Nat := 4983230072969 + 3 ^ 40 * 161793 * 2
def baseEnd_161793 : Nat := 36923366903551430152637

theorem tailTrace_161793 : CollatzResearch.WordTrace tailWord_161793 prefixEnd_161793 36923366903551430152637 := by
  unfold tailWord_161793
  simp only [CollatzResearch.WordTrace]
  refine ⟨5901075502859067889610033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3934050335239378593073355 5901075502859067889610033)
  ·
    refine ⟨4425806627144300917207525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5901075502859067889610033 4425806627144300917207525)
    ·
      refine ⟨829838742589556421976411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4425806627144300917207525 829838742589556421976411)
      ·
        refine ⟨1244758113884334632964617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 829838742589556421976411 1244758113884334632964617)
        ·
          refine ⟨933568585413250974723463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1244758113884334632964617 933568585413250974723463)
          ·
            refine ⟨1400352878119876462085195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 933568585413250974723463 1400352878119876462085195)
            ·
              refine ⟨2100529317179814693127793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1400352878119876462085195 2100529317179814693127793)
              ·
                refine ⟨1575396987884861019845845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2100529317179814693127793 1575396987884861019845845)
                ·
                  refine ⟨36923366903551430152637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1575396987884861019845845 36923366903551430152637)
                  ·
                    rfl

theorem cell21_161793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 7].length) (baseStart_161793 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_161793 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_161793 prefixEnd_161793 := by exact prefixLift 161793
  have htrace : WordTrace (prefixWord ++ tailWord_161793) baseStart_161793 baseEnd_161793 := by
    simpa [prefixWord, tailWord_161793, baseEnd_161793] using wordTrace_append hprefix tailTrace_161793
  have hstable : (prefixWord ++ tailWord_161793).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161793).length < 2 ^ (prefixWord ++ tailWord_161793).sum := by decide
  have hdescent : baseEnd_161793 < baseStart_161793 := by decide
  rcases family_descends (prefixWord ++ tailWord_161793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161796 : List Nat := [2, 3, 2, 4, 1, 1, 8]
def baseStart_161796 : Nat := 118140960795 + 161796 * 2 ^ 59
def prefixEnd_161796 : Nat := 4983230072969 + 3 ^ 40 * 161796 * 2
def baseEnd_161796 : Nat := 4102672393824899066959

theorem tailTrace_161796 : CollatzResearch.WordTrace tailWord_161796 prefixEnd_161796 4102672393824899066959 := by
  unfold tailWord_161796
  simp only [CollatzResearch.WordTrace]
  refine ⟨2950592460924099700984621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3934123281232132934646161 2950592460924099700984621)
  ·
    refine ⟨1106472172846537387869233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2950592460924099700984621 1106472172846537387869233)
    ·
      refine ⟨829854129634903040901925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1106472172846537387869233 829854129634903040901925)
      ·
        refine ⟨155597649306544320169111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 829854129634903040901925 155597649306544320169111)
        ·
          refine ⟨233396473959816480253667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155597649306544320169111 233396473959816480253667)
          ·
            refine ⟨350094710939724720380501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233396473959816480253667 350094710939724720380501)
            ·
              refine ⟨4102672393824899066959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 350094710939724720380501 4102672393824899066959)
              ·
                rfl

theorem cell21_161796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 8].length) (baseStart_161796 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_161796 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_161796 prefixEnd_161796 := by exact prefixLift 161796
  have htrace : WordTrace (prefixWord ++ tailWord_161796) baseStart_161796 baseEnd_161796 := by
    simpa [prefixWord, tailWord_161796, baseEnd_161796] using wordTrace_append hprefix tailTrace_161796
  have hstable : (prefixWord ++ tailWord_161796).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161796).length < 2 ^ (prefixWord ++ tailWord_161796).sum := by decide
  have hdescent : baseEnd_161796 < baseStart_161796 := by decide
  rcases family_descends (prefixWord ++ tailWord_161796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161917 : List Nat := [1, 4, 1, 1, 3, 3, 2, 2, 4]
def baseStart_161917 : Nat := 118140960795 + 161917 * 2 ^ 59
def prefixEnd_161917 : Nat := 4983230072969 + 3 ^ 40 * 161917 * 2
def baseEnd_161917 : Nat := 36951665392954770085717

theorem tailTrace_161917 : CollatzResearch.WordTrace tailWord_161917 prefixEnd_161917 36951665392954770085717 := by
  unfold tailWord_161917
  simp only [CollatzResearch.WordTrace]
  refine ⟨5905598154409837067124005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3937065436273224711416003 5905598154409837067124005)
  ·
    refine ⟨1107299653951844450085751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5905598154409837067124005 1107299653951844450085751)
    ·
      refine ⟨1660949480927766675128627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1107299653951844450085751 1660949480927766675128627)
      ·
        refine ⟨2491424221391650012692941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1660949480927766675128627 2491424221391650012692941)
        ·
          refine ⟨934284083021868754759853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2491424221391650012692941 934284083021868754759853)
          ·
            refine ⟨350356531133200783034945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 934284083021868754759853 350356531133200783034945)
            ·
              refine ⟨262767398349900587276209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 350356531133200783034945 262767398349900587276209)
              ·
                refine ⟨197075548762425440457157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 262767398349900587276209 197075548762425440457157)
                ·
                  refine ⟨36951665392954770085717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 197075548762425440457157 36951665392954770085717)
                  ·
                    rfl

theorem cell21_161917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 2, 4].length) (baseStart_161917 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_161917 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_161917 prefixEnd_161917 := by exact prefixLift 161917
  have htrace : WordTrace (prefixWord ++ tailWord_161917) baseStart_161917 baseEnd_161917 := by
    simpa [prefixWord, tailWord_161917, baseEnd_161917] using wordTrace_append hprefix tailTrace_161917
  have hstable : (prefixWord ++ tailWord_161917).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161917).length < 2 ^ (prefixWord ++ tailWord_161917).sum := by decide
  have hdescent : baseEnd_161917 < baseStart_161917 := by decide
  rcases family_descends (prefixWord ++ tailWord_161917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162035 : List Nat := [1, 1, 1, 2, 2, 4, 1, 3, 6]
def baseStart_162035 : Nat := 118140960795 + 162035 * 2 ^ 59
def prefixEnd_162035 : Nat := 4983230072969 + 3 ^ 40 * 162035 * 2
def baseEnd_162035 : Nat := 36978594600612787118809

theorem tailTrace_162035 : CollatzResearch.WordTrace tailWord_162035 prefixEnd_162035 36978594600612787118809 := by
  unfold tailWord_162035
  simp only [CollatzResearch.WordTrace]
  refine ⟨5909901967982343219919559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3939934645321562146613039 5909901967982343219919559)
  ·
    refine ⟨8864852951973514829879339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5909901967982343219919559 8864852951973514829879339)
    ·
      refine ⟨13297279427960272244819009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8864852951973514829879339 13297279427960272244819009)
      ·
        refine ⟨9972959570970204183614257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13297279427960272244819009 9972959570970204183614257)
        ·
          refine ⟨7479719678227653137710693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9972959570970204183614257 7479719678227653137710693)
          ·
            refine ⟨1402447439667684963320755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7479719678227653137710693 1402447439667684963320755)
            ·
              refine ⟨2103671159501527444981133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1402447439667684963320755 2103671159501527444981133)
              ·
                refine ⟨788876684813072791867925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2103671159501527444981133 788876684813072791867925)
                ·
                  refine ⟨36978594600612787118809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 788876684813072791867925 36978594600612787118809)
                  ·
                    rfl

theorem cell21_162035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 3, 6].length) (baseStart_162035 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_162035 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_162035 prefixEnd_162035 := by exact prefixLift 162035
  have htrace : WordTrace (prefixWord ++ tailWord_162035) baseStart_162035 baseEnd_162035 := by
    simpa [prefixWord, tailWord_162035, baseEnd_162035] using wordTrace_append hprefix tailTrace_162035
  have hstable : (prefixWord ++ tailWord_162035).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162035).length < 2 ^ (prefixWord ++ tailWord_162035).sum := by decide
  have hdescent : baseEnd_162035 < baseStart_162035 := by decide
  rcases family_descends (prefixWord ++ tailWord_162035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162038 : List Nat := [5, 1, 1, 1, 1, 1, 5, 1, 5]
def baseStart_162038 : Nat := 118140960795 + 162038 * 2 ^ 59
def prefixEnd_162038 : Nat := 4983230072969 + 3 ^ 40 * 162038 * 2
def baseEnd_162038 : Nat := 36979279241485448568803

theorem tailTrace_162038 : CollatzResearch.WordTrace tailWord_162038 prefixEnd_162038 36979279241485448568803 := by
  unfold tailWord_162038
  simp only [CollatzResearch.WordTrace]
  refine ⟨369375711685717170767423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3940007591314316488185845 369375711685717170767423)
  ·
    refine ⟨554063567528575756151135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 369375711685717170767423 554063567528575756151135)
    ·
      refine ⟨831095351292863634226703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 554063567528575756151135 831095351292863634226703)
      ·
        refine ⟨1246643026939295451340055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 831095351292863634226703 1246643026939295451340055)
        ·
          refine ⟨1869964540408943177010083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1246643026939295451340055 1869964540408943177010083)
          ·
            refine ⟨2804946810613414765515125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1869964540408943177010083 2804946810613414765515125)
            ·
              refine ⟨262963763495007634267043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2804946810613414765515125 262963763495007634267043)
              ·
                refine ⟨394445645242511451400565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 262963763495007634267043 394445645242511451400565)
                ·
                  refine ⟨36979279241485448568803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 394445645242511451400565 36979279241485448568803)
                  ·
                    rfl

theorem cell21_162038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_162038 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_162038 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_162038 prefixEnd_162038 := by exact prefixLift 162038
  have htrace : WordTrace (prefixWord ++ tailWord_162038) baseStart_162038 baseEnd_162038 := by
    simpa [prefixWord, tailWord_162038, baseEnd_162038] using wordTrace_append hprefix tailTrace_162038
  have hstable : (prefixWord ++ tailWord_162038).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162038).length < 2 ^ (prefixWord ++ tailWord_162038).sum := by decide
  have hdescent : baseEnd_162038 < baseStart_162038 := by decide
  rcases family_descends (prefixWord ++ tailWord_162038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162100 : List Nat := [2, 5, 1, 1, 1, 4, 1, 6]
def baseStart_162100 : Nat := 118140960795 + 162100 * 2 ^ 59
def prefixEnd_162100 : Nat := 4983230072969 + 3 ^ 40 * 162100 * 2
def baseEnd_162100 : Nat := 12331142828729039511781

theorem tailTrace_162100 : CollatzResearch.WordTrace tailWord_162100 prefixEnd_162100 12331142828729039511781 := by
  unfold tailWord_162100
  simp only [CollatzResearch.WordTrace]
  refine ⟨2956136356373429660517877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3941515141831239547357169 2956136356373429660517877)
  ·
    refine ⟨277137783410009030673551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2956136356373429660517877 277137783410009030673551)
    ·
      refine ⟨415706675115013546010327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277137783410009030673551 415706675115013546010327)
      ·
        refine ⟨623560012672520319015491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 415706675115013546010327 623560012672520319015491)
        ·
          refine ⟨935340019008780478523237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 623560012672520319015491 935340019008780478523237)
          ·
            refine ⟨175376253564146339723107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 935340019008780478523237 175376253564146339723107)
            ·
              refine ⟨263064380346219509584661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 175376253564146339723107 263064380346219509584661)
              ·
                refine ⟨12331142828729039511781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 263064380346219509584661 12331142828729039511781)
                ·
                  rfl

theorem cell21_162100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 6].length) (baseStart_162100 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_162100 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_162100 prefixEnd_162100 := by exact prefixLift 162100
  have htrace : WordTrace (prefixWord ++ tailWord_162100) baseStart_162100 baseEnd_162100 := by
    simpa [prefixWord, tailWord_162100, baseEnd_162100] using wordTrace_append hprefix tailTrace_162100
  have hstable : (prefixWord ++ tailWord_162100).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162100).length < 2 ^ (prefixWord ++ tailWord_162100).sum := by decide
  have hdescent : baseEnd_162100 < baseStart_162100 := by decide
  rcases family_descends (prefixWord ++ tailWord_162100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162173 : List Nat := [1, 4, 1, 1, 2, 3, 2, 2, 5]
def baseStart_162173 : Nat := 118140960795 + 162173 * 2 ^ 59
def prefixEnd_162173 : Nat := 4983230072969 + 3 ^ 40 * 162173 * 2
def baseEnd_162173 : Nat := 37010088080755213818527

theorem tailTrace_162173 : CollatzResearch.WordTrace tailWord_162173 prefixEnd_162173 37010088080755213818527 := by
  unfold tailWord_162173
  simp only [CollatzResearch.WordTrace]
  refine ⟨5914935241482392788443173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3943290160988261858962115 5914935241482392788443173)
  ·
    refine ⟨1109050357777948647833095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5914935241482392788443173 1109050357777948647833095)
    ·
      refine ⟨1663575536666922971749643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1109050357777948647833095 1663575536666922971749643)
      ·
        refine ⟨2495363305000384457624465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1663575536666922971749643 2495363305000384457624465)
        ·
          refine ⟨1871522478750288343218349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2495363305000384457624465 1871522478750288343218349)
          ·
            refine ⟨701820929531358128706881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1871522478750288343218349 701820929531358128706881)
            ·
              refine ⟨526365697148518596530161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 701820929531358128706881 526365697148518596530161)
              ·
                refine ⟨394774272861388947397621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 526365697148518596530161 394774272861388947397621)
                ·
                  refine ⟨37010088080755213818527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 394774272861388947397621 37010088080755213818527)
                  ·
                    rfl

theorem cell21_162173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 2, 5].length) (baseStart_162173 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_162173 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_162173 prefixEnd_162173 := by exact prefixLift 162173
  have htrace : WordTrace (prefixWord ++ tailWord_162173) baseStart_162173 baseEnd_162173 := by
    simpa [prefixWord, tailWord_162173, baseEnd_162173] using wordTrace_append hprefix tailTrace_162173
  have hstable : (prefixWord ++ tailWord_162173).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162173).length < 2 ^ (prefixWord ++ tailWord_162173).sum := by decide
  have hdescent : baseEnd_162173 < baseStart_162173 := by decide
  rcases family_descends (prefixWord ++ tailWord_162173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162187 : List Nat := [1, 1, 1, 1, 4, 4, 1, 2, 6]
def baseStart_162187 : Nat := 118140960795 + 162187 * 2 ^ 59
def prefixEnd_162187 : Nat := 4983230072969 + 3 ^ 40 * 162187 * 2
def baseEnd_162187 : Nat := 37013283071494300585165

theorem tailTrace_162187 : CollatzResearch.WordTrace tailWord_162187 prefixEnd_162187 37013283071494300585165 := by
  unfold tailWord_162187
  simp only [CollatzResearch.WordTrace]
  refine ⟨5915445863431673179452815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3943630575621115452968543 5915445863431673179452815)
  ·
    refine ⟨8873168795147509769179223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5915445863431673179452815 8873168795147509769179223)
    ·
      refine ⟨13309753192721264653768835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8873168795147509769179223 13309753192721264653768835)
      ·
        refine ⟨19964629789081896980653253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13309753192721264653768835 19964629789081896980653253)
        ·
          refine ⟨3743368085452855683872485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19964629789081896980653253 3743368085452855683872485)
          ·
            refine ⟨701881516022410440726091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3743368085452855683872485 701881516022410440726091)
            ·
              refine ⟨1052822274033615661089137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 701881516022410440726091 1052822274033615661089137)
              ·
                refine ⟨789616705525211745816853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1052822274033615661089137 789616705525211745816853)
                ·
                  refine ⟨37013283071494300585165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 789616705525211745816853 37013283071494300585165)
                  ·
                    rfl

theorem cell21_162187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 2, 6].length) (baseStart_162187 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_162187 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_162187 prefixEnd_162187 := by exact prefixLift 162187
  have htrace : WordTrace (prefixWord ++ tailWord_162187) baseStart_162187 baseEnd_162187 := by
    simpa [prefixWord, tailWord_162187, baseEnd_162187] using wordTrace_append hprefix tailTrace_162187
  have hstable : (prefixWord ++ tailWord_162187).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162187).length < 2 ^ (prefixWord ++ tailWord_162187).sum := by decide
  have hdescent : baseEnd_162187 < baseStart_162187 := by decide
  rcases family_descends (prefixWord ++ tailWord_162187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162207 : List Nat := [1, 1, 2, 5, 1, 1, 5, 2, 3]
def baseStart_162207 : Nat := 118140960795 + 162207 * 2 ^ 59
def prefixEnd_162207 : Nat := 4983230072969 + 3 ^ 40 * 162207 * 2
def baseEnd_162207 : Nat := 37017847343978710251791

theorem tailTrace_162207 : CollatzResearch.WordTrace tailWord_162207 prefixEnd_162207 37017847343978710251791 := by
  unfold tailWord_162207
  simp only [CollatzResearch.WordTrace]
  refine ⟨5916175323359216595180875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3944116882239477730120583 5916175323359216595180875)
  ·
    refine ⟨8874262985038824892771313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5916175323359216595180875 8874262985038824892771313)
    ·
      refine ⟨6655697238779118669578485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8874262985038824892771313 6655697238779118669578485)
      ·
        refine ⟨623971616135542375272983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6655697238779118669578485 623971616135542375272983)
        ·
          refine ⟨935957424203313562909475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 623971616135542375272983 935957424203313562909475)
          ·
            refine ⟨1403936136304970344364213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 935957424203313562909475 1403936136304970344364213)
            ·
              refine ⟨131619012778590969784145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1403936136304970344364213 131619012778590969784145)
              ·
                refine ⟨98714259583943227338109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 131619012778590969784145 98714259583943227338109)
                ·
                  refine ⟨37017847343978710251791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 98714259583943227338109 37017847343978710251791)
                  ·
                    rfl

theorem cell21_162207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 5, 2, 3].length) (baseStart_162207 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_162207 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_162207 prefixEnd_162207 := by exact prefixLift 162207
  have htrace : WordTrace (prefixWord ++ tailWord_162207) baseStart_162207 baseEnd_162207 := by
    simpa [prefixWord, tailWord_162207, baseEnd_162207] using wordTrace_append hprefix tailTrace_162207
  have hstable : (prefixWord ++ tailWord_162207).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162207).length < 2 ^ (prefixWord ++ tailWord_162207).sum := by decide
  have hdescent : baseEnd_162207 < baseStart_162207 := by decide
  rcases family_descends (prefixWord ++ tailWord_162207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162232 : List Nat := [2, 1, 2, 1, 2, 2, 1, 3, 7]
def baseStart_162232 : Nat := 118140960795 + 162232 * 2 ^ 59
def prefixEnd_162232 : Nat := 4983230072969 + 3 ^ 40 * 162232 * 2
def baseEnd_162232 : Nat := 37023552684584222335073

theorem tailTrace_162232 : CollatzResearch.WordTrace tailWord_162232 prefixEnd_162232 37023552684584222335073 := by
  unfold tailWord_162232
  simp only [CollatzResearch.WordTrace]
  refine ⟨2958543574134322932420475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3944724765512430576560633 2958543574134322932420475)
  ·
    refine ⟨4437815361201484398630713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2958543574134322932420475 4437815361201484398630713)
    ·
      refine ⟨3328361520901113298973035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4437815361201484398630713 3328361520901113298973035)
      ·
        refine ⟨4992542281351669948459553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3328361520901113298973035 4992542281351669948459553)
        ·
          refine ⟨3744406711013752461344665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4992542281351669948459553 3744406711013752461344665)
          ·
            refine ⟨2808305033260314346008499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3744406711013752461344665 2808305033260314346008499)
            ·
              refine ⟨4212457549890471519012749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2808305033260314346008499 4212457549890471519012749)
              ·
                refine ⟨1579671581208926819629781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4212457549890471519012749 1579671581208926819629781)
                ·
                  refine ⟨37023552684584222335073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1579671581208926819629781 37023552684584222335073)
                  ·
                    rfl

theorem cell21_162232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 7].length) (baseStart_162232 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_162232 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_162232 prefixEnd_162232 := by exact prefixLift 162232
  have htrace : WordTrace (prefixWord ++ tailWord_162232) baseStart_162232 baseEnd_162232 := by
    simpa [prefixWord, tailWord_162232, baseEnd_162232] using wordTrace_append hprefix tailTrace_162232
  have hstable : (prefixWord ++ tailWord_162232).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162232).length < 2 ^ (prefixWord ++ tailWord_162232).sum := by decide
  have hdescent : baseEnd_162232 < baseStart_162232 := by decide
  rcases family_descends (prefixWord ++ tailWord_162232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162258 : List Nat := [3, 2, 2, 4, 2, 1, 2, 2, 3]
def baseStart_162258 : Nat := 118140960795 + 162258 * 2 ^ 59
def prefixEnd_162258 : Nat := 4983230072969 + 3 ^ 40 * 162258 * 2
def baseEnd_162258 : Nat := 37029486238813954901687

theorem tailTrace_162258 : CollatzResearch.WordTrace tailWord_162258 prefixEnd_162258 37029486238813954901687 := by
  unfold tailWord_162258
  simp only [CollatzResearch.WordTrace]
  refine ⟨1479508861543613076321857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3945356964116301536858285 1479508861543613076321857)
  ·
    refine ⟨1109631646157709807241393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1479508861543613076321857 1109631646157709807241393)
    ·
      refine ⟨832223734618282355431045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1109631646157709807241393 832223734618282355431045)
      ·
        refine ⟨156041950240927941643321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 832223734618282355431045 156041950240927941643321)
        ·
          refine ⟨117031462680695956232491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156041950240927941643321 117031462680695956232491)
          ·
            refine ⟨175547194021043934348737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117031462680695956232491 175547194021043934348737)
            ·
              refine ⟨131660395515782950761553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 175547194021043934348737 131660395515782950761553)
              ·
                refine ⟨98745296636837213071165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 131660395515782950761553 98745296636837213071165)
                ·
                  refine ⟨37029486238813954901687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 98745296636837213071165 37029486238813954901687)
                  ·
                    rfl

theorem cell21_162258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 2, 2, 3].length) (baseStart_162258 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_162258 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_162258 prefixEnd_162258 := by exact prefixLift 162258
  have htrace : WordTrace (prefixWord ++ tailWord_162258) baseStart_162258 baseEnd_162258 := by
    simpa [prefixWord, tailWord_162258, baseEnd_162258] using wordTrace_append hprefix tailTrace_162258
  have hstable : (prefixWord ++ tailWord_162258).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162258).length < 2 ^ (prefixWord ++ tailWord_162258).sum := by decide
  have hdescent : baseEnd_162258 < baseStart_162258 := by decide
  rcases family_descends (prefixWord ++ tailWord_162258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162266 : List Nat := [3, 1, 1, 2, 3, 1, 3, 4, 3]
def baseStart_162266 : Nat := 118140960795 + 162266 * 2 ^ 59
def prefixEnd_162266 : Nat := 4983230072969 + 3 ^ 40 * 162266 * 2
def baseEnd_162266 : Nat := 37031311947807718768337

theorem tailTrace_162266 : CollatzResearch.WordTrace tailWord_162266 prefixEnd_162266 37031311947807718768337 := by
  unfold tailWord_162266
  simp only [CollatzResearch.WordTrace]
  refine ⟨1479581807536367417894663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3945551486763646447719101 1479581807536367417894663)
  ·
    refine ⟨2219372711304551126841995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1479581807536367417894663 2219372711304551126841995)
    ·
      refine ⟨3329059066956826690262993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2219372711304551126841995 3329059066956826690262993)
      ·
        refine ⟨2496794300217620017697245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3329059066956826690262993 2496794300217620017697245)
        ·
          refine ⟨936297862581607506636467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2496794300217620017697245 936297862581607506636467)
          ·
            refine ⟨1404446793872411259954701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 936297862581607506636467 1404446793872411259954701)
            ·
              refine ⟨526667547702154222483013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1404446793872411259954701 526667547702154222483013)
              ·
                refine ⟨98750165194153916715565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 526667547702154222483013 98750165194153916715565)
                ·
                  refine ⟨37031311947807718768337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 98750165194153916715565 37031311947807718768337)
                  ·
                    rfl

theorem cell21_162266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 4, 3].length) (baseStart_162266 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_162266 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_162266 prefixEnd_162266 := by exact prefixLift 162266
  have htrace : WordTrace (prefixWord ++ tailWord_162266) baseStart_162266 baseEnd_162266 := by
    simpa [prefixWord, tailWord_162266, baseEnd_162266] using wordTrace_append hprefix tailTrace_162266
  have hstable : (prefixWord ++ tailWord_162266).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162266).length < 2 ^ (prefixWord ++ tailWord_162266).sum := by decide
  have hdescent : baseEnd_162266 < baseStart_162266 := by decide
  rcases family_descends (prefixWord ++ tailWord_162266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162280 : List Nat := [2, 1, 4, 1, 1, 3, 2, 3, 4]
def baseStart_162280 : Nat := 118140960795 + 162280 * 2 ^ 59
def prefixEnd_162280 : Nat := 4983230072969 + 3 ^ 40 * 162280 * 2
def baseEnd_162280 : Nat := 37034506938546805534975

theorem tailTrace_162280 : CollatzResearch.WordTrace tailWord_162280 prefixEnd_162280 37034506938546805534975 := by
  unfold tailWord_162280
  simp only [CollatzResearch.WordTrace]
  refine ⟨2959418926047375031294147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3945891901396500041725529 2959418926047375031294147)
  ·
    refine ⟨4439128389071062546941221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2959418926047375031294147 4439128389071062546941221)
    ·
      refine ⟨832336572950824227551479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4439128389071062546941221 832336572950824227551479)
      ·
        refine ⟨1248504859426236341327219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 832336572950824227551479 1248504859426236341327219)
        ·
          refine ⟨1872757289139354511990829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1248504859426236341327219 1872757289139354511990829)
          ·
            refine ⟨702283983427257941996561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1872757289139354511990829 702283983427257941996561)
            ·
              refine ⟨526712987570443456497421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 702283983427257941996561 526712987570443456497421)
              ·
                refine ⟨197517370338916296186533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 526712987570443456497421 197517370338916296186533)
                ·
                  refine ⟨37034506938546805534975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 197517370338916296186533 37034506938546805534975)
                  ·
                    rfl

theorem cell21_162280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 3, 4].length) (baseStart_162280 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_162280 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_162280 prefixEnd_162280 := by exact prefixLift 162280
  have htrace : WordTrace (prefixWord ++ tailWord_162280) baseStart_162280 baseEnd_162280 := by
    simpa [prefixWord, tailWord_162280, baseEnd_162280] using wordTrace_append hprefix tailTrace_162280
  have hstable : (prefixWord ++ tailWord_162280).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162280).length < 2 ^ (prefixWord ++ tailWord_162280).sum := by decide
  have hdescent : baseEnd_162280 < baseStart_162280 := by decide
  rcases family_descends (prefixWord ++ tailWord_162280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162325 : List Nat := [1, 3, 2, 1, 3, 1, 4, 1, 5]
def baseStart_162325 : Nat := 118140960795 + 162325 * 2 ^ 59
def prefixEnd_162325 : Nat := 4983230072969 + 3 ^ 40 * 162325 * 2
def baseEnd_162325 : Nat := 37044776551636727284883

theorem tailTrace_162325 : CollatzResearch.WordTrace tailWord_162325 prefixEnd_162325 37044776551636727284883 := by
  unfold tailWord_162325
  simp only [CollatzResearch.WordTrace]
  refine ⟨5920479136931722747976429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3946986091287815165317619 5920479136931722747976429)
  ·
    refine ⟨2220179676349396030491161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5920479136931722747976429 2220179676349396030491161)
    ·
      refine ⟨1665134757262047022868371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2220179676349396030491161 1665134757262047022868371)
      ·
        refine ⟨2497702135893070534302557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1665134757262047022868371 2497702135893070534302557)
        ·
          refine ⟨936638300959901450363459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2497702135893070534302557 936638300959901450363459)
          ·
            refine ⟨1404957451439852175545189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 936638300959901450363459 1404957451439852175545189)
            ·
              refine ⟨263429522144972282914723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1404957451439852175545189 263429522144972282914723)
              ·
                refine ⟨395144283217458424372085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 263429522144972282914723 395144283217458424372085)
                ·
                  refine ⟨37044776551636727284883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 395144283217458424372085 37044776551636727284883)
                  ·
                    rfl

theorem cell21_162325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 1, 5].length) (baseStart_162325 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_162325 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_162325 prefixEnd_162325 := by exact prefixLift 162325
  have htrace : WordTrace (prefixWord ++ tailWord_162325) baseStart_162325 baseEnd_162325 := by
    simpa [prefixWord, tailWord_162325, baseEnd_162325] using wordTrace_append hprefix tailTrace_162325
  have hstable : (prefixWord ++ tailWord_162325).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162325).length < 2 ^ (prefixWord ++ tailWord_162325).sum := by decide
  have hdescent : baseEnd_162325 < baseStart_162325 := by decide
  rcases family_descends (prefixWord ++ tailWord_162325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162384 : List Nat := [2, 1, 1, 1, 1, 3, 2, 5, 5]
def baseStart_162384 : Nat := 118140960795 + 162384 * 2 ^ 59
def prefixEnd_162384 : Nat := 4983230072969 + 3 ^ 40 * 162384 * 2
def baseEnd_162384 : Nat := 37058241155465735801429

theorem tailTrace_162384 : CollatzResearch.WordTrace tailWord_162384 prefixEnd_162384 37058241155465735801429 := by
  unfold tailWord_162384
  simp only [CollatzResearch.WordTrace]
  refine ⟨2961315521858987912187103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3948420695811983882916137 2961315521858987912187103)
  ·
    refine ⟨4441973282788481868280655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2961315521858987912187103 4441973282788481868280655)
    ·
      refine ⟨6662959924182722802420983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4441973282788481868280655 6662959924182722802420983)
      ·
        refine ⟨9994439886274084203631475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6662959924182722802420983 9994439886274084203631475)
        ·
          refine ⟨14991659829411126305447213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9994439886274084203631475 14991659829411126305447213)
          ·
            refine ⟨5621872436029172364542705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14991659829411126305447213 5621872436029172364542705)
            ·
              refine ⟨4216404327021879273407029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5621872436029172364542705 4216404327021879273407029)
              ·
                refine ⟨395287905658301181881909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4216404327021879273407029 395287905658301181881909)
                ·
                  refine ⟨37058241155465735801429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 395287905658301181881909 37058241155465735801429)
                  ·
                    rfl

theorem cell21_162384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 5, 5].length) (baseStart_162384 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_162384 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_162384 prefixEnd_162384 := by exact prefixLift 162384
  have htrace : WordTrace (prefixWord ++ tailWord_162384) baseStart_162384 baseEnd_162384 := by
    simpa [prefixWord, tailWord_162384, baseEnd_162384] using wordTrace_append hprefix tailTrace_162384
  have hstable : (prefixWord ++ tailWord_162384).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162384).length < 2 ^ (prefixWord ++ tailWord_162384).sum := by decide
  have hdescent : baseEnd_162384 < baseStart_162384 := by decide
  rcases family_descends (prefixWord ++ tailWord_162384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162429 : List Nat := [1, 4, 1, 1, 14]
def baseStart_162429 : Nat := 118140960795 + 162429 * 2 ^ 59
def prefixEnd_162429 : Nat := 4983230072969 + 3 ^ 40 * 162429 * 2
def baseEnd_162429 : Nat := 457635935414267377177

theorem tailTrace_162429 : CollatzResearch.WordTrace tailWord_162429 prefixEnd_162429 457635935414267377177 := by
  unfold tailWord_162429
  simp only [CollatzResearch.WordTrace]
  refine ⟨5924272328554948509762341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3949514885703299006508227 5924272328554948509762341)
  ·
    refine ⟨1110801061604052845580439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5924272328554948509762341 1110801061604052845580439)
    ·
      refine ⟨1666201592406079268370659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1110801061604052845580439 1666201592406079268370659)
      ·
        refine ⟨2499302388609118902555989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1666201592406079268370659 2499302388609118902555989)
        ·
          refine ⟨457635935414267377177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 2499302388609118902555989 457635935414267377177)
          ·
            rfl

theorem cell21_162429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 14].length) (baseStart_162429 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_162429 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_162429 prefixEnd_162429 := by exact prefixLift 162429
  have htrace : WordTrace (prefixWord ++ tailWord_162429) baseStart_162429 baseEnd_162429 := by
    simpa [prefixWord, tailWord_162429, baseEnd_162429] using wordTrace_append hprefix tailTrace_162429
  have hstable : (prefixWord ++ tailWord_162429).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162429).length < 2 ^ (prefixWord ++ tailWord_162429).sum := by decide
  have hdescent : baseEnd_162429 < baseStart_162429 := by decide
  rcases family_descends (prefixWord ++ tailWord_162429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162432 : List Nat := [2, 1, 1, 2, 1, 6, 2, 2, 4]
def baseStart_162432 : Nat := 118140960795 + 162432 * 2 ^ 59
def prefixEnd_162432 : Nat := 4983230072969 + 3 ^ 40 * 162432 * 2
def baseEnd_162432 : Nat := 37069195409428319001331

theorem tailTrace_162432 : CollatzResearch.WordTrace tailWord_162432 prefixEnd_162432 37069195409428319001331 := by
  unfold tailWord_162432
  simp only [CollatzResearch.WordTrace]
  refine ⟨2962190873772040011060775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3949587831696053348081033 2962190873772040011060775)
  ·
    refine ⟨4443286310658060016591163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2962190873772040011060775 4443286310658060016591163)
    ·
      refine ⟨6664929465987090024886745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4443286310658060016591163 6664929465987090024886745)
      ·
        refine ⟨4998697099490317518665059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6664929465987090024886745 4998697099490317518665059)
        ·
          refine ⟨7498045649235476277997589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4998697099490317518665059 7498045649235476277997589)
          ·
            refine ⟨351470889807912950531137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 7498045649235476277997589 351470889807912950531137)
            ·
              refine ⟨263603167355934712898353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 351470889807912950531137 263603167355934712898353)
              ·
                refine ⟨197702375516951034673765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 263603167355934712898353 197702375516951034673765)
                ·
                  refine ⟨37069195409428319001331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 197702375516951034673765 37069195409428319001331)
                  ·
                    rfl

theorem cell21_162432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 2, 4].length) (baseStart_162432 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_162432 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_162432 prefixEnd_162432 := by exact prefixLift 162432
  have htrace : WordTrace (prefixWord ++ tailWord_162432) baseStart_162432 baseEnd_162432 := by
    simpa [prefixWord, tailWord_162432, baseEnd_162432] using wordTrace_append hprefix tailTrace_162432
  have hstable : (prefixWord ++ tailWord_162432).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162432).length < 2 ^ (prefixWord ++ tailWord_162432).sum := by decide
  have hdescent : baseEnd_162432 < baseStart_162432 := by decide
  rcases family_descends (prefixWord ++ tailWord_162432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162494 : List Nat := [4, 2, 1, 1, 2, 1, 1, 6, 3]
def baseStart_162494 : Nat := 118140960795 + 162494 * 2 ^ 59
def prefixEnd_162494 : Nat := 4983230072969 + 3 ^ 40 * 162494 * 2
def baseEnd_162494 : Nat := 37083344654129988967871

theorem tailTrace_162494 : CollatzResearch.WordTrace tailWord_162494 prefixEnd_162494 37083344654129988967871 := by
  unfold tailWord_162494
  simp only [CollatzResearch.WordTrace]
  refine ⟨740830384164933076359817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3951095382212976407252357 740830384164933076359817)
  ·
    refine ⟨555622788123699807269863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 740830384164933076359817 555622788123699807269863)
    ·
      refine ⟨833434182185549710904795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 555622788123699807269863 833434182185549710904795)
      ·
        refine ⟨1250151273278324566357193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 833434182185549710904795 1250151273278324566357193)
        ·
          refine ⟨937613454958743424767895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1250151273278324566357193 937613454958743424767895)
          ·
            refine ⟨1406420182438115137151843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 937613454958743424767895 1406420182438115137151843)
            ·
              refine ⟨2109630273657172705727765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1406420182438115137151843 2109630273657172705727765)
              ·
                refine ⟨98888919077679970580989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2109630273657172705727765 98888919077679970580989)
                ·
                  refine ⟨37083344654129988967871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 98888919077679970580989 37083344654129988967871)
                  ·
                    rfl

theorem cell21_162494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 6, 3].length) (baseStart_162494 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_162494 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_162494 prefixEnd_162494 := by exact prefixLift 162494
  have htrace : WordTrace (prefixWord ++ tailWord_162494) baseStart_162494 baseEnd_162494 := by
    simpa [prefixWord, tailWord_162494, baseEnd_162494] using wordTrace_append hprefix tailTrace_162494
  have hstable : (prefixWord ++ tailWord_162494).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162494).length < 2 ^ (prefixWord ++ tailWord_162494).sum := by decide
  have hdescent : baseEnd_162494 < baseStart_162494 := by decide
  rcases family_descends (prefixWord ++ tailWord_162494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162553 : List Nat := [1, 2, 1, 3, 1, 1, 1, 8, 3]
def baseStart_162553 : Nat := 118140960795 + 162553 * 2 ^ 59
def prefixEnd_162553 : Nat := 4983230072969 + 3 ^ 40 * 162553 * 2
def baseEnd_162553 : Nat := 37096809257958997484417

theorem tailTrace_162553 : CollatzResearch.WordTrace tailWord_162553 prefixEnd_162553 37096809257958997484417 := by
  unfold tailWord_162553
  simp only [CollatzResearch.WordTrace]
  refine ⟨5928794980105717687276313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3952529986737145124850875 5928794980105717687276313)
  ·
    refine ⟨4446596235079288265457235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5928794980105717687276313 4446596235079288265457235)
    ·
      refine ⟨6669894352618932398185853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4446596235079288265457235 6669894352618932398185853)
      ·
        refine ⟨2501210382232099649319695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6669894352618932398185853 2501210382232099649319695)
        ·
          refine ⟨3751815573348149473979543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2501210382232099649319695 3751815573348149473979543)
          ·
            refine ⟨5627723360022224210969315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3751815573348149473979543 5627723360022224210969315)
            ·
              refine ⟨8441585040033336316453973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5627723360022224210969315 8441585040033336316453973)
              ·
                refine ⟨98924824687890659958445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8441585040033336316453973 98924824687890659958445)
                ·
                  refine ⟨37096809257958997484417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 98924824687890659958445 37096809257958997484417)
                  ·
                    rfl

theorem cell21_162553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 8, 3].length) (baseStart_162553 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_162553 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_162553 prefixEnd_162553 := by exact prefixLift 162553
  have htrace : WordTrace (prefixWord ++ tailWord_162553) baseStart_162553 baseEnd_162553 := by
    simpa [prefixWord, tailWord_162553, baseEnd_162553] using wordTrace_append hprefix tailTrace_162553
  have hstable : (prefixWord ++ tailWord_162553).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162553).length < 2 ^ (prefixWord ++ tailWord_162553).sum := by decide
  have hdescent : baseEnd_162553 < baseStart_162553 := by decide
  rcases family_descends (prefixWord ++ tailWord_162553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162581 : List Nat := [1, 3, 2, 1, 2, 2, 1, 9]
def baseStart_162581 : Nat := 118140960795 + 162581 * 2 ^ 59
def prefixEnd_162581 : Nat := 4983230072969 + 3 ^ 40 * 162581 * 2
def baseEnd_162581 : Nat := 12367733079812390339231

theorem tailTrace_162581 : CollatzResearch.WordTrace tailWord_162581 prefixEnd_162581 12367733079812390339231 := by
  unfold tailWord_162581
  simp only [CollatzResearch.WordTrace]
  refine ⟨5929816224004278469295597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3953210816002852312863731 5929816224004278469295597)
  ·
    refine ⟨2223681084001604425985849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5929816224004278469295597 2223681084001604425985849)
    ·
      refine ⟨1667760813001203319489387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2223681084001604425985849 1667760813001203319489387)
      ·
        refine ⟨2501641219501804979234081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1667760813001203319489387 2501641219501804979234081)
        ·
          refine ⟨1876230914626353734425561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2501641219501804979234081 1876230914626353734425561)
          ·
            refine ⟨1407173185969765300819171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1876230914626353734425561 1407173185969765300819171)
            ·
              refine ⟨2110759778954647951228757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1407173185969765300819171 2110759778954647951228757)
              ·
                refine ⟨12367733079812390339231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2110759778954647951228757 12367733079812390339231)
                ·
                  rfl

theorem cell21_162581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 9].length) (baseStart_162581 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_162581 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_162581 prefixEnd_162581 := by exact prefixLift 162581
  have htrace : WordTrace (prefixWord ++ tailWord_162581) baseStart_162581 baseEnd_162581 := by
    simpa [prefixWord, tailWord_162581, baseEnd_162581] using wordTrace_append hprefix tailTrace_162581
  have hstable : (prefixWord ++ tailWord_162581).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162581).length < 2 ^ (prefixWord ++ tailWord_162581).sum := by decide
  have hdescent : baseEnd_162581 < baseStart_162581 := by decide
  rcases family_descends (prefixWord ++ tailWord_162581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162660 : List Nat := [2, 3, 1, 1, 4, 1, 3, 2, 4]
def baseStart_162660 : Nat := 118140960795 + 162660 * 2 ^ 59
def prefixEnd_162660 : Nat := 4983230072969 + 3 ^ 40 * 162660 * 2
def baseEnd_162660 : Nat := 37121228115750589200865

theorem tailTrace_162660 : CollatzResearch.WordTrace tailWord_162660 prefixEnd_162660 37121228115750589200865 := by
  unfold tailWord_162660
  simp only [CollatzResearch.WordTrace]
  refine ⟨2966348795359037480710717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3955131727145383307614289 2966348795359037480710717)
  ·
    refine ⟨1112380798259639055266519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2966348795359037480710717 1112380798259639055266519)
    ·
      refine ⟨1668571197389458582899779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1112380798259639055266519 1668571197389458582899779)
      ·
        refine ⟨2502856796084187874349669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1668571197389458582899779 2502856796084187874349669)
        ·
          refine ⟨469285649265785226440563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2502856796084187874349669 469285649265785226440563)
          ·
            refine ⟨703928473898677839660845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 469285649265785226440563 703928473898677839660845)
            ·
              refine ⟨263973177712004189872817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 703928473898677839660845 263973177712004189872817)
              ·
                refine ⟨197979883284003142404613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 263973177712004189872817 197979883284003142404613)
                ·
                  refine ⟨37121228115750589200865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 197979883284003142404613 37121228115750589200865)
                  ·
                    rfl

theorem cell21_162660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 2, 4].length) (baseStart_162660 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_162660 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_162660 prefixEnd_162660 := by exact prefixLift 162660
  have htrace : WordTrace (prefixWord ++ tailWord_162660) baseStart_162660 baseEnd_162660 := by
    simpa [prefixWord, tailWord_162660, baseEnd_162660] using wordTrace_append hprefix tailTrace_162660
  have hstable : (prefixWord ++ tailWord_162660).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162660).length < 2 ^ (prefixWord ++ tailWord_162660).sum := by decide
  have hdescent : baseEnd_162660 < baseStart_162660 := by decide
  rcases family_descends (prefixWord ++ tailWord_162660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162677 : List Nat := [1, 3, 4, 1, 1, 3, 3, 1, 4]
def baseStart_162677 : Nat := 118140960795 + 162677 * 2 ^ 59
def prefixEnd_162677 : Nat := 4983230072969 + 3 ^ 40 * 162677 * 2
def baseEnd_162677 : Nat := 37125107747362337417497

theorem tailTrace_162677 : CollatzResearch.WordTrace tailWord_162677 prefixEnd_162677 37125107747362337417497 := by
  unfold tailWord_162677
  simp only [CollatzResearch.WordTrace]
  refine ⟨5933317631656486864790285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3955545087770991243193523 5933317631656486864790285)
  ·
    refine ⟨2224994111871182574296357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5933317631656486864790285 2224994111871182574296357)
    ·
      refine ⟨417186395975846732680567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2224994111871182574296357 417186395975846732680567)
      ·
        refine ⟨625779593963770099020851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 417186395975846732680567 625779593963770099020851)
        ·
          refine ⟨938669390945655148531277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 625779593963770099020851 938669390945655148531277)
          ·
            refine ⟨352001021604620680699229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 938669390945655148531277 352001021604620680699229)
            ·
              refine ⟨132000383101732755262211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 352001021604620680699229 132000383101732755262211)
              ·
                refine ⟨198000574652599132893317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132000383101732755262211 198000574652599132893317)
                ·
                  refine ⟨37125107747362337417497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 198000574652599132893317 37125107747362337417497)
                  ·
                    rfl

theorem cell21_162677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 3, 1, 4].length) (baseStart_162677 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_162677 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_162677 prefixEnd_162677 := by exact prefixLift 162677
  have htrace : WordTrace (prefixWord ++ tailWord_162677) baseStart_162677 baseEnd_162677 := by
    simpa [prefixWord, tailWord_162677, baseEnd_162677] using wordTrace_append hprefix tailTrace_162677
  have hstable : (prefixWord ++ tailWord_162677).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162677).length < 2 ^ (prefixWord ++ tailWord_162677).sum := by decide
  have hdescent : baseEnd_162677 < baseStart_162677 := by decide
  rcases family_descends (prefixWord ++ tailWord_162677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162719 : List Nat := [1, 1, 2, 5, 2, 1, 2, 1, 6]
def baseStart_162719 : Nat := 118140960795 + 162719 * 2 ^ 59
def prefixEnd_162719 : Nat := 4983230072969 + 3 ^ 40 * 162719 * 2
def baseEnd_162719 : Nat := 37134692719579597717411

theorem tailTrace_162719 : CollatzResearch.WordTrace tailWord_162719 prefixEnd_162719 37134692719579597717411 := by
  unfold tailWord_162719
  simp only [CollatzResearch.WordTrace]
  refine ⟨5934849497504328037819211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3956566331669552025212807 5934849497504328037819211)
  ·
    refine ⟨8902274246256492056728817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5934849497504328037819211 8902274246256492056728817)
    ·
      refine ⟨6676705684692369042546613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8902274246256492056728817 6676705684692369042546613)
      ·
        refine ⟨625941157939909597738745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6676705684692369042546613 625941157939909597738745)
        ·
          refine ⟨469455868454932198304059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 625941157939909597738745 469455868454932198304059)
          ·
            refine ⟨704183802682398297456089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 469455868454932198304059 704183802682398297456089)
            ·
              refine ⟨528137852011798723092067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 704183802682398297456089 528137852011798723092067)
              ·
                refine ⟨792206778017698084638101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 528137852011798723092067 792206778017698084638101)
                ·
                  refine ⟨37134692719579597717411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 792206778017698084638101 37134692719579597717411)
                  ·
                    rfl

theorem cell21_162719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 1, 6].length) (baseStart_162719 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_162719 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_162719 prefixEnd_162719 := by exact prefixLift 162719
  have htrace : WordTrace (prefixWord ++ tailWord_162719) baseStart_162719 baseEnd_162719 := by
    simpa [prefixWord, tailWord_162719, baseEnd_162719] using wordTrace_append hprefix tailTrace_162719
  have hstable : (prefixWord ++ tailWord_162719).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162719).length < 2 ^ (prefixWord ++ tailWord_162719).sum := by decide
  have hdescent : baseEnd_162719 < baseStart_162719 := by decide
  rcases family_descends (prefixWord ++ tailWord_162719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162722 : List Nat := [3, 3, 1, 2, 2, 3, 1, 1, 5]
def baseStart_162722 : Nat := 118140960795 + 162722 * 2 ^ 59
def prefixEnd_162722 : Nat := 4983230072969 + 3 ^ 40 * 162722 * 2
def baseEnd_162722 : Nat := 37135377360452259167405

theorem tailTrace_162722 : CollatzResearch.WordTrace tailWord_162722 prefixEnd_162722 37135377360452259167405 := by
  unfold tailWord_162722
  simp only [CollatzResearch.WordTrace]
  refine ⟨1483739729123364887544605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3956639277662306366785613 1483739729123364887544605)
  ·
    refine ⟨556402398421261832829227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1483739729123364887544605 556402398421261832829227)
    ·
      refine ⟨834603597631892749243841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 556402398421261832829227 834603597631892749243841)
      ·
        refine ⟨625952698223919561932881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 834603597631892749243841 625952698223919561932881)
        ·
          refine ⟨469464523667939671449661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 625952698223919561932881 469464523667939671449661)
          ·
            refine ⟨176049196375477376793623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 469464523667939671449661 176049196375477376793623)
            ·
              refine ⟨264073794563216065190435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 176049196375477376793623 264073794563216065190435)
              ·
                refine ⟨396110691844824097785653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 264073794563216065190435 396110691844824097785653)
                ·
                  refine ⟨37135377360452259167405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 396110691844824097785653 37135377360452259167405)
                  ·
                    rfl

theorem cell21_162722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_162722 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_162722 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_162722 prefixEnd_162722 := by exact prefixLift 162722
  have htrace : WordTrace (prefixWord ++ tailWord_162722) baseStart_162722 baseEnd_162722 := by
    simpa [prefixWord, tailWord_162722, baseEnd_162722] using wordTrace_append hprefix tailTrace_162722
  have hstable : (prefixWord ++ tailWord_162722).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162722).length < 2 ^ (prefixWord ++ tailWord_162722).sum := by decide
  have hdescent : baseEnd_162722 < baseStart_162722 := by decide
  rcases family_descends (prefixWord ++ tailWord_162722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162840 : List Nat := [2, 1, 2, 3, 2, 2, 1, 3, 5]
def baseStart_162840 : Nat := 118140960795 + 162840 * 2 ^ 59
def prefixEnd_162840 : Nat := 4983230072969 + 3 ^ 40 * 162840 * 2
def baseEnd_162840 : Nat := 37162306568110276200497

theorem tailTrace_162840 : CollatzResearch.WordTrace tailWord_162840 prefixEnd_162840 37162306568110276200497 := by
  unfold tailWord_162840
  simp only [CollatzResearch.WordTrace]
  refine ⟨2969631365032982851486987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3959508486710643801982649 2969631365032982851486987)
  ·
    refine ⟨4454447047549474277230481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2969631365032982851486987 4454447047549474277230481)
    ·
      refine ⟨3340835285662105707922861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4454447047549474277230481 3340835285662105707922861)
      ·
        refine ⟨1252813232123289640471073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3340835285662105707922861 1252813232123289640471073)
        ·
          refine ⟨939609924092467230353305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1252813232123289640471073 939609924092467230353305)
          ·
            refine ⟨704707443069350422764979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 939609924092467230353305 704707443069350422764979)
            ·
              refine ⟨1057061164604025634147469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 704707443069350422764979 1057061164604025634147469)
              ·
                refine ⟨396397936726509612805301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1057061164604025634147469 396397936726509612805301)
                ·
                  refine ⟨37162306568110276200497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 396397936726509612805301 37162306568110276200497)
                  ·
                    rfl

theorem cell21_162840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 3, 5].length) (baseStart_162840 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_162840 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_162840 prefixEnd_162840 := by exact prefixLift 162840
  have htrace : WordTrace (prefixWord ++ tailWord_162840) baseStart_162840 baseEnd_162840 := by
    simpa [prefixWord, tailWord_162840, baseEnd_162840] using wordTrace_append hprefix tailTrace_162840
  have hstable : (prefixWord ++ tailWord_162840).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162840).length < 2 ^ (prefixWord ++ tailWord_162840).sum := by decide
  have hdescent : baseEnd_162840 < baseStart_162840 := by decide
  rcases family_descends (prefixWord ++ tailWord_162840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162942 : List Nat := [4, 2, 4, 1, 1, 2, 2, 2, 3]
def baseStart_162942 : Nat := 118140960795 + 162942 * 2 ^ 59
def prefixEnd_162942 : Nat := 4983230072969 + 3 ^ 40 * 162942 * 2
def baseEnd_162942 : Nat := 37185584357780765500289

theorem tailTrace_162942 : CollatzResearch.WordTrace tailWord_162942 prefixEnd_162942 37185584357780765500289 := by
  unfold tailWord_162942
  simp only [CollatzResearch.WordTrace]
  refine ⟨742872871962054640398385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3961988650464291415458053 742872871962054640398385)
  ·
    refine ⟨557154653971540980298789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 742872871962054640398385 557154653971540980298789)
    ·
      refine ⟨104466497619663933806023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 557154653971540980298789 104466497619663933806023)
      ·
        refine ⟨156699746429495900709035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104466497619663933806023 156699746429495900709035)
        ·
          refine ⟨235049619644243851063553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156699746429495900709035 235049619644243851063553)
          ·
            refine ⟨176287214733182888297665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 235049619644243851063553 176287214733182888297665)
            ·
              refine ⟨132215411049887166223249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 176287214733182888297665 132215411049887166223249)
              ·
                refine ⟨99161558287415374667437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 132215411049887166223249 99161558287415374667437)
                ·
                  refine ⟨37185584357780765500289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 99161558287415374667437 37185584357780765500289)
                  ·
                    rfl

theorem cell21_162942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 2, 2, 3].length) (baseStart_162942 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_162942 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_162942 prefixEnd_162942 := by exact prefixLift 162942
  have htrace : WordTrace (prefixWord ++ tailWord_162942) baseStart_162942 baseEnd_162942 := by
    simpa [prefixWord, tailWord_162942, baseEnd_162942] using wordTrace_append hprefix tailTrace_162942
  have hstable : (prefixWord ++ tailWord_162942).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162942).length < 2 ^ (prefixWord ++ tailWord_162942).sum := by decide
  have hdescent : baseEnd_162942 < baseStart_162942 := by decide
  rcases family_descends (prefixWord ++ tailWord_162942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162947 : List Nat := [1, 1, 1, 3, 3, 2, 4, 2, 4]
def baseStart_162947 : Nat := 118140960795 + 162947 * 2 ^ 59
def prefixEnd_162947 : Nat := 4983230072969 + 3 ^ 40 * 162947 * 2
def baseEnd_162947 : Nat := 37186725425901867916945

theorem tailTrace_162947 : CollatzResearch.WordTrace tailWord_162947 prefixEnd_162947 37186725425901867916945 := by
  unfold tailWord_162947
  simp only [CollatzResearch.WordTrace]
  refine ⟨5943165340678322977119095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3962110227118881984746063 5943165340678322977119095)
  ·
    refine ⟨8914748011017484465678643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5943165340678322977119095 8914748011017484465678643)
    ·
      refine ⟨13372122016526226698517965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8914748011017484465678643 13372122016526226698517965)
      ·
        refine ⟨5014545756197335011944237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13372122016526226698517965 5014545756197335011944237)
        ·
          refine ⟨1880454658574000629479089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5014545756197335011944237 1880454658574000629479089)
          ·
            refine ⟨1410340993930500472109317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1880454658574000629479089 1410340993930500472109317)
            ·
              refine ⟨264438936361968838520497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1410340993930500472109317 264438936361968838520497)
              ·
                refine ⟨198329202271476628890373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 264438936361968838520497 198329202271476628890373)
                ·
                  refine ⟨37186725425901867916945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 198329202271476628890373 37186725425901867916945)
                  ·
                    rfl

theorem cell21_162947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 2, 4].length) (baseStart_162947 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_162947 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_162947 prefixEnd_162947 := by exact prefixLift 162947
  have htrace : WordTrace (prefixWord ++ tailWord_162947) baseStart_162947 baseEnd_162947 := by
    simpa [prefixWord, tailWord_162947, baseEnd_162947] using wordTrace_append hprefix tailTrace_162947
  have hstable : (prefixWord ++ tailWord_162947).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162947).length < 2 ^ (prefixWord ++ tailWord_162947).sum := by decide
  have hdescent : baseEnd_162947 < baseStart_162947 := by decide
  rcases family_descends (prefixWord ++ tailWord_162947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163009 : List Nat := [1, 2, 6, 1, 1, 1, 1, 3, 5]
def baseStart_163009 : Nat := 118140960795 + 163009 * 2 ^ 59
def prefixEnd_163009 : Nat := 4983230072969 + 3 ^ 40 * 163009 * 2
def baseEnd_163009 : Nat := 37200874670603537883485

theorem tailTrace_163009 : CollatzResearch.WordTrace tailWord_163009 prefixEnd_163009 37200874670603537883485 := by
  unfold tailWord_163009
  simp only [CollatzResearch.WordTrace]
  refine ⟨5945426666453707565876081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3963617777635805043917387 5945426666453707565876081)
  ·
    refine ⟨4459069999840280674407061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5945426666453707565876081 4459069999840280674407061)
    ·
      refine ⟨209018906242513156612831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 4459069999840280674407061 209018906242513156612831)
      ·
        refine ⟨313528359363769734919247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209018906242513156612831 313528359363769734919247)
        ·
          refine ⟨470292539045654602378871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 313528359363769734919247 470292539045654602378871)
          ·
            refine ⟨705438808568481903568307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 470292539045654602378871 705438808568481903568307)
            ·
              refine ⟨1058158212852722855352461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 705438808568481903568307 1058158212852722855352461)
              ·
                refine ⟨396809329819771070757173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1058158212852722855352461 396809329819771070757173)
                ·
                  refine ⟨37200874670603537883485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 396809329819771070757173 37200874670603537883485)
                  ·
                    rfl

theorem cell21_163009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 3, 5].length) (baseStart_163009 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_163009 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_163009 prefixEnd_163009 := by exact prefixLift 163009
  have htrace : WordTrace (prefixWord ++ tailWord_163009) baseStart_163009 baseEnd_163009 := by
    simpa [prefixWord, tailWord_163009, baseEnd_163009] using wordTrace_append hprefix tailTrace_163009
  have hstable : (prefixWord ++ tailWord_163009).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163009).length < 2 ^ (prefixWord ++ tailWord_163009).sum := by decide
  have hdescent : baseEnd_163009 < baseStart_163009 := by decide
  rcases family_descends (prefixWord ++ tailWord_163009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163060 : List Nat := [2, 6, 1, 2, 1, 2, 1, 1, 5]
def baseStart_163060 : Nat := 118140960795 + 163060 * 2 ^ 59
def prefixEnd_163060 : Nat := 4983230072969 + 3 ^ 40 * 163060 * 2
def baseEnd_163060 : Nat := 37212513565438782533381

theorem tailTrace_163060 : CollatzResearch.WordTrace tailWord_163060 prefixEnd_163060 37212513565438782533381 := by
  unfold tailWord_163060
  simp only [CollatzResearch.WordTrace]
  refine ⟨2973643394634471637991317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3964857859512628850655089 2973643394634471637991317)
  ·
    refine ⟨139389534123490858030843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 2973643394634471637991317 139389534123490858030843)
    ·
      refine ⟨209084301185236287046265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139389534123490858030843 209084301185236287046265)
      ·
        refine ⟨156813225888927215284699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209084301185236287046265 156813225888927215284699)
        ·
          refine ⟨235219838833390822927049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156813225888927215284699 235219838833390822927049)
          ·
            refine ⟨176414879125043117195287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 235219838833390822927049 176414879125043117195287)
            ·
              refine ⟨264622318687564675792931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 176414879125043117195287 264622318687564675792931)
              ·
                refine ⟨396933478031347013689397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 264622318687564675792931 396933478031347013689397)
                ·
                  refine ⟨37212513565438782533381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 396933478031347013689397 37212513565438782533381)
                  ·
                    rfl

theorem cell21_163060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_163060 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_163060 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_163060 prefixEnd_163060 := by exact prefixLift 163060
  have htrace : WordTrace (prefixWord ++ tailWord_163060) baseStart_163060 baseEnd_163060 := by
    simpa [prefixWord, tailWord_163060, baseEnd_163060] using wordTrace_append hprefix tailTrace_163060
  have hstable : (prefixWord ++ tailWord_163060).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163060).length < 2 ^ (prefixWord ++ tailWord_163060).sum := by decide
  have hdescent : baseEnd_163060 < baseStart_163060 := by decide
  rcases family_descends (prefixWord ++ tailWord_163060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163074 : List Nat := [3, 4, 1, 1, 3, 2, 2, 1, 4]
def baseStart_163074 : Nat := 118140960795 + 163074 * 2 ^ 59
def prefixEnd_163074 : Nat := 4983230072969 + 3 ^ 40 * 163074 * 2
def baseEnd_163074 : Nat := 37215708556177869300019

theorem tailTrace_163074 : CollatzResearch.WordTrace tailWord_163074 prefixEnd_163074 37215708556177869300019 := by
  unfold tailWord_163074
  simp only [CollatzResearch.WordTrace]
  refine ⟨1486949352804555916748069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3965198274145482444661517 1486949352804555916748069)
  ·
    refine ⟨278803003650854234390263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1486949352804555916748069 278803003650854234390263)
    ·
      refine ⟨418204505476281351585395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278803003650854234390263 418204505476281351585395)
      ·
        refine ⟨627306758214422027378093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 418204505476281351585395 627306758214422027378093)
        ·
          refine ⟨235240034330408260266785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 627306758214422027378093 235240034330408260266785)
          ·
            refine ⟨176430025747806195200089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 235240034330408260266785 176430025747806195200089)
            ·
              refine ⟨132322519310854646400067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 176430025747806195200089 132322519310854646400067)
              ·
                refine ⟨198483778966281969600101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132322519310854646400067 198483778966281969600101)
                ·
                  refine ⟨37215708556177869300019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 198483778966281969600101 37215708556177869300019)
                  ·
                    rfl

theorem cell21_163074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_163074 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_163074 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_163074 prefixEnd_163074 := by exact prefixLift 163074
  have htrace : WordTrace (prefixWord ++ tailWord_163074) baseStart_163074 baseEnd_163074 := by
    simpa [prefixWord, tailWord_163074, baseEnd_163074] using wordTrace_append hprefix tailTrace_163074
  have hstable : (prefixWord ++ tailWord_163074).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163074).length < 2 ^ (prefixWord ++ tailWord_163074).sum := by decide
  have hdescent : baseEnd_163074 < baseStart_163074 := by decide
  rcases family_descends (prefixWord ++ tailWord_163074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163175 : List Nat := [1, 1, 5, 1, 4, 1, 1, 1, 6]
def baseStart_163175 : Nat := 118140960795 + 163175 * 2 ^ 59
def prefixEnd_163175 : Nat := 4983230072969 + 3 ^ 40 * 163175 * 2
def baseEnd_163175 : Nat := 37238758132224138116479

theorem tailTrace_163175 : CollatzResearch.WordTrace tailWord_163175 prefixEnd_163175 37238758132224138116479 := by
  unfold tailWord_163175
  simp only [CollatzResearch.WordTrace]
  refine ⟨5951481183852317916418979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3967654122568211944279319 5951481183852317916418979)
  ·
    refine ⟨8927221775778476874628469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5951481183852317916418979 8927221775778476874628469)
    ·
      refine ⟨836927041479232206996419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8927221775778476874628469 836927041479232206996419)
      ·
        refine ⟨1255390562218848310494629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 836927041479232206996419 1255390562218848310494629)
        ·
          refine ⟨235385730416034058217743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1255390562218848310494629 235385730416034058217743)
          ·
            refine ⟨353078595624051087326615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 235385730416034058217743 353078595624051087326615)
            ·
              refine ⟨529617893436076630989923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 353078595624051087326615 529617893436076630989923)
              ·
                refine ⟨794426840154114946484885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 529617893436076630989923 794426840154114946484885)
                ·
                  refine ⟨37238758132224138116479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 794426840154114946484885 37238758132224138116479)
                  ·
                    rfl

theorem cell21_163175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 1, 6].length) (baseStart_163175 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_163175 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_163175 prefixEnd_163175 := by exact prefixLift 163175
  have htrace : WordTrace (prefixWord ++ tailWord_163175) baseStart_163175 baseEnd_163175 := by
    simpa [prefixWord, tailWord_163175, baseEnd_163175] using wordTrace_append hprefix tailTrace_163175
  have hstable : (prefixWord ++ tailWord_163175).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163175).length < 2 ^ (prefixWord ++ tailWord_163175).sum := by decide
  have hdescent : baseEnd_163175 < baseStart_163175 := by decide
  rcases family_descends (prefixWord ++ tailWord_163175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163324 : List Nat := [2, 2, 2, 1, 2, 1, 2, 9]
def baseStart_163324 : Nat := 118140960795 + 163324 * 2 ^ 59
def prefixEnd_163324 : Nat := 4983230072969 + 3 ^ 40 * 163324 * 2
def baseEnd_163324 : Nat := 12424253987410996710947

theorem tailTrace_163324 : CollatzResearch.WordTrace tailWord_163324 prefixEnd_163324 12424253987410996710947 := by
  unfold tailWord_163324
  simp only [CollatzResearch.WordTrace]
  refine ⟨2978457830156258181796513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3971277106875010909062017 2978457830156258181796513)
  ·
    refine ⟨2233843372617193636347385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2978457830156258181796513 2233843372617193636347385)
    ·
      refine ⟨1675382529462895227260539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2233843372617193636347385 1675382529462895227260539)
      ·
        refine ⟨2513073794194342840890809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1675382529462895227260539 2513073794194342840890809)
        ·
          refine ⟨1884805345645757130668107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2513073794194342840890809 1884805345645757130668107)
          ·
            refine ⟨2827208018468635696002161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1884805345645757130668107 2827208018468635696002161)
            ·
              refine ⟨2120406013851476772001621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2827208018468635696002161 2120406013851476772001621)
              ·
                refine ⟨12424253987410996710947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2120406013851476772001621 12424253987410996710947)
                ·
                  rfl

theorem cell21_163324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 9].length) (baseStart_163324 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_163324 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_163324 prefixEnd_163324 := by exact prefixLift 163324
  have htrace : WordTrace (prefixWord ++ tailWord_163324) baseStart_163324 baseEnd_163324 := by
    simpa [prefixWord, tailWord_163324, baseEnd_163324] using wordTrace_append hprefix tailTrace_163324
  have hstable : (prefixWord ++ tailWord_163324).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163324).length < 2 ^ (prefixWord ++ tailWord_163324).sum := by decide
  have hdescent : baseEnd_163324 < baseStart_163324 := by decide
  rcases family_descends (prefixWord ++ tailWord_163324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163330 : List Nat := [3, 4, 1, 2, 1, 1, 1, 5, 3]
def baseStart_163330 : Nat := 118140960795 + 163330 * 2 ^ 59
def prefixEnd_163330 : Nat := 4983230072969 + 3 ^ 40 * 163330 * 2
def baseEnd_163330 : Nat := 37274131243978313032829

theorem tailTrace_163330 : CollatzResearch.WordTrace tailWord_163330 prefixEnd_163330 37274131243978313032829 := by
  unfold tailWord_163330
  simp only [CollatzResearch.WordTrace]
  refine ⟨1489283624572694847077861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3971422998860519592207629 1489283624572694847077861)
  ·
    refine ⟨279240679607380283827099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1489283624572694847077861 279240679607380283827099)
    ·
      refine ⟨418861019411070425740649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279240679607380283827099 418861019411070425740649)
      ·
        refine ⟨314145764558302819305487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 418861019411070425740649 314145764558302819305487)
        ·
          refine ⟨471218646837454228958231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 314145764558302819305487 471218646837454228958231)
          ·
            refine ⟨706827970256181343437347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 471218646837454228958231 706827970256181343437347)
            ·
              refine ⟨1060241955384272015156021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 706827970256181343437347 1060241955384272015156021)
              ·
                refine ⟨99397683317275501420877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1060241955384272015156021 99397683317275501420877)
                ·
                  refine ⟨37274131243978313032829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 99397683317275501420877 37274131243978313032829)
                  ·
                    rfl

theorem cell21_163330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_163330 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_163330 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_163330 prefixEnd_163330 := by exact prefixLift 163330
  have htrace : WordTrace (prefixWord ++ tailWord_163330) baseStart_163330 baseEnd_163330 := by
    simpa [prefixWord, tailWord_163330, baseEnd_163330] using wordTrace_append hprefix tailTrace_163330
  have hstable : (prefixWord ++ tailWord_163330).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163330).length < 2 ^ (prefixWord ++ tailWord_163330).sum := by decide
  have hdescent : baseEnd_163330 < baseStart_163330 := by decide
  rcases family_descends (prefixWord ++ tailWord_163330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163420 : List Nat := [2, 2, 4, 1, 2, 1, 4, 1, 4]
def baseStart_163420 : Nat := 118140960795 + 163420 * 2 ^ 59
def prefixEnd_163420 : Nat := 4983230072969 + 3 ^ 40 * 163420 * 2
def baseEnd_163420 : Nat := 37294670470158156532645

theorem tailTrace_163420 : CollatzResearch.WordTrace tailWord_163420 prefixEnd_163420 37294670470158156532645 := by
  unfold tailWord_163420
  simp only [CollatzResearch.WordTrace]
  refine ⟨2980208533982362379543857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3973611378643149839391809 2980208533982362379543857)
  ·
    refine ⟨2235156400486771784657893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2980208533982362379543857 2235156400486771784657893)
    ·
      refine ⟨419091825091269709623355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2235156400486771784657893 419091825091269709623355)
      ·
        refine ⟨628637737636904564435033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 419091825091269709623355 628637737636904564435033)
        ·
          refine ⟨471478303227678423326275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 628637737636904564435033 471478303227678423326275)
          ·
            refine ⟨707217454841517634989413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 471478303227678423326275 707217454841517634989413)
            ·
              refine ⟨132603272782784556560515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 707217454841517634989413 132603272782784556560515)
              ·
                refine ⟨198904909174176834840773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132603272782784556560515 198904909174176834840773)
                ·
                  refine ⟨37294670470158156532645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 198904909174176834840773 37294670470158156532645)
                  ·
                    rfl

theorem cell21_163420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 4, 1, 4].length) (baseStart_163420 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_163420 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_163420 prefixEnd_163420 := by exact prefixLift 163420
  have htrace : WordTrace (prefixWord ++ tailWord_163420) baseStart_163420 baseEnd_163420 := by
    simpa [prefixWord, tailWord_163420, baseEnd_163420] using wordTrace_append hprefix tailTrace_163420
  have hstable : (prefixWord ++ tailWord_163420).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163420).length < 2 ^ (prefixWord ++ tailWord_163420).sum := by decide
  have hdescent : baseEnd_163420 < baseStart_163420 := by decide
  rcases family_descends (prefixWord ++ tailWord_163420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163431 : List Nat := [1, 1, 5, 1, 1, 1, 2, 4, 5]
def baseStart_163431 : Nat := 118140960795 + 163431 * 2 ^ 59
def prefixEnd_163431 : Nat := 4983230072969 + 3 ^ 40 * 163431 * 2
def baseEnd_163431 : Nat := 37297180820024581849289

theorem tailTrace_163431 : CollatzResearch.WordTrace tailWord_163431 prefixEnd_163431 37297180820024581849289 := by
  unfold tailWord_163431
  simp only [CollatzResearch.WordTrace]
  refine ⟨5960818270924873637738147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3973878847283249091825431 5960818270924873637738147)
  ·
    refine ⟨8941227406387310456607221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5960818270924873637738147 8941227406387310456607221)
    ·
      refine ⟨838240069348810355306927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8941227406387310456607221 838240069348810355306927)
      ·
        refine ⟨1257360104023215532960391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 838240069348810355306927 1257360104023215532960391)
        ·
          refine ⟨1886040156034823299440587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1257360104023215532960391 1886040156034823299440587)
          ·
            refine ⟨2829060234052234949160881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1886040156034823299440587 2829060234052234949160881)
            ·
              refine ⟨2121795175539176211870661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2829060234052234949160881 2121795175539176211870661)
              ·
                refine ⟨397836595413595539725749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2121795175539176211870661 397836595413595539725749)
                ·
                  refine ⟨37297180820024581849289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 397836595413595539725749 37297180820024581849289)
                  ·
                    rfl

theorem cell21_163431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 4, 5].length) (baseStart_163431 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_163431 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_163431 prefixEnd_163431 := by exact prefixLift 163431
  have htrace : WordTrace (prefixWord ++ tailWord_163431) baseStart_163431 baseEnd_163431 := by
    simpa [prefixWord, tailWord_163431, baseEnd_163431] using wordTrace_append hprefix tailTrace_163431
  have hstable : (prefixWord ++ tailWord_163431).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163431).length < 2 ^ (prefixWord ++ tailWord_163431).sum := by decide
  have hdescent : baseEnd_163431 < baseStart_163431 := by decide
  rcases family_descends (prefixWord ++ tailWord_163431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163465 : List Nat := [1, 2, 1, 1, 4, 1, 6, 2, 3]
def baseStart_163465 : Nat := 118140960795 + 163465 * 2 ^ 59
def prefixEnd_163465 : Nat := 4983230072969 + 3 ^ 40 * 163465 * 2
def baseEnd_163465 : Nat := 37304940083248078282553

theorem tailTrace_163465 : CollatzResearch.WordTrace tailWord_163465 prefixEnd_163465 37304940083248078282553 := by
  unfold tailWord_163465
  simp only [CollatzResearch.WordTrace]
  refine ⟨5962058352801697444475849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3974705568534464962983899 5962058352801697444475849)
  ·
    refine ⟨4471543764601273083356887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5962058352801697444475849 4471543764601273083356887)
    ·
      refine ⟨6707315646901909625035331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4471543764601273083356887 6707315646901909625035331)
      ·
        refine ⟨10060973470352864437552997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6707315646901909625035331 10060973470352864437552997)
        ·
          refine ⟨1886432525691162082041187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10060973470352864437552997 1886432525691162082041187)
          ·
            refine ⟨2829648788536743123061781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1886432525691162082041187 2829648788536743123061781)
            ·
              refine ⟨132639786962659833893521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2829648788536743123061781 132639786962659833893521)
              ·
                refine ⟨99479840221994875420141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 132639786962659833893521 99479840221994875420141)
                ·
                  refine ⟨37304940083248078282553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 99479840221994875420141 37304940083248078282553)
                  ·
                    rfl

theorem cell21_163465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 6, 2, 3].length) (baseStart_163465 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_163465 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_163465 prefixEnd_163465 := by exact prefixLift 163465
  have htrace : WordTrace (prefixWord ++ tailWord_163465) baseStart_163465 baseEnd_163465 := by
    simpa [prefixWord, tailWord_163465, baseEnd_163465] using wordTrace_append hprefix tailTrace_163465
  have hstable : (prefixWord ++ tailWord_163465).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163465).length < 2 ^ (prefixWord ++ tailWord_163465).sum := by decide
  have hdescent : baseEnd_163465 < baseStart_163465 := by decide
  rcases family_descends (prefixWord ++ tailWord_163465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163510 : List Nat := [5, 1, 3, 1, 1, 2, 8]
def baseStart_163510 : Nat := 118140960795 + 163510 * 2 ^ 59
def prefixEnd_163510 : Nat := 4983230072969 + 3 ^ 40 * 163510 * 2
def baseEnd_163510 : Nat := 4146134410704222225829

theorem tailTrace_163510 : CollatzResearch.WordTrace tailWord_163510 prefixEnd_163510 4146134410704222225829 := by
  unfold tailWord_163510
  simp only [CollatzResearch.WordTrace]
  refine ⟨372731227352416883116499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3975799758425780086575989 372731227352416883116499)
  ·
    refine ⟨559096841028625324674749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 372731227352416883116499 559096841028625324674749)
    ·
      refine ⟨209661315385734496753031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 559096841028625324674749 209661315385734496753031)
      ·
        refine ⟨314491973078601745129547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209661315385734496753031 314491973078601745129547)
        ·
          refine ⟨471737959617902617694321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 314491973078601745129547 471737959617902617694321)
          ·
            refine ⟨353803469713426963270741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 471737959617902617694321 353803469713426963270741)
            ·
              refine ⟨4146134410704222225829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 353803469713426963270741 4146134410704222225829)
              ·
                rfl

theorem cell21_163510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 8].length) (baseStart_163510 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_163510 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_163510 prefixEnd_163510 := by exact prefixLift 163510
  have htrace : WordTrace (prefixWord ++ tailWord_163510) baseStart_163510 baseEnd_163510 := by
    simpa [prefixWord, tailWord_163510, baseEnd_163510] using wordTrace_append hprefix tailTrace_163510
  have hstable : (prefixWord ++ tailWord_163510).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163510).length < 2 ^ (prefixWord ++ tailWord_163510).sum := by decide
  have hdescent : baseEnd_163510 < baseStart_163510 := by decide
  rcases family_descends (prefixWord ++ tailWord_163510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163524 : List Nat := [2, 3, 3, 1, 1, 1, 4, 1, 5]
def baseStart_163524 : Nat := 118140960795 + 163524 * 2 ^ 59
def prefixEnd_163524 : Nat := 4983230072969 + 3 ^ 40 * 163524 * 2
def baseEnd_163524 : Nat := 37318404687077086799099

theorem tailTrace_163524 : CollatzResearch.WordTrace tailWord_163524 prefixEnd_163524 37318404687077086799099 := by
  unfold tailWord_163524
  simp only [CollatzResearch.WordTrace]
  refine ⟨2982105129793975260436813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3976140173058633680582417 2982105129793975260436813)
  ·
    refine ⟨1118289423672740722663805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2982105129793975260436813 1118289423672740722663805)
    ·
      refine ⟨419358533877277770998927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1118289423672740722663805 419358533877277770998927)
      ·
        refine ⟨629037800815916656498391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 419358533877277770998927 629037800815916656498391)
        ·
          refine ⟨943556701223874984747587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 629037800815916656498391 943556701223874984747587)
          ·
            refine ⟨1415335051835812477121381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 943556701223874984747587 1415335051835812477121381)
            ·
              refine ⟨265375322219214839460259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1415335051835812477121381 265375322219214839460259)
              ·
                refine ⟨398062983328822259190389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 265375322219214839460259 398062983328822259190389)
                ·
                  refine ⟨37318404687077086799099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 398062983328822259190389 37318404687077086799099)
                  ·
                    rfl

theorem cell21_163524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 1, 5].length) (baseStart_163524 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_163524 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_163524 prefixEnd_163524 := by exact prefixLift 163524
  have htrace : WordTrace (prefixWord ++ tailWord_163524) baseStart_163524 baseEnd_163524 := by
    simpa [prefixWord, tailWord_163524, baseEnd_163524] using wordTrace_append hprefix tailTrace_163524
  have hstable : (prefixWord ++ tailWord_163524).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163524).length < 2 ^ (prefixWord ++ tailWord_163524).sum := by decide
  have hdescent : baseEnd_163524 < baseStart_163524 := by decide
  rcases family_descends (prefixWord ++ tailWord_163524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163572 : List Nat := [2, 6, 1, 1, 1, 1, 2, 1, 6]
def baseStart_163572 : Nat := 118140960795 + 163572 * 2 ^ 59
def prefixEnd_163572 : Nat := 4983230072969 + 3 ^ 40 * 163572 * 2
def baseEnd_163572 : Nat := 37329358941039669999001

theorem tailTrace_163572 : CollatzResearch.WordTrace tailWord_163572 prefixEnd_163572 37329358941039669999001 := by
  unfold tailWord_163572
  simp only [CollatzResearch.WordTrace]
  refine ⟨2982980481707027359310485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3977307308942703145747313 2982980481707027359310485)
  ·
    refine ⟨139827210080016907467679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 2982980481707027359310485 139827210080016907467679)
    ·
      refine ⟨209740815120025361201519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139827210080016907467679 209740815120025361201519)
      ·
        refine ⟨314611222680038041802279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209740815120025361201519 314611222680038041802279)
        ·
          refine ⟨471916834020057062703419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 314611222680038041802279 471916834020057062703419)
          ·
            refine ⟨707875251030085594055129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 471916834020057062703419 707875251030085594055129)
            ·
              refine ⟨530906438272564195541347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 707875251030085594055129 530906438272564195541347)
              ·
                refine ⟨796359657408846293312021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 530906438272564195541347 796359657408846293312021)
                ·
                  refine ⟨37329358941039669999001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 796359657408846293312021 37329358941039669999001)
                  ·
                    rfl

theorem cell21_163572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_163572 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_163572 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_163572 prefixEnd_163572 := by exact prefixLift 163572
  have htrace : WordTrace (prefixWord ++ tailWord_163572) baseStart_163572 baseEnd_163572 := by
    simpa [prefixWord, tailWord_163572, baseEnd_163572] using wordTrace_append hprefix tailTrace_163572
  have hstable : (prefixWord ++ tailWord_163572).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163572).length < 2 ^ (prefixWord ++ tailWord_163572).sum := by decide
  have hdescent : baseEnd_163572 < baseStart_163572 := by decide
  rcases family_descends (prefixWord ++ tailWord_163572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163583 : List Nat := [1, 1, 2, 2, 1, 3, 5, 1, 5]
def baseStart_163583 : Nat := 118140960795 + 163583 * 2 ^ 59
def prefixEnd_163583 : Nat := 4983230072969 + 3 ^ 40 * 163583 * 2
def baseEnd_163583 : Nat := 37331869290906095315645

theorem tailTrace_163583 : CollatzResearch.WordTrace tailWord_163583 prefixEnd_163583 37331869290906095315645 := by
  unfold tailWord_163583
  simp only [CollatzResearch.WordTrace]
  refine ⟨5966362166374203597271403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3977574777582802398180935 5966362166374203597271403)
  ·
    refine ⟨8949543249561305395907105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5966362166374203597271403 8949543249561305395907105)
    ·
      refine ⟨6712157437170979046930329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8949543249561305395907105 6712157437170979046930329)
      ·
        refine ⟨5034118077878234285197747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6712157437170979046930329 5034118077878234285197747)
        ·
          refine ⟨7551177116817351427796621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5034118077878234285197747 7551177116817351427796621)
          ·
            refine ⟨2831691418806506785423733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7551177116817351427796621 2831691418806506785423733)
            ·
              refine ⟨265471070513110011133475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2831691418806506785423733 265471070513110011133475)
              ·
                refine ⟨398206605769665016700213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 265471070513110011133475 398206605769665016700213)
                ·
                  refine ⟨37331869290906095315645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 398206605769665016700213 37331869290906095315645)
                  ·
                    rfl

theorem cell21_163583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 1, 5].length) (baseStart_163583 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_163583 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_163583 prefixEnd_163583 := by exact prefixLift 163583
  have htrace : WordTrace (prefixWord ++ tailWord_163583) baseStart_163583 baseEnd_163583 := by
    simpa [prefixWord, tailWord_163583, baseEnd_163583] using wordTrace_append hprefix tailTrace_163583
  have hstable : (prefixWord ++ tailWord_163583).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163583).length < 2 ^ (prefixWord ++ tailWord_163583).sum := by decide
  have hdescent : baseEnd_163583 < baseStart_163583 := by decide
  rcases family_descends (prefixWord ++ tailWord_163583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163634 : List Nat := [3, 2, 1, 1, 3, 4, 2, 2, 3]
def baseStart_163634 : Nat := 118140960795 + 163634 * 2 ^ 59
def prefixEnd_163634 : Nat := 4983230072969 + 3 ^ 40 * 163634 * 2
def baseEnd_163634 : Nat := 37343508185741339965541

theorem tailTrace_163634 : CollatzResearch.WordTrace tailWord_163634 prefixEnd_163634 37343508185741339965541 := by
  unfold tailWord_163634
  simp only [CollatzResearch.WordTrace]
  refine ⟨1492055572297359826844489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3978814859459626204918637 1492055572297359826844489)
  ·
    refine ⟨1119041679223019870133367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1492055572297359826844489 1119041679223019870133367)
    ·
      refine ⟨1678562518834529805200051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1119041679223019870133367 1678562518834529805200051)
      ·
        refine ⟨2517843778251794707800077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1678562518834529805200051 2517843778251794707800077)
        ·
          refine ⟨944191416844423015425029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2517843778251794707800077 944191416844423015425029)
          ·
            refine ⟨177035890658329315392193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 944191416844423015425029 177035890658329315392193)
            ·
              refine ⟨132776917993746986544145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 177035890658329315392193 132776917993746986544145)
              ·
                refine ⟨99582688495310239908109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 132776917993746986544145 99582688495310239908109)
                ·
                  refine ⟨37343508185741339965541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 99582688495310239908109 37343508185741339965541)
                  ·
                    rfl

theorem cell21_163634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 2, 2, 3].length) (baseStart_163634 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_163634 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_163634 prefixEnd_163634 := by exact prefixLift 163634
  have htrace : WordTrace (prefixWord ++ tailWord_163634) baseStart_163634 baseEnd_163634 := by
    simpa [prefixWord, tailWord_163634, baseEnd_163634] using wordTrace_append hprefix tailTrace_163634
  have hstable : (prefixWord ++ tailWord_163634).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163634).length < 2 ^ (prefixWord ++ tailWord_163634).sum := by decide
  have hdescent : baseEnd_163634 < baseStart_163634 := by decide
  rcases family_descends (prefixWord ++ tailWord_163634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163645 : List Nat := [1, 4, 1, 4, 1, 1, 3, 6]
def baseStart_163645 : Nat := 118140960795 + 163645 * 2 ^ 59
def prefixEnd_163645 : Nat := 4983230072969 + 3 ^ 40 * 163645 * 2
def baseEnd_163645 : Nat := 12448672845202588427395

theorem tailTrace_163645 : CollatzResearch.WordTrace tailWord_163645 prefixEnd_163645 12448672845202588427395 := by
  unfold tailWord_163645
  simp only [CollatzResearch.WordTrace]
  refine ⟨5968623492149588186028389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3979082328099725457352259 5968623492149588186028389)
  ·
    refine ⟨1119116904778047784880323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5968623492149588186028389 1119116904778047784880323)
    ·
      refine ⟨1678675357167071677320485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1119116904778047784880323 1678675357167071677320485)
      ·
        refine ⟨314751629468825939497591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1678675357167071677320485 314751629468825939497591)
        ·
          refine ⟨472127444203238909246387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 314751629468825939497591 472127444203238909246387)
          ·
            refine ⟨708191166304858363869581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 472127444203238909246387 708191166304858363869581)
            ·
              refine ⟨265571687364321886451093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 708191166304858363869581 265571687364321886451093)
              ·
                refine ⟨12448672845202588427395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 265571687364321886451093 12448672845202588427395)
                ·
                  rfl

theorem cell21_163645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 6].length) (baseStart_163645 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_163645 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_163645 prefixEnd_163645 := by exact prefixLift 163645
  have htrace : WordTrace (prefixWord ++ tailWord_163645) baseStart_163645 baseEnd_163645 := by
    simpa [prefixWord, tailWord_163645, baseEnd_163645] using wordTrace_append hprefix tailTrace_163645
  have hstable : (prefixWord ++ tailWord_163645).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163645).length < 2 ^ (prefixWord ++ tailWord_163645).sum := by decide
  have hdescent : baseEnd_163645 < baseStart_163645 := by decide
  rcases family_descends (prefixWord ++ tailWord_163645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163673 : List Nat := [1, 2, 1, 2, 2, 3, 2, 2, 6]
def baseStart_163673 : Nat := 118140960795 + 163673 * 2 ^ 59
def prefixEnd_163673 : Nat := 4983230072969 + 3 ^ 40 * 163673 * 2
def baseEnd_163673 : Nat := 37352408517085938815461

theorem tailTrace_163673 : CollatzResearch.WordTrace tailWord_163673 prefixEnd_163673 37352408517085938815461 := by
  unfold tailWord_163673
  simp only [CollatzResearch.WordTrace]
  refine ⟨5969644736048148968047673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3979763157365432645365115 5969644736048148968047673)
  ·
    refine ⟨4477233552036111726035755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5969644736048148968047673 4477233552036111726035755)
    ·
      refine ⟨6715850328054167589053633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4477233552036111726035755 6715850328054167589053633)
      ·
        refine ⟨5036887746040625691790225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6715850328054167589053633 5036887746040625691790225)
        ·
          refine ⟨3777665809530469268842669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5036887746040625691790225 3777665809530469268842669)
          ·
            refine ⟨1416624678573925975816001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3777665809530469268842669 1416624678573925975816001)
            ·
              refine ⟨1062468508930444481862001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1416624678573925975816001 1062468508930444481862001)
              ·
                refine ⟨796851381697833361396501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1062468508930444481862001 796851381697833361396501)
                ·
                  refine ⟨37352408517085938815461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 796851381697833361396501 37352408517085938815461)
                  ·
                    rfl

theorem cell21_163673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 2, 6].length) (baseStart_163673 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_163673 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_163673 prefixEnd_163673 := by exact prefixLift 163673
  have htrace : WordTrace (prefixWord ++ tailWord_163673) baseStart_163673 baseEnd_163673 := by
    simpa [prefixWord, tailWord_163673, baseEnd_163673] using wordTrace_append hprefix tailTrace_163673
  have hstable : (prefixWord ++ tailWord_163673).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163673).length < 2 ^ (prefixWord ++ tailWord_163673).sum := by decide
  have hdescent : baseEnd_163673 < baseStart_163673 := by decide
  rcases family_descends (prefixWord ++ tailWord_163673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163839 : List Nat := [1, 1, 2, 2, 1, 2, 1, 11]
def baseStart_163839 : Nat := 118140960795 + 163839 * 2 ^ 59
def prefixEnd_163839 : Nat := 4983230072969 + 3 ^ 40 * 163839 * 2
def baseEnd_163839 : Nat := 12463430659568846349485

theorem tailTrace_163839 : CollatzResearch.WordTrace tailWord_163839 prefixEnd_163839 12463430659568846349485 := by
  unfold tailWord_163839
  simp only [CollatzResearch.WordTrace]
  refine ⟨5975699253446759318590571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3983799502297839545727047 5975699253446759318590571)
  ·
    refine ⟨8963548880170138977885857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5975699253446759318590571 8963548880170138977885857)
    ·
      refine ⟨6722661660127604233414393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8963548880170138977885857 6722661660127604233414393)
      ·
        refine ⟨5041996245095703175060795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6722661660127604233414393 5041996245095703175060795)
        ·
          refine ⟨7562994367643554762591193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5041996245095703175060795 7562994367643554762591193)
          ·
            refine ⟨5672245775732666071943395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7562994367643554762591193 5672245775732666071943395)
            ·
              refine ⟨8508368663598999107915093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5672245775732666071943395 8508368663598999107915093)
              ·
                refine ⟨12463430659568846349485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 8508368663598999107915093 12463430659568846349485)
                ·
                  rfl

theorem cell21_163839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 11].length) (baseStart_163839 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_163839 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_163839 prefixEnd_163839 := by exact prefixLift 163839
  have htrace : WordTrace (prefixWord ++ tailWord_163839) baseStart_163839 baseEnd_163839 := by
    simpa [prefixWord, tailWord_163839, baseEnd_163839] using wordTrace_append hprefix tailTrace_163839
  have hstable : (prefixWord ++ tailWord_163839).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163839).length < 2 ^ (prefixWord ++ tailWord_163839).sum := by decide
  have hdescent : baseEnd_163839 < baseStart_163839 := by decide
  rcases family_descends (prefixWord ++ tailWord_163839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163876 : List Nat := [2, 3, 1, 4, 2, 1, 3, 1, 4]
def baseStart_163876 : Nat := 118140960795 + 163876 * 2 ^ 59
def prefixEnd_163876 : Nat := 4983230072969 + 3 ^ 40 * 163876 * 2
def baseEnd_163876 : Nat := 37398735882802696931713

theorem tailTrace_163876 : CollatzResearch.WordTrace tailWord_163876 prefixEnd_163876 37398735882802696931713 := by
  unfold tailWord_163876
  simp only [CollatzResearch.WordTrace]
  refine ⟨2988524377156357318843741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3984699169541809758458321 2988524377156357318843741)
  ·
    refine ⟨1120696641433633994566403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2988524377156357318843741 1120696641433633994566403)
    ·
      refine ⟨1681044962150450991849605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1120696641433633994566403 1681044962150450991849605)
      ·
        refine ⟨315195930403209560971801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1681044962150450991849605 315195930403209560971801)
        ·
          refine ⟨236396947802407170728851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 315195930403209560971801 236396947802407170728851)
          ·
            refine ⟨354595421703610756093277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 236396947802407170728851 354595421703610756093277)
            ·
              refine ⟨132973283138854033534979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 354595421703610756093277 132973283138854033534979)
              ·
                refine ⟨199459924708281050302469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132973283138854033534979 199459924708281050302469)
                ·
                  refine ⟨37398735882802696931713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 199459924708281050302469 37398735882802696931713)
                  ·
                    rfl

theorem cell21_163876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 3, 1, 4].length) (baseStart_163876 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_163876 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_163876 prefixEnd_163876 := by exact prefixLift 163876
  have htrace : WordTrace (prefixWord ++ tailWord_163876) baseStart_163876 baseEnd_163876 := by
    simpa [prefixWord, tailWord_163876, baseEnd_163876] using wordTrace_append hprefix tailTrace_163876
  have hstable : (prefixWord ++ tailWord_163876).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163876).length < 2 ^ (prefixWord ++ tailWord_163876).sum := by decide
  have hdescent : baseEnd_163876 < baseStart_163876 := by decide
  rcases family_descends (prefixWord ++ tailWord_163876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163901 : List Nat := [1, 4, 1, 3, 1, 1, 1, 1, 8]
def baseStart_163901 : Nat := 118140960795 + 163901 * 2 ^ 59
def prefixEnd_163901 : Nat := 4983230072969 + 3 ^ 40 * 163901 * 2
def baseEnd_163901 : Nat := 37404441223408209014995

theorem tailTrace_163901 : CollatzResearch.WordTrace tailWord_163901 prefixEnd_163901 37404441223408209014995 := by
  unfold tailWord_163901
  simp only [CollatzResearch.WordTrace]
  refine ⟨5977960579222143907347557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3985307052814762604898371 5977960579222143907347557)
  ·
    refine ⟨1120867608604151982627667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5977960579222143907347557 1120867608604151982627667)
    ·
      refine ⟨1681301412906227973941501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1120867608604151982627667 1681301412906227973941501)
      ·
        refine ⟨630488029839835490228063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1681301412906227973941501 630488029839835490228063)
        ·
          refine ⟨945732044759753235342095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 630488029839835490228063 945732044759753235342095)
          ·
            refine ⟨1418598067139629853013143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 945732044759753235342095 1418598067139629853013143)
            ·
              refine ⟨2127897100709444779519715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1418598067139629853013143 2127897100709444779519715)
              ·
                refine ⟨3191845651064167169279573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2127897100709444779519715 3191845651064167169279573)
                ·
                  refine ⟨37404441223408209014995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3191845651064167169279573 37404441223408209014995)
                  ·
                    rfl

theorem cell21_163901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 8].length) (baseStart_163901 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_163901 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_163901 prefixEnd_163901 := by exact prefixLift 163901
  have htrace : WordTrace (prefixWord ++ tailWord_163901) baseStart_163901 baseEnd_163901 := by
    simpa [prefixWord, tailWord_163901, baseEnd_163901] using wordTrace_append hprefix tailTrace_163901
  have hstable : (prefixWord ++ tailWord_163901).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163901).length < 2 ^ (prefixWord ++ tailWord_163901).sum := by decide
  have hdescent : baseEnd_163901 < baseStart_163901 := by decide
  rcases family_descends (prefixWord ++ tailWord_163901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163904 : List Nat := [2, 1, 1, 2, 2, 4, 3, 3, 3]
def baseStart_163904 : Nat := 118140960795 + 163904 * 2 ^ 59
def prefixEnd_163904 : Nat := 4983230072969 + 3 ^ 40 * 163904 * 2
def baseEnd_163904 : Nat := 37405125864280870464989

theorem tailTrace_163904 : CollatzResearch.WordTrace tailWord_163904 prefixEnd_163904 37405125864280870464989 := by
  unfold tailWord_163904
  simp only [CollatzResearch.WordTrace]
  refine ⟨2989034999105637709853383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3985379998807516946471177 2989034999105637709853383)
  ·
    refine ⟨4483552498658456564780075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2989034999105637709853383 4483552498658456564780075)
    ·
      refine ⟨6725328747987684847170113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4483552498658456564780075 6725328747987684847170113)
      ·
        refine ⟨5043996560990763635377585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6725328747987684847170113 5043996560990763635377585)
        ·
          refine ⟨3782997420743072726533189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5043996560990763635377585 3782997420743072726533189)
          ·
            refine ⟨709312016389326136224973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3782997420743072726533189 709312016389326136224973)
            ·
              refine ⟨265992006145997301084365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 709312016389326136224973 265992006145997301084365)
              ·
                refine ⟨99747002304748987906637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 265992006145997301084365 99747002304748987906637)
                ·
                  refine ⟨37405125864280870464989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 99747002304748987906637 37405125864280870464989)
                  ·
                    rfl

theorem cell21_163904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 3, 3].length) (baseStart_163904 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_163904 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_163904 prefixEnd_163904 := by exact prefixLift 163904
  have htrace : WordTrace (prefixWord ++ tailWord_163904) baseStart_163904 baseEnd_163904 := by
    simpa [prefixWord, tailWord_163904, baseEnd_163904] using wordTrace_append hprefix tailTrace_163904
  have hstable : (prefixWord ++ tailWord_163904).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163904).length < 2 ^ (prefixWord ++ tailWord_163904).sum := by decide
  have hdescent : baseEnd_163904 < baseStart_163904 := by decide
  rcases family_descends (prefixWord ++ tailWord_163904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163932 : List Nat := [2, 2, 4, 1, 1, 2, 1, 8]
def baseStart_163932 : Nat := 118140960795 + 163932 * 2 ^ 59
def prefixEnd_163932 : Nat := 4983230072969 + 3 ^ 40 * 163932 * 2
def baseEnd_163932 : Nat := 12470505281919681332755

theorem tailTrace_163932 : CollatzResearch.WordTrace tailWord_163932 prefixEnd_163932 12470505281919681332755 := by
  unfold tailWord_163932
  simp only [CollatzResearch.WordTrace]
  refine ⟨2989545621054918100863025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3986060828073224134484033 2989545621054918100863025)
  ·
    refine ⟨2242159215791188575647269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2989545621054918100863025 2242159215791188575647269)
    ·
      refine ⟨420404852960847857933863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2242159215791188575647269 420404852960847857933863)
      ·
        refine ⟨630607279441271786900795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 420404852960847857933863 630607279441271786900795)
        ·
          refine ⟨945910919161907680351193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 630607279441271786900795 945910919161907680351193)
          ·
            refine ⟨709433189371430760263395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 945910919161907680351193 709433189371430760263395)
            ·
              refine ⟨1064149784057146140395093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 709433189371430760263395 1064149784057146140395093)
              ·
                refine ⟨12470505281919681332755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1064149784057146140395093 12470505281919681332755)
                ·
                  rfl

theorem cell21_163932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 8].length) (baseStart_163932 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_163932 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_163932 prefixEnd_163932 := by exact prefixLift 163932
  have htrace : WordTrace (prefixWord ++ tailWord_163932) baseStart_163932 baseEnd_163932 := by
    simpa [prefixWord, tailWord_163932, baseEnd_163932] using wordTrace_append hprefix tailTrace_163932
  have hstable : (prefixWord ++ tailWord_163932).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163932).length < 2 ^ (prefixWord ++ tailWord_163932).sum := by decide
  have hdescent : baseEnd_163932 < baseStart_163932 := by decide
  rcases family_descends (prefixWord ++ tailWord_163932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164028 : List Nat := [2, 2, 2, 3, 4, 1, 1, 2, 4]
def baseStart_164028 : Nat := 118140960795 + 164028 * 2 ^ 59
def prefixEnd_164028 : Nat := 4983230072969 + 3 ^ 40 * 164028 * 2
def baseEnd_164028 : Nat := 37433424353684210398069

theorem tailTrace_164028 : CollatzResearch.WordTrace tailWord_164028 prefixEnd_164028 37433424353684210398069 := by
  unfold tailWord_164028
  simp only [CollatzResearch.WordTrace]
  refine ⟨2991296324881022298610369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3988395099841363064813825 2991296324881022298610369)
  ·
    refine ⟨2243472243660766723957777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2991296324881022298610369 2243472243660766723957777)
    ·
      refine ⟨1682604182745575042968333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2243472243660766723957777 1682604182745575042968333)
      ·
        refine ⟨630976568529590641113125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1682604182745575042968333 630976568529590641113125)
        ·
          refine ⟨118308106599298245208711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 630976568529590641113125 118308106599298245208711)
          ·
            refine ⟨177462159898947367813067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118308106599298245208711 177462159898947367813067)
            ·
              refine ⟨266193239848421051719601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 177462159898947367813067 266193239848421051719601)
              ·
                refine ⟨199644929886315788789701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 266193239848421051719601 199644929886315788789701)
                ·
                  refine ⟨37433424353684210398069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 199644929886315788789701 37433424353684210398069)
                  ·
                    rfl

theorem cell21_164028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 2, 4].length) (baseStart_164028 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_164028 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_164028 prefixEnd_164028 := by exact prefixLift 164028
  have htrace : WordTrace (prefixWord ++ tailWord_164028) baseStart_164028 baseEnd_164028 := by
    simpa [prefixWord, tailWord_164028, baseEnd_164028] using wordTrace_append hprefix tailTrace_164028
  have hstable : (prefixWord ++ tailWord_164028).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164028).length < 2 ^ (prefixWord ++ tailWord_164028).sum := by decide
  have hdescent : baseEnd_164028 < baseStart_164028 := by decide
  rcases family_descends (prefixWord ++ tailWord_164028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164191 : List Nat := [1, 1, 2, 3, 1, 2, 3, 5, 3]
def baseStart_164191 : Nat := 118140960795 + 164191 * 2 ^ 59
def prefixEnd_164191 : Nat := 4983230072969 + 3 ^ 40 * 164191 * 2
def baseEnd_164191 : Nat := 37470623174432149181069

theorem tailTrace_164191 : CollatzResearch.WordTrace tailWord_164191 prefixEnd_164191 37470623174432149181069 := by
  unfold tailWord_164191
  simp only [CollatzResearch.WordTrace]
  refine ⟨5988537748171523435404427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3992358498781015623602951 5988537748171523435404427)
  ·
    refine ⟨8982806622257285153106641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5988537748171523435404427 8982806622257285153106641)
    ·
      refine ⟨6737104966692963864829981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8982806622257285153106641 6737104966692963864829981)
      ·
        refine ⟨2526414362509861449311243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6737104966692963864829981 2526414362509861449311243)
        ·
          refine ⟨3789621543764792173966865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2526414362509861449311243 3789621543764792173966865)
          ·
            refine ⟨2842216157823594130475149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3789621543764792173966865 2842216157823594130475149)
            ·
              refine ⟨1065831059183847798928181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2842216157823594130475149 1065831059183847798928181)
              ·
                refine ⟨99921661798485731149517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1065831059183847798928181 99921661798485731149517)
                ·
                  refine ⟨37470623174432149181069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 99921661798485731149517 37470623174432149181069)
                  ·
                    rfl

theorem cell21_164191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 5, 3].length) (baseStart_164191 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_164191 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_164191 prefixEnd_164191 := by exact prefixLift 164191
  have htrace : WordTrace (prefixWord ++ tailWord_164191) baseStart_164191 baseEnd_164191 := by
    simpa [prefixWord, tailWord_164191, baseEnd_164191] using wordTrace_append hprefix tailTrace_164191
  have hstable : (prefixWord ++ tailWord_164191).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164191).length < 2 ^ (prefixWord ++ tailWord_164191).sum := by decide
  have hdescent : baseEnd_164191 < baseStart_164191 := by decide
  rcases family_descends (prefixWord ++ tailWord_164191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164205 : List Nat := [1, 5, 1, 1, 1, 2, 3, 1, 6]
def baseStart_164205 : Nat := 118140960795 + 164205 * 2 ^ 59
def prefixEnd_164205 : Nat := 4983230072969 + 3 ^ 40 * 164205 * 2
def baseEnd_164205 : Nat := 37473818165171235947707

theorem tailTrace_164205 : CollatzResearch.WordTrace tailWord_164205 prefixEnd_164205 37473818165171235947707 := by
  unfold tailWord_164205
  simp only [CollatzResearch.WordTrace]
  refine ⟨5989048370120803826414069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3992698913413869217609379 5989048370120803826414069)
  ·
    refine ⟨561473284698825358726319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5989048370120803826414069 561473284698825358726319)
    ·
      refine ⟨842209927048238038089479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 561473284698825358726319 842209927048238038089479)
      ·
        refine ⟨1263314890572357057134219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 842209927048238038089479 1263314890572357057134219)
        ·
          refine ⟨1894972335858535585701329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1263314890572357057134219 1894972335858535585701329)
          ·
            refine ⟨1421229251893901689275997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1894972335858535585701329 1421229251893901689275997)
            ·
              refine ⟨532960969460213133478499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1421229251893901689275997 532960969460213133478499)
              ·
                refine ⟨799441454190319700217749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 532960969460213133478499 799441454190319700217749)
                ·
                  refine ⟨37473818165171235947707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 799441454190319700217749 37473818165171235947707)
                  ·
                    rfl

theorem cell21_164205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_164205 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_164205 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_164205 prefixEnd_164205 := by exact prefixLift 164205
  have htrace : WordTrace (prefixWord ++ tailWord_164205) baseStart_164205 baseEnd_164205 := by
    simpa [prefixWord, tailWord_164205, baseEnd_164205] using wordTrace_append hprefix tailTrace_164205
  have hstable : (prefixWord ++ tailWord_164205).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164205).length < 2 ^ (prefixWord ++ tailWord_164205).sum := by decide
  have hdescent : baseEnd_164205 < baseStart_164205 := by decide
  rcases family_descends (prefixWord ++ tailWord_164205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164236 : List Nat := [2, 2, 1, 2, 1, 4, 4, 5]
def baseStart_164236 : Nat := 118140960795 + 164236 * 2 ^ 59
def prefixEnd_164236 : Nat := 4983230072969 + 3 ^ 40 * 164236 * 2
def baseEnd_164236 : Nat := 12493630929174023643659

theorem tailTrace_164236 : CollatzResearch.WordTrace tailWord_164236 prefixEnd_164236 12493630929174023643659 := by
  unfold tailWord_164236
  simp only [CollatzResearch.WordTrace]
  refine ⟨2995089516504248060396281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3993452688672330747195041 2995089516504248060396281)
  ·
    refine ⟨2246317137378186045297211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2995089516504248060396281 2246317137378186045297211)
    ·
      refine ⟨3369475706067279067945817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2246317137378186045297211 3369475706067279067945817)
      ·
        refine ⟨2527106779550459300959363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3369475706067279067945817 2527106779550459300959363)
        ·
          refine ⟨3790660169325688951439045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2527106779550459300959363 3790660169325688951439045)
          ·
            refine ⟨710748781748566678394821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3790660169325688951439045 710748781748566678394821)
            ·
              refine ⟨133265396577856252199029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 710748781748566678394821 133265396577856252199029)
              ·
                refine ⟨12493630929174023643659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 133265396577856252199029 12493630929174023643659)
                ·
                  rfl

theorem cell21_164236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 4, 5].length) (baseStart_164236 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_164236 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_164236 prefixEnd_164236 := by exact prefixLift 164236
  have htrace : WordTrace (prefixWord ++ tailWord_164236) baseStart_164236 baseEnd_164236 := by
    simpa [prefixWord, tailWord_164236, baseEnd_164236] using wordTrace_append hprefix tailTrace_164236
  have hstable : (prefixWord ++ tailWord_164236).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164236).length < 2 ^ (prefixWord ++ tailWord_164236).sum := by decide
  have hdescent : baseEnd_164236 < baseStart_164236 := by decide
  rcases family_descends (prefixWord ++ tailWord_164236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164253 : List Nat := [1, 4, 2, 1, 5, 1, 7]
def baseStart_164253 : Nat := 118140960795 + 164253 * 2 ^ 59
def prefixEnd_164253 : Nat := 4983230072969 + 3 ^ 40 * 164253 * 2
def baseEnd_164253 : Nat := 4164974713237091016401

theorem tailTrace_164253 : CollatzResearch.WordTrace tailWord_164253 prefixEnd_164253 4164974713237091016401 := by
  unfold tailWord_164253
  simp only [CollatzResearch.WordTrace]
  refine ⟨5990799073946908024161413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3993866049297938682774275 5990799073946908024161413)
  ·
    refine ⟨1123274826365045254530265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5990799073946908024161413 1123274826365045254530265)
    ·
      refine ⟨842456119773783940897699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1123274826365045254530265 842456119773783940897699)
      ·
        refine ⟨1263684179660675911346549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 842456119773783940897699 1263684179660675911346549)
        ·
          refine ⟨118470391843188366688739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1263684179660675911346549 118470391843188366688739)
          ·
            refine ⟨177705587764782550033109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118470391843188366688739 177705587764782550033109)
            ·
              refine ⟨4164974713237091016401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 177705587764782550033109 4164974713237091016401)
              ·
                rfl

theorem cell21_164253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 7].length) (baseStart_164253 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_164253 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_164253 prefixEnd_164253 := by exact prefixLift 164253
  have htrace : WordTrace (prefixWord ++ tailWord_164253) baseStart_164253 baseEnd_164253 := by
    simpa [prefixWord, tailWord_164253, baseEnd_164253] using wordTrace_append hprefix tailTrace_164253
  have hstable : (prefixWord ++ tailWord_164253).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164253).length < 2 ^ (prefixWord ++ tailWord_164253).sum := by decide
  have hdescent : baseEnd_164253 < baseStart_164253 := by decide
  rcases family_descends (prefixWord ++ tailWord_164253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164295 : List Nat := [1, 1, 4, 1, 1, 4, 2, 7]
def baseStart_164295 : Nat := 118140960795 + 164295 * 2 ^ 59
def prefixEnd_164295 : Nat := 4983230072969 + 3 ^ 40 * 164295 * 2
def baseEnd_164295 : Nat := 12498119130450359815841

theorem tailTrace_164295 : CollatzResearch.WordTrace tailWord_164295 prefixEnd_164295 12498119130450359815841 := by
  unfold tailWord_164295
  simp only [CollatzResearch.WordTrace]
  refine ⟨5992330939794749197190339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3994887293196499464793559 5992330939794749197190339)
  ·
    refine ⟨8988496409692123795785509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5992330939794749197190339 8988496409692123795785509)
    ·
      refine ⟨1685343076817273211709783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8988496409692123795785509 1685343076817273211709783)
      ·
        refine ⟨2528014615225909817564675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1685343076817273211709783 2528014615225909817564675)
        ·
          refine ⟨3792021922838864726347013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2528014615225909817564675 3792021922838864726347013)
          ·
            refine ⟨711004110532287136190065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3792021922838864726347013 711004110532287136190065)
            ·
              refine ⟨533253082899215352142549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 711004110532287136190065 533253082899215352142549)
              ·
                refine ⟨12498119130450359815841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 533253082899215352142549 12498119130450359815841)
                ·
                  rfl

theorem cell21_164295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 7].length) (baseStart_164295 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_164295 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_164295 prefixEnd_164295 := by exact prefixLift 164295
  have htrace : WordTrace (prefixWord ++ tailWord_164295) baseStart_164295 baseEnd_164295 := by
    simpa [prefixWord, tailWord_164295, baseEnd_164295] using wordTrace_append hprefix tailTrace_164295
  have hstable : (prefixWord ++ tailWord_164295).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164295).length < 2 ^ (prefixWord ++ tailWord_164295).sum := by decide
  have hdescent : baseEnd_164295 < baseStart_164295 := by decide
  rcases family_descends (prefixWord ++ tailWord_164295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164402 : List Nat := [3, 2, 1, 1, 2, 1, 4, 2, 5]
def baseStart_164402 : Nat := 118140960795 + 164402 * 2 ^ 59
def prefixEnd_164402 : Nat := 4983230072969 + 3 ^ 40 * 164402 * 2
def baseEnd_164402 : Nat := 37518776249142671163971

theorem tailTrace_164402 : CollatzResearch.WordTrace tailWord_164402 prefixEnd_164402 37518776249142671163971 := by
  unfold tailWord_164402
  simp only [CollatzResearch.WordTrace]
  refine ⟨1499058387601776617833865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3997489033604737647556973 1499058387601776617833865)
  ·
    refine ⟨1124293790701332463375399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1499058387601776617833865 1124293790701332463375399)
    ·
      refine ⟨1686440686051998695063099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1124293790701332463375399 1686440686051998695063099)
      ·
        refine ⟨2529661029077998042594649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1686440686051998695063099 2529661029077998042594649)
        ·
          refine ⟨1897245771808498531945987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2529661029077998042594649 1897245771808498531945987)
          ·
            refine ⟨2845868657712747797918981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1897245771808498531945987 2845868657712747797918981)
            ·
              refine ⟨533600373321140212109809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2845868657712747797918981 533600373321140212109809)
              ·
                refine ⟨400200279990855159082357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 533600373321140212109809 400200279990855159082357)
                ·
                  refine ⟨37518776249142671163971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 400200279990855159082357 37518776249142671163971)
                  ·
                    rfl

theorem cell21_164402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 2, 5].length) (baseStart_164402 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_164402 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_164402 prefixEnd_164402 := by exact prefixLift 164402
  have htrace : WordTrace (prefixWord ++ tailWord_164402) baseStart_164402 baseEnd_164402 := by
    simpa [prefixWord, tailWord_164402, baseEnd_164402] using wordTrace_append hprefix tailTrace_164402
  have hstable : (prefixWord ++ tailWord_164402).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164402).length < 2 ^ (prefixWord ++ tailWord_164402).sum := by decide
  have hdescent : baseEnd_164402 < baseStart_164402 := by decide
  rcases family_descends (prefixWord ++ tailWord_164402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164416 : List Nat := [2, 1, 1, 2, 2, 2, 3, 2, 6]
def baseStart_164416 : Nat := 118140960795 + 164416 * 2 ^ 59
def prefixEnd_164416 : Nat := 4983230072969 + 3 ^ 40 * 164416 * 2
def baseEnd_164416 : Nat := 37521971239881757930609

theorem tailTrace_164416 : CollatzResearch.WordTrace tailWord_164416 prefixEnd_164416 37521971239881757930609 := by
  unfold tailWord_164416
  simp only [CollatzResearch.WordTrace]
  refine ⟨2998372086178193431172551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3997829448237591241563401 2998372086178193431172551)
  ·
    refine ⟨4497558129267290146758827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2998372086178193431172551 4497558129267290146758827)
    ·
      refine ⟨6746337193900935220138241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4497558129267290146758827 6746337193900935220138241)
      ·
        refine ⟨5059752895425701415103681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6746337193900935220138241 5059752895425701415103681)
        ·
          refine ⟨3794814671569276061327761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5059752895425701415103681 3794814671569276061327761)
          ·
            refine ⟨2846111003676957045995821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3794814671569276061327761 2846111003676957045995821)
            ·
              refine ⟨1067291626378858892248433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2846111003676957045995821 1067291626378858892248433)
              ·
                refine ⟨800468719784144169186325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1067291626378858892248433 800468719784144169186325)
                ·
                  refine ⟨37521971239881757930609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 800468719784144169186325 37521971239881757930609)
                  ·
                    rfl

theorem cell21_164416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 2, 6].length) (baseStart_164416 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_164416 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_164416 prefixEnd_164416 := by exact prefixLift 164416
  have htrace : WordTrace (prefixWord ++ tailWord_164416) baseStart_164416 baseEnd_164416 := by
    simpa [prefixWord, tailWord_164416, baseEnd_164416] using wordTrace_append hprefix tailTrace_164416
  have hstable : (prefixWord ++ tailWord_164416).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164416).length < 2 ^ (prefixWord ++ tailWord_164416).sum := by decide
  have hdescent : baseEnd_164416 < baseStart_164416 := by decide
  rcases family_descends (prefixWord ++ tailWord_164416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164509 : List Nat := [1, 4, 2, 1, 1, 1, 4, 3, 4]
def baseStart_164509 : Nat := 118140960795 + 164509 * 2 ^ 59
def prefixEnd_164509 : Nat := 4983230072969 + 3 ^ 40 * 164509 * 2
def baseEnd_164509 : Nat := 37543195106934262880419

theorem tailTrace_164509 : CollatzResearch.WordTrace tailWord_164509 prefixEnd_164509 37543195106934262880419 := by
  unfold tailWord_164509
  simp only [CollatzResearch.WordTrace]
  refine ⟨6000136161019463745480581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4000090774012975830320387 6000136161019463745480581)
  ·
    refine ⟨1125025530191149452277609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6000136161019463745480581 1125025530191149452277609)
    ·
      refine ⟨843769147643362089208207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1125025530191149452277609 843769147643362089208207)
      ·
        refine ⟨1265653721465043133812311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 843769147643362089208207 1265653721465043133812311)
        ·
          refine ⟨1898480582197564700718467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1265653721465043133812311 1898480582197564700718467)
          ·
            refine ⟨2847720873296347051077701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1898480582197564700718467 2847720873296347051077701)
            ·
              refine ⟨533947663743065072077069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2847720873296347051077701 533947663743065072077069)
              ·
                refine ⟨200230373903649402028901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 533947663743065072077069 200230373903649402028901)
                ·
                  refine ⟨37543195106934262880419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 200230373903649402028901 37543195106934262880419)
                  ·
                    rfl

theorem cell21_164509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 3, 4].length) (baseStart_164509 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_164509 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_164509 prefixEnd_164509 := by exact prefixLift 164509
  have htrace : WordTrace (prefixWord ++ tailWord_164509) baseStart_164509 baseEnd_164509 := by
    simpa [prefixWord, tailWord_164509, baseEnd_164509] using wordTrace_append hprefix tailTrace_164509
  have hstable : (prefixWord ++ tailWord_164509).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164509).length < 2 ^ (prefixWord ++ tailWord_164509).sum := by decide
  have hdescent : baseEnd_164509 < baseStart_164509 := by decide
  rcases family_descends (prefixWord ++ tailWord_164509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164529 : List Nat := [1, 2, 2, 6, 1, 1, 2, 3, 3]
def baseStart_164529 : Nat := 118140960795 + 164529 * 2 ^ 59
def prefixEnd_164529 : Nat := 4983230072969 + 3 ^ 40 * 164529 * 2
def baseEnd_164529 : Nat := 37547759379418672547045

theorem tailTrace_164529 : CollatzResearch.WordTrace tailWord_164529 prefixEnd_164529 37547759379418672547045 := by
  unfold tailWord_164529
  simp only [CollatzResearch.WordTrace]
  refine ⟨6000865620947007161208641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4000577080631338107472427 6000865620947007161208641)
  ·
    refine ⟨4500649215710255370906481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6000865620947007161208641 4500649215710255370906481)
    ·
      refine ⟨3375486911782691528179861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4500649215710255370906481 3375486911782691528179861)
      ·
        refine ⟨158225948989813665383431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 3375486911782691528179861 158225948989813665383431)
        ·
          refine ⟨237338923484720498075147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158225948989813665383431 237338923484720498075147)
          ·
            refine ⟨356008385227080747112721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 237338923484720498075147 356008385227080747112721)
            ·
              refine ⟨267006288920310560334541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 356008385227080747112721 267006288920310560334541)
              ·
                refine ⟨100127358345116460125453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 267006288920310560334541 100127358345116460125453)
                ·
                  refine ⟨37547759379418672547045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 100127358345116460125453 37547759379418672547045)
                  ·
                    rfl

theorem cell21_164529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 3, 3].length) (baseStart_164529 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_164529 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_164529 prefixEnd_164529 := by exact prefixLift 164529
  have htrace : WordTrace (prefixWord ++ tailWord_164529) baseStart_164529 baseEnd_164529 := by
    simpa [prefixWord, tailWord_164529, baseEnd_164529] using wordTrace_append hprefix tailTrace_164529
  have hstable : (prefixWord ++ tailWord_164529).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164529).length < 2 ^ (prefixWord ++ tailWord_164529).sum := by decide
  have hdescent : baseEnd_164529 < baseStart_164529 := by decide
  rcases family_descends (prefixWord ++ tailWord_164529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164537 : List Nat := [1, 2, 1, 4, 1, 1, 1, 1, 9]
def baseStart_164537 : Nat := 118140960795 + 164537 * 2 ^ 59
def prefixEnd_164537 : Nat := 4983230072969 + 3 ^ 40 * 164537 * 2
def baseEnd_164537 : Nat := 37549585088412436413695

theorem tailTrace_164537 : CollatzResearch.WordTrace tailWord_164537 prefixEnd_164537 37549585088412436413695 := by
  unfold tailWord_164537
  simp only [CollatzResearch.WordTrace]
  refine ⟨6001157404918024527499865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4000771603278683018333243 6001157404918024527499865)
  ·
    refine ⟨4500868053688518395624899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6001157404918024527499865 4500868053688518395624899)
    ·
      refine ⟨6751302080532777593437349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4500868053688518395624899 6751302080532777593437349)
      ·
        refine ⟨1265869140099895798769503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6751302080532777593437349 1265869140099895798769503)
        ·
          refine ⟨1898803710149843698154255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1265869140099895798769503 1898803710149843698154255)
          ·
            refine ⟨2848205565224765547231383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1898803710149843698154255 2848205565224765547231383)
            ·
              refine ⟨4272308347837148320847075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2848205565224765547231383 4272308347837148320847075)
              ·
                refine ⟨6408462521755722481270613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4272308347837148320847075 6408462521755722481270613)
                ·
                  refine ⟨37549585088412436413695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 6408462521755722481270613 37549585088412436413695)
                  ·
                    rfl

theorem cell21_164537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 9].length) (baseStart_164537 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_164537 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_164537 prefixEnd_164537 := by exact prefixLift 164537
  have htrace : WordTrace (prefixWord ++ tailWord_164537) baseStart_164537 baseEnd_164537 := by
    simpa [prefixWord, tailWord_164537, baseEnd_164537] using wordTrace_append hprefix tailTrace_164537
  have hstable : (prefixWord ++ tailWord_164537).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164537).length < 2 ^ (prefixWord ++ tailWord_164537).sum := by decide
  have hdescent : baseEnd_164537 < baseStart_164537 := by decide
  rcases family_descends (prefixWord ++ tailWord_164537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164554 : List Nat := [3, 1, 2, 1, 4, 1, 1, 3, 5]
def baseStart_164554 : Nat := 118140960795 + 164554 * 2 ^ 59
def prefixEnd_164554 : Nat := 4983230072969 + 3 ^ 40 * 164554 * 2
def baseEnd_164554 : Nat := 37553464720024184630327

theorem tailTrace_164554 : CollatzResearch.WordTrace tailWord_164554 prefixEnd_164554 37553464720024184630327 := by
  unfold tailWord_164554
  simp only [CollatzResearch.WordTrace]
  refine ⟨1500444361464109107717179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4001184963904290953912477 1500444361464109107717179)
  ·
    refine ⟨2250666542196163661575769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1500444361464109107717179 2250666542196163661575769)
    ·
      refine ⟨1687999906647122746181827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2250666542196163661575769 1687999906647122746181827)
      ·
        refine ⟨2531999859970684119272741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1687999906647122746181827 2531999859970684119272741)
        ·
          refine ⟨474749973744503272363639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2531999859970684119272741 474749973744503272363639)
          ·
            refine ⟨712124960616754908545459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 474749973744503272363639 712124960616754908545459)
            ·
              refine ⟨1068187440925132362818189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 712124960616754908545459 1068187440925132362818189)
              ·
                refine ⟨400570290346924636056821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1068187440925132362818189 400570290346924636056821)
                ·
                  refine ⟨37553464720024184630327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 400570290346924636056821 37553464720024184630327)
                  ·
                    rfl

theorem cell21_164554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 3, 5].length) (baseStart_164554 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_164554 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_164554 prefixEnd_164554 := by exact prefixLift 164554
  have htrace : WordTrace (prefixWord ++ tailWord_164554) baseStart_164554 baseEnd_164554 := by
    simpa [prefixWord, tailWord_164554, baseEnd_164554] using wordTrace_append hprefix tailTrace_164554
  have hstable : (prefixWord ++ tailWord_164554).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164554).length < 2 ^ (prefixWord ++ tailWord_164554).sum := by decide
  have hdescent : baseEnd_164554 < baseStart_164554 := by decide
  rcases family_descends (prefixWord ++ tailWord_164554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164661 : List Nat := [1, 3, 3, 1, 3, 1, 1, 4, 4]
def baseStart_164661 : Nat := 118140960795 + 164661 * 2 ^ 59
def prefixEnd_164661 : Nat := 4983230072969 + 3 ^ 40 * 164661 * 2
def baseEnd_164661 : Nat := 37577883577815776346775

theorem tailTrace_164661 : CollatzResearch.WordTrace tailWord_164661 prefixEnd_164661 37577883577815776346775 := by
  unfold tailWord_164661
  simp only [CollatzResearch.WordTrace]
  refine ⟨6005680056468793705013837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4003786704312529136675891 6005680056468793705013837)
  ·
    refine ⟨2252130021175797639380189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6005680056468793705013837 2252130021175797639380189)
    ·
      refine ⟨844548757940924114767571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2252130021175797639380189 844548757940924114767571)
      ·
        refine ⟨1266823136911386172151357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 844548757940924114767571 1266823136911386172151357)
        ·
          refine ⟨475058676341769814556759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1266823136911386172151357 475058676341769814556759)
          ·
            refine ⟨712588014512654721835139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 475058676341769814556759 712588014512654721835139)
            ·
              refine ⟨1068882021768982082752709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 712588014512654721835139 1068882021768982082752709)
              ·
                refine ⟨200415379081684140516133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1068882021768982082752709 200415379081684140516133)
                ·
                  refine ⟨37577883577815776346775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 200415379081684140516133 37577883577815776346775)
                  ·
                    rfl

theorem cell21_164661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 4, 4].length) (baseStart_164661 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_164661 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_164661 prefixEnd_164661 := by exact prefixLift 164661
  have htrace : WordTrace (prefixWord ++ tailWord_164661) baseStart_164661 baseEnd_164661 := by
    simpa [prefixWord, tailWord_164661, baseEnd_164661] using wordTrace_append hprefix tailTrace_164661
  have hstable : (prefixWord ++ tailWord_164661).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164661).length < 2 ^ (prefixWord ++ tailWord_164661).sum := by decide
  have hdescent : baseEnd_164661 < baseStart_164661 := by decide
  rcases family_descends (prefixWord ++ tailWord_164661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164788 : List Nat := [2, 5, 2, 1, 1, 3, 2, 1, 4]
def baseStart_164788 : Nat := 118140960795 + 164788 * 2 ^ 59
def prefixEnd_164788 : Nat := 4983230072969 + 3 ^ 40 * 164788 * 2
def baseEnd_164788 : Nat := 37606866708091777729849

theorem tailTrace_164788 : CollatzResearch.WordTrace tailWord_164788 prefixEnd_164788 37606866708091777729849 := by
  unfold tailWord_164788
  simp only [CollatzResearch.WordTrace]
  refine ⟨3005156063504347197443509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4006874751339129596591345 3005156063504347197443509)
  ·
    refine ⟨281733380953532549760329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3005156063504347197443509 281733380953532549760329)
    ·
      refine ⟨211300035715149412320247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 281733380953532549760329 211300035715149412320247)
      ·
        refine ⟨316950053572724118480371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211300035715149412320247 316950053572724118480371)
        ·
          refine ⟨475425080359086177720557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 316950053572724118480371 475425080359086177720557)
          ·
            refine ⟨178284405134657316645209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 475425080359086177720557 178284405134657316645209)
            ·
              refine ⟨133713303850992987483907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 178284405134657316645209 133713303850992987483907)
              ·
                refine ⟨200569955776489481225861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133713303850992987483907 200569955776489481225861)
                ·
                  refine ⟨37606866708091777729849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 200569955776489481225861 37606866708091777729849)
                  ·
                    rfl

theorem cell21_164788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_164788 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_164788 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_164788 prefixEnd_164788 := by exact prefixLift 164788
  have htrace : WordTrace (prefixWord ++ tailWord_164788) baseStart_164788 baseEnd_164788 := by
    simpa [prefixWord, tailWord_164788, baseEnd_164788] using wordTrace_append hprefix tailTrace_164788
  have hstable : (prefixWord ++ tailWord_164788).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164788).length < 2 ^ (prefixWord ++ tailWord_164788).sum := by decide
  have hdescent : baseEnd_164788 < baseStart_164788 := by decide
  rcases family_descends (prefixWord ++ tailWord_164788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164875 : List Nat := [1, 1, 1, 1, 6, 3, 2, 3, 3]
def baseStart_164875 : Nat := 118140960795 + 164875 * 2 ^ 59
def prefixEnd_164875 : Nat := 4983230072969 + 3 ^ 40 * 164875 * 2
def baseEnd_164875 : Nat := 37626721293398959779671

theorem tailTrace_164875 : CollatzResearch.WordTrace tailWord_164875 prefixEnd_164875 37626721293398959779671 := by
  unfold tailWord_164875
  simp only [CollatzResearch.WordTrace]
  refine ⟨6013485277693508253304079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4008990185129005502202719 6013485277693508253304079)
  ·
    refine ⟨9020227916540262379956119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6013485277693508253304079 9020227916540262379956119)
    ·
      refine ⟨13530341874810393569934179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9020227916540262379956119 13530341874810393569934179)
      ·
        refine ⟨20295512812215590354901269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13530341874810393569934179 20295512812215590354901269)
        ·
          refine ⟨951352163072605797885997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 20295512812215590354901269 951352163072605797885997)
          ·
            refine ⟨356757061152227174207249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 951352163072605797885997 356757061152227174207249)
            ·
              refine ⟨267567795864170380655437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 356757061152227174207249 267567795864170380655437)
              ·
                refine ⟨100337923449063892745789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 267567795864170380655437 100337923449063892745789)
                ·
                  refine ⟨37626721293398959779671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 100337923449063892745789 37626721293398959779671)
                  ·
                    rfl

theorem cell21_164875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 3, 3].length) (baseStart_164875 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_164875 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_164875 prefixEnd_164875 := by exact prefixLift 164875
  have htrace : WordTrace (prefixWord ++ tailWord_164875) baseStart_164875 baseEnd_164875 := by
    simpa [prefixWord, tailWord_164875, baseEnd_164875] using wordTrace_append hprefix tailTrace_164875
  have hstable : (prefixWord ++ tailWord_164875).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164875).length < 2 ^ (prefixWord ++ tailWord_164875).sum := by decide
  have hdescent : baseEnd_164875 < baseStart_164875 := by decide
  rcases family_descends (prefixWord ++ tailWord_164875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164920 : List Nat := [2, 1, 2, 1, 5, 3, 2, 5]
def baseStart_164920 : Nat := 118140960795 + 164920 * 2 ^ 59
def prefixEnd_164920 : Nat := 4983230072969 + 3 ^ 40 * 164920 * 2
def baseEnd_164920 : Nat := 12545663635496293843193

theorem tailTrace_164920 : CollatzResearch.WordTrace tailWord_164920 prefixEnd_164920 12545663635496293843193 := by
  unfold tailWord_164920
  simp only [CollatzResearch.WordTrace]
  refine ⟨3007563281265240469346107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4010084375020320625794809 3007563281265240469346107)
  ·
    refine ⟨4511344921897860704019161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3007563281265240469346107 4511344921897860704019161)
    ·
      refine ⟨3383508691423395528014371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4511344921897860704019161 3383508691423395528014371)
      ·
        refine ⟨5075263037135093292021557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3383508691423395528014371 5075263037135093292021557)
        ·
          refine ⟨475805909731414996127021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5075263037135093292021557 475805909731414996127021)
          ·
            refine ⟨178427216149280623547633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 475805909731414996127021 178427216149280623547633)
            ·
              refine ⟨133820412111960467660725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 178427216149280623547633 133820412111960467660725)
              ·
                refine ⟨12545663635496293843193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 133820412111960467660725 12545663635496293843193)
                ·
                  rfl

theorem cell21_164920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 2, 5].length) (baseStart_164920 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_164920 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_164920 prefixEnd_164920 := by exact prefixLift 164920
  have htrace : WordTrace (prefixWord ++ tailWord_164920) baseStart_164920 baseEnd_164920 := by
    simpa [prefixWord, tailWord_164920, baseEnd_164920] using wordTrace_append hprefix tailTrace_164920
  have hstable : (prefixWord ++ tailWord_164920).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164920).length < 2 ^ (prefixWord ++ tailWord_164920).sum := by decide
  have hdescent : baseEnd_164920 < baseStart_164920 := by decide
  rcases family_descends (prefixWord ++ tailWord_164920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164931 : List Nat := [1, 1, 1, 3, 1, 2, 3, 1, 8]
def baseStart_164931 : Nat := 118140960795 + 164931 * 2 ^ 59
def prefixEnd_164931 : Nat := 4983230072969 + 3 ^ 40 * 164931 * 2
def baseEnd_164931 : Nat := 37639501256355306846223

theorem tailTrace_164931 : CollatzResearch.WordTrace tailWord_164931 prefixEnd_164931 37639501256355306846223 := by
  unfold tailWord_164931
  simp only [CollatzResearch.WordTrace]
  refine ⟨6015527765490629817342647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4010351843660419878228431 6015527765490629817342647)
  ·
    refine ⟨9023291648235944726013971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6015527765490629817342647 9023291648235944726013971)
    ·
      refine ⟨13534937472353917089020957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9023291648235944726013971 13534937472353917089020957)
      ·
        refine ⟨5075601552132718908382859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13534937472353917089020957 5075601552132718908382859)
        ·
          refine ⟨7613402328199078362574289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5075601552132718908382859 7613402328199078362574289)
          ·
            refine ⟨5710051746149308771930717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7613402328199078362574289 5710051746149308771930717)
            ·
              refine ⟨2141269404805990789474019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5710051746149308771930717 2141269404805990789474019)
              ·
                refine ⟨3211904107208986184211029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2141269404805990789474019 3211904107208986184211029)
                ·
                  refine ⟨37639501256355306846223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3211904107208986184211029 37639501256355306846223)
                  ·
                    rfl

theorem cell21_164931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 8].length) (baseStart_164931 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_164931 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_164931 prefixEnd_164931 := by exact prefixLift 164931
  have htrace : WordTrace (prefixWord ++ tailWord_164931) baseStart_164931 baseEnd_164931 := by
    simpa [prefixWord, tailWord_164931, baseEnd_164931] using wordTrace_append hprefix tailTrace_164931
  have hstable : (prefixWord ++ tailWord_164931).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164931).length < 2 ^ (prefixWord ++ tailWord_164931).sum := by decide
  have hdescent : baseEnd_164931 < baseStart_164931 := by decide
  rcases family_descends (prefixWord ++ tailWord_164931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164948 : List Nat := [2, 4, 1, 1, 1, 1, 4, 1, 6]
def baseStart_164948 : Nat := 118140960795 + 164948 * 2 ^ 59
def prefixEnd_164948 : Nat := 4983230072969 + 3 ^ 40 * 164948 * 2
def baseEnd_164948 : Nat := 37643380887967055062855

theorem tailTrace_164948 : CollatzResearch.WordTrace tailWord_164948 prefixEnd_164948 37643380887967055062855 := by
  unfold tailWord_164948
  simp only [CollatzResearch.WordTrace]
  refine ⟨3008073903214520860355749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4010765204286027813807665 3008073903214520860355749)
  ·
    refine ⟨564013856852722661316703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3008073903214520860355749 564013856852722661316703)
    ·
      refine ⟨846020785279083991975055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 564013856852722661316703 846020785279083991975055)
      ·
        refine ⟨1269031177918625987962583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 846020785279083991975055 1269031177918625987962583)
        ·
          refine ⟨1903546766877938981943875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1269031177918625987962583 1903546766877938981943875)
          ·
            refine ⟨2855320150316908472915813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1903546766877938981943875 2855320150316908472915813)
            ·
              refine ⟨535372528184420338671715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2855320150316908472915813 535372528184420338671715)
              ·
                refine ⟨803058792276630508007573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 535372528184420338671715 803058792276630508007573)
                ·
                  refine ⟨37643380887967055062855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 803058792276630508007573 37643380887967055062855)
                  ·
                    rfl

theorem cell21_164948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_164948 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_164948 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_164948 prefixEnd_164948 := by exact prefixLift 164948
  have htrace : WordTrace (prefixWord ++ tailWord_164948) baseStart_164948 baseEnd_164948 := by
    simpa [prefixWord, tailWord_164948, baseEnd_164948] using wordTrace_append hprefix tailTrace_164948
  have hstable : (prefixWord ++ tailWord_164948).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164948).length < 2 ^ (prefixWord ++ tailWord_164948).sum := by decide
  have hdescent : baseEnd_164948 < baseStart_164948 := by decide
  rcases family_descends (prefixWord ++ tailWord_164948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165024 : List Nat := [2, 1, 1, 4, 2, 1, 1, 5, 4]
def baseStart_165024 : Nat := 118140960795 + 165024 * 2 ^ 59
def prefixEnd_165024 : Nat := 4983230072969 + 3 ^ 40 * 165024 * 2
def baseEnd_165024 : Nat := 37660725123407811796033

theorem tailTrace_165024 : CollatzResearch.WordTrace tailWord_165024 prefixEnd_165024 37660725123407811796033 := by
  unfold tailWord_165024
  simp only [CollatzResearch.WordTrace]
  refine ⟨3009459877076853350239063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4012613169435804466985417 3009459877076853350239063)
  ·
    refine ⟨4514189815615280025358595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3009459877076853350239063 4514189815615280025358595)
    ·
      refine ⟨6771284723422920038037893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4514189815615280025358595 6771284723422920038037893)
      ·
        refine ⟨1269615885641797507132105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6771284723422920038037893 1269615885641797507132105)
        ·
          refine ⟨952211914231348130349079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1269615885641797507132105 952211914231348130349079)
          ·
            refine ⟨1428317871347022195523619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 952211914231348130349079 1428317871347022195523619)
            ·
              refine ⟨2142476807020533293285429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1428317871347022195523619 2142476807020533293285429)
              ·
                refine ⟨200857200658174996245509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2142476807020533293285429 200857200658174996245509)
                ·
                  refine ⟨37660725123407811796033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 200857200658174996245509 37660725123407811796033)
                  ·
                    rfl

theorem cell21_165024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 5, 4].length) (baseStart_165024 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_165024 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_165024 prefixEnd_165024 := by exact prefixLift 165024
  have htrace : WordTrace (prefixWord ++ tailWord_165024) baseStart_165024 baseEnd_165024 := by
    simpa [prefixWord, tailWord_165024, baseEnd_165024] using wordTrace_append hprefix tailTrace_165024
  have hstable : (prefixWord ++ tailWord_165024).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165024).length < 2 ^ (prefixWord ++ tailWord_165024).sum := by decide
  have hdescent : baseEnd_165024 < baseStart_165024 := by decide
  rcases family_descends (prefixWord ++ tailWord_165024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165134 : List Nat := [4, 1, 1, 2, 1, 5, 2, 1, 4]
def baseStart_165134 : Nat := 118140960795 + 165134 * 2 ^ 59
def prefixEnd_165134 : Nat := 4983230072969 + 3 ^ 40 * 165134 * 2
def baseEnd_165134 : Nat := 37685828622072064962475

theorem tailTrace_165134 : CollatzResearch.WordTrace tailWord_165134 prefixEnd_165134 37685828622072064962475 := by
  unfold tailWord_165134
  simp only [CollatzResearch.WordTrace]
  refine ⟨752866472969399435872807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4015287855836796991321637 752866472969399435872807)
  ·
    refine ⟨1129299709454099153809211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 752866472969399435872807 1129299709454099153809211)
    ·
      refine ⟨1693949564181148730713817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1129299709454099153809211 1693949564181148730713817)
      ·
        refine ⟨1270462173135861548035363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1693949564181148730713817 1270462173135861548035363)
        ·
          refine ⟨1905693259703792322053045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1270462173135861548035363 1905693259703792322053045)
          ·
            refine ⟨178658743097230530192473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1905693259703792322053045 178658743097230530192473)
            ·
              refine ⟨133994057322922897644355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 178658743097230530192473 133994057322922897644355)
              ·
                refine ⟨200991085984384346466533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133994057322922897644355 200991085984384346466533)
                ·
                  refine ⟨37685828622072064962475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 200991085984384346466533 37685828622072064962475)
                  ·
                    rfl

theorem cell21_165134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 2, 1, 4].length) (baseStart_165134 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_165134 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_165134 prefixEnd_165134 := by exact prefixLift 165134
  have htrace : WordTrace (prefixWord ++ tailWord_165134) baseStart_165134 baseEnd_165134 := by
    simpa [prefixWord, tailWord_165134, baseEnd_165134] using wordTrace_append hprefix tailTrace_165134
  have hstable : (prefixWord ++ tailWord_165134).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165134).length < 2 ^ (prefixWord ++ tailWord_165134).sum := by decide
  have hdescent : baseEnd_165134 < baseStart_165134 := by decide
  rcases family_descends (prefixWord ++ tailWord_165134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165207 : List Nat := [1, 1, 3, 2, 3, 3, 3, 5]
def baseStart_165207 : Nat := 118140960795 + 165207 * 2 ^ 59
def prefixEnd_165207 : Nat := 4983230072969 + 3 ^ 40 * 165207 * 2
def baseEnd_165207 : Nat := 12567496072213386748553

theorem tailTrace_165207 : CollatzResearch.WordTrace tailWord_165207 prefixEnd_165207 12567496072213386748553 := by
  unfold tailWord_165207
  simp only [CollatzResearch.WordTrace]
  refine ⟨6025594312490728954389875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4017062874993819302926583 6025594312490728954389875)
  ·
    refine ⟨9038391468736093431584813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6025594312490728954389875 9038391468736093431584813)
    ·
      refine ⟨3389396800776035036844305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9038391468736093431584813 3389396800776035036844305)
      ·
        refine ⟨2542047600582026277633229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3389396800776035036844305 2542047600582026277633229)
        ·
          refine ⟨953267850218259854112461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2542047600582026277633229 953267850218259854112461)
          ·
            refine ⟨357475443831847445292173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 953267850218259854112461 357475443831847445292173)
            ·
              refine ⟨134053291436942791984565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 357475443831847445292173 134053291436942791984565)
              ·
                refine ⟨12567496072213386748553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 134053291436942791984565 12567496072213386748553)
                ·
                  rfl

theorem cell21_165207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 3, 5].length) (baseStart_165207 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_165207 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_165207 prefixEnd_165207 := by exact prefixLift 165207
  have htrace : WordTrace (prefixWord ++ tailWord_165207) baseStart_165207 baseEnd_165207 := by
    simpa [prefixWord, tailWord_165207, baseEnd_165207] using wordTrace_append hprefix tailTrace_165207
  have hstable : (prefixWord ++ tailWord_165207).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165207).length < 2 ^ (prefixWord ++ tailWord_165207).sum := by decide
  have hdescent : baseEnd_165207 < baseStart_165207 := by decide
  rcases family_descends (prefixWord ++ tailWord_165207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165272 : List Nat := [2, 1, 2, 5, 2, 2, 1, 3, 3]
def baseStart_165272 : Nat := 118140960795 + 165272 * 2 ^ 59
def prefixEnd_165272 : Nat := 4983230072969 + 3 ^ 40 * 165272 * 2
def baseEnd_165272 : Nat := 37717322102214491662193

theorem tailTrace_165272 : CollatzResearch.WordTrace tailWord_165272 prefixEnd_165272 37717322102214491662193 := by
  unfold tailWord_165272
  simp only [CollatzResearch.WordTrace]
  refine ⟨3013982528627622527753035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4018643371503496703670713 3013982528627622527753035)
  ·
    refine ⟨4520973792941433791629553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3013982528627622527753035 4520973792941433791629553)
    ·
      refine ⟨3390730344706075343722165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4520973792941433791629553 3390730344706075343722165)
      ·
        refine ⟨317880969816194563473953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3390730344706075343722165 317880969816194563473953)
        ·
          refine ⟨238410727362145922605465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 317880969816194563473953 238410727362145922605465)
          ·
            refine ⟨178808045521609441954099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 238410727362145922605465 178808045521609441954099)
            ·
              refine ⟨268212068282414162931149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178808045521609441954099 268212068282414162931149)
              ·
                refine ⟨100579525605905311099181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 268212068282414162931149 100579525605905311099181)
                ·
                  refine ⟨37717322102214491662193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 100579525605905311099181 37717322102214491662193)
                  ·
                    rfl

theorem cell21_165272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 3, 3].length) (baseStart_165272 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_165272 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_165272 prefixEnd_165272 := by exact prefixLift 165272
  have htrace : WordTrace (prefixWord ++ tailWord_165272) baseStart_165272 baseEnd_165272 := by
    simpa [prefixWord, tailWord_165272, baseEnd_165272] using wordTrace_append hprefix tailTrace_165272
  have hstable : (prefixWord ++ tailWord_165272).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165272).length < 2 ^ (prefixWord ++ tailWord_165272).sum := by decide
  have hdescent : baseEnd_165272 < baseStart_165272 := by decide
  rcases family_descends (prefixWord ++ tailWord_165272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165373 : List Nat := [1, 4, 1, 1, 1, 5, 1, 2, 5]
def baseStart_165373 : Nat := 118140960795 + 165373 * 2 ^ 59
def prefixEnd_165373 : Nat := 4983230072969 + 3 ^ 40 * 165373 * 2
def baseEnd_165373 : Nat := 37740371678260760478653

theorem tailTrace_165373 : CollatzResearch.WordTrace tailWord_165373 prefixEnd_165373 37740371678260760478653 := by
  unfold tailWord_165373
  simp only [CollatzResearch.WordTrace]
  refine ⟨6031648829889339304932773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4021099219926226203288515 6031648829889339304932773)
  ·
    refine ⟨1130934155604251119674895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6031648829889339304932773 1130934155604251119674895)
    ·
      refine ⟨1696401233406376679512343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1130934155604251119674895 1696401233406376679512343)
      ·
        refine ⟨2544601850109565019268515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1696401233406376679512343 2544601850109565019268515)
        ·
          refine ⟨3816902775164347528902773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2544601850109565019268515 3816902775164347528902773)
          ·
            refine ⟨357834635171657580834635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3816902775164347528902773 357834635171657580834635)
            ·
              refine ⟨536751952757486371251953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 357834635171657580834635 536751952757486371251953)
              ·
                refine ⟨402563964568114778438965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 536751952757486371251953 402563964568114778438965)
                ·
                  refine ⟨37740371678260760478653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 402563964568114778438965 37740371678260760478653)
                  ·
                    rfl

theorem cell21_165373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 2, 5].length) (baseStart_165373 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_165373 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_165373 prefixEnd_165373 := by exact prefixLift 165373
  have htrace : WordTrace (prefixWord ++ tailWord_165373) baseStart_165373 baseEnd_165373 := by
    simpa [prefixWord, tailWord_165373, baseEnd_165373] using wordTrace_append hprefix tailTrace_165373
  have hstable : (prefixWord ++ tailWord_165373).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165373).length < 2 ^ (prefixWord ++ tailWord_165373).sum := by decide
  have hdescent : baseEnd_165373 < baseStart_165373 := by decide
  rcases family_descends (prefixWord ++ tailWord_165373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165382 : List Nat := [6, 2, 1, 1, 2, 1, 2, 3, 3]
def baseStart_165382 : Nat := 118140960795 + 165382 * 2 ^ 59
def prefixEnd_165382 : Nat := 4983230072969 + 3 ^ 40 * 165382 * 2
def baseEnd_165382 : Nat := 37742425600878744828635

theorem tailTrace_165382 : CollatzResearch.WordTrace tailWord_165382 prefixEnd_165382 37742425600878744828635 := by
  unfold tailWord_165382
  simp only [CollatzResearch.WordTrace]
  refine ⟨188499283964272932562825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 4021318057904489228006933 188499283964272932562825)
  ·
    refine ⟨141374462973204699422119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 188499283964272932562825 141374462973204699422119)
    ·
      refine ⟨212061694459807049133179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141374462973204699422119 212061694459807049133179)
      ·
        refine ⟨318092541689710573699769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212061694459807049133179 318092541689710573699769)
        ·
          refine ⟨238569406267282930274827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 318092541689710573699769 238569406267282930274827)
          ·
            refine ⟨357854109400924395412241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238569406267282930274827 357854109400924395412241)
            ·
              refine ⟨268390582050693296559181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 357854109400924395412241 268390582050693296559181)
              ·
                refine ⟨100646468269009986209693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 268390582050693296559181 100646468269009986209693)
                ·
                  refine ⟨37742425600878744828635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 100646468269009986209693 37742425600878744828635)
                  ·
                    rfl

theorem cell21_165382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_165382 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_165382 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_165382 prefixEnd_165382 := by exact prefixLift 165382
  have htrace : WordTrace (prefixWord ++ tailWord_165382) baseStart_165382 baseEnd_165382 := by
    simpa [prefixWord, tailWord_165382, baseEnd_165382] using wordTrace_append hprefix tailTrace_165382
  have hstable : (prefixWord ++ tailWord_165382).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165382).length < 2 ^ (prefixWord ++ tailWord_165382).sum := by decide
  have hdescent : baseEnd_165382 < baseStart_165382 := by decide
  rcases family_descends (prefixWord ++ tailWord_165382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165418 : List Nat := [3, 1, 4, 1, 1, 1, 2, 8]
def baseStart_165418 : Nat := 118140960795 + 165418 * 2 ^ 59
def prefixEnd_165418 : Nat := 4983230072969 + 3 ^ 40 * 165418 * 2
def baseEnd_165418 : Nat := 12583547097116894076187

theorem tailTrace_165418 : CollatzResearch.WordTrace tailWord_165418 prefixEnd_165418 12583547097116894076187 := by
  unfold tailWord_165418
  simp only [CollatzResearch.WordTrace]
  refine ⟨1508322528681577997580227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4022193409817541326880605 1508322528681577997580227)
  ·
    refine ⟨2262483793022366996370341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1508322528681577997580227 2262483793022366996370341)
    ·
      refine ⟨424215711191693811819439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2262483793022366996370341 424215711191693811819439)
      ·
        refine ⟨636323566787540717729159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 424215711191693811819439 636323566787540717729159)
        ·
          refine ⟨954485350181311076593739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 636323566787540717729159 954485350181311076593739)
          ·
            refine ⟨1431728025271966614890609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 954485350181311076593739 1431728025271966614890609)
            ·
              refine ⟨1073796018953974961167957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1431728025271966614890609 1073796018953974961167957)
              ·
                refine ⟨12583547097116894076187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1073796018953974961167957 12583547097116894076187)
                ·
                  rfl

theorem cell21_165418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 8].length) (baseStart_165418 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_165418 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_165418 prefixEnd_165418 := by exact prefixLift 165418
  have htrace : WordTrace (prefixWord ++ tailWord_165418) baseStart_165418 baseEnd_165418 := by
    simpa [prefixWord, tailWord_165418, baseEnd_165418] using wordTrace_append hprefix tailTrace_165418
  have hstable : (prefixWord ++ tailWord_165418).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165418).length < 2 ^ (prefixWord ++ tailWord_165418).sum := by decide
  have hdescent : baseEnd_165418 < baseStart_165418 := by decide
  rcases family_descends (prefixWord ++ tailWord_165418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165463 : List Nat := [1, 1, 3, 2, 2, 3, 2, 1, 6]
def baseStart_165463 : Nat := 118140960795 + 165463 * 2 ^ 59
def prefixEnd_165463 : Nat := 4983230072969 + 3 ^ 40 * 165463 * 2
def baseEnd_165463 : Nat := 37760910904440603978469

theorem tailTrace_165463 : CollatzResearch.WordTrace tailWord_165463 prefixEnd_165463 37760910904440603978469 := by
  unfold tailWord_165463
  simp only [CollatzResearch.WordTrace]
  refine ⟨6034931399563284675709043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4023287599708856450472695 6034931399563284675709043)
  ·
    refine ⟨9052397099344927013563565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6034931399563284675709043 9052397099344927013563565)
    ·
      refine ⟨3394648912254347630086337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9052397099344927013563565 3394648912254347630086337)
      ·
        refine ⟨2545986684190760722564753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3394648912254347630086337 2545986684190760722564753)
        ·
          refine ⟨1909490013143070541923565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2545986684190760722564753 1909490013143070541923565)
          ·
            refine ⟨716058754928651453221337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1909490013143070541923565 716058754928651453221337)
            ·
              refine ⟨537044066196488589916003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 716058754928651453221337 537044066196488589916003)
              ·
                refine ⟨805566099294732884874005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 537044066196488589916003 805566099294732884874005)
                ·
                  refine ⟨37760910904440603978469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 805566099294732884874005 37760910904440603978469)
                  ·
                    rfl

theorem cell21_165463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 1, 6].length) (baseStart_165463 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_165463 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_165463 prefixEnd_165463 := by exact prefixLift 165463
  have htrace : WordTrace (prefixWord ++ tailWord_165463) baseStart_165463 baseEnd_165463 := by
    simpa [prefixWord, tailWord_165463, baseEnd_165463] using wordTrace_append hprefix tailTrace_165463
  have hstable : (prefixWord ++ tailWord_165463).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165463).length < 2 ^ (prefixWord ++ tailWord_165463).sum := by decide
  have hdescent : baseEnd_165463 < baseStart_165463 := by decide
  rcases family_descends (prefixWord ++ tailWord_165463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165539 : List Nat := [1, 1, 1, 4, 1, 1, 3, 5, 4]
def baseStart_165539 : Nat := 118140960795 + 165539 * 2 ^ 59
def prefixEnd_165539 : Nat := 4983230072969 + 3 ^ 40 * 165539 * 2
def baseEnd_165539 : Nat := 37778255139881360711647

theorem tailTrace_165539 : CollatzResearch.WordTrace tailWord_165539 prefixEnd_165539 37778255139881360711647 := by
  unfold tailWord_165539
  simp only [CollatzResearch.WordTrace]
  refine ⟨6037703347287949655475671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4025135564858633103650447 6037703347287949655475671)
  ·
    refine ⟨9056555020931924483213507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6037703347287949655475671 9056555020931924483213507)
    ·
      refine ⟨13584832531397886724820261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9056555020931924483213507 13584832531397886724820261)
      ·
        refine ⟨2547156099637103760903799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13584832531397886724820261 2547156099637103760903799)
        ·
          refine ⟨3820734149455655641355699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2547156099637103760903799 3820734149455655641355699)
          ·
            refine ⟨5731101224183483462033549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3820734149455655641355699 5731101224183483462033549)
            ·
              refine ⟨2149162959068806298262581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5731101224183483462033549 2149162959068806298262581)
              ·
                refine ⟨201484027412700590462117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2149162959068806298262581 201484027412700590462117)
                ·
                  refine ⟨37778255139881360711647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 201484027412700590462117 37778255139881360711647)
                  ·
                    rfl

theorem cell21_165539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 5, 4].length) (baseStart_165539 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_165539 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_165539 prefixEnd_165539 := by exact prefixLift 165539
  have htrace : WordTrace (prefixWord ++ tailWord_165539) baseStart_165539 baseEnd_165539 := by
    simpa [prefixWord, tailWord_165539, baseEnd_165539] using wordTrace_append hprefix tailTrace_165539
  have hstable : (prefixWord ++ tailWord_165539).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165539).length < 2 ^ (prefixWord ++ tailWord_165539).sum := by decide
  have hdescent : baseEnd_165539 < baseStart_165539 := by decide
  rcases family_descends (prefixWord ++ tailWord_165539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165660 : List Nat := [2, 2, 3, 1, 1, 2, 2, 1, 7]
def baseStart_165660 : Nat := 118140960795 + 165660 * 2 ^ 59
def prefixEnd_165660 : Nat := 4983230072969 + 3 ^ 40 * 165660 * 2
def baseEnd_165660 : Nat := 37805868988412039194733

theorem tailTrace_165660 : CollatzResearch.WordTrace tailWord_165660 prefixEnd_165660 37805868988412039194733 := by
  unfold tailWord_165660
  simp only [CollatzResearch.WordTrace]
  refine ⟨3021058289924793660315217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4028077719899724880420289 3021058289924793660315217)
  ·
    refine ⟨2265793717443595245236413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3021058289924793660315217 2265793717443595245236413)
    ·
      refine ⟨849672644041348216963655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2265793717443595245236413 849672644041348216963655)
      ·
        refine ⟨1274508966062022325445483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 849672644041348216963655 1274508966062022325445483)
        ·
          refine ⟨1911763449093033488168225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1274508966062022325445483 1911763449093033488168225)
          ·
            refine ⟨1433822586819775116126169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1911763449093033488168225 1433822586819775116126169)
            ·
              refine ⟨1075366940114831337094627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1433822586819775116126169 1075366940114831337094627)
              ·
                refine ⟨1613050410172247005641941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1075366940114831337094627 1613050410172247005641941)
                ·
                  refine ⟨37805868988412039194733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1613050410172247005641941 37805868988412039194733)
                  ·
                    rfl

theorem cell21_165660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 7].length) (baseStart_165660 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_165660 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_165660 prefixEnd_165660 := by exact prefixLift 165660
  have htrace : WordTrace (prefixWord ++ tailWord_165660) baseStart_165660 baseEnd_165660 := by
    simpa [prefixWord, tailWord_165660, baseEnd_165660] using wordTrace_append hprefix tailTrace_165660
  have hstable : (prefixWord ++ tailWord_165660).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165660).length < 2 ^ (prefixWord ++ tailWord_165660).sum := by decide
  have hdescent : baseEnd_165660 < baseStart_165660 := by decide
  rcases family_descends (prefixWord ++ tailWord_165660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165722 : List Nat := [3, 1, 1, 2, 1, 3, 5, 5]
def baseStart_165722 : Nat := 118140960795 + 165722 * 2 ^ 59
def prefixEnd_165722 : Nat := 4983230072969 + 3 ^ 40 * 165722 * 2
def baseEnd_165722 : Nat := 12606672744371236387091

theorem tailTrace_165722 : CollatzResearch.WordTrace tailWord_165722 prefixEnd_165722 12606672744371236387091 := by
  unfold tailWord_165722
  simp only [CollatzResearch.WordTrace]
  refine ⟨1511094476406242977346855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4029585270416647939591613 1511094476406242977346855)
  ·
    refine ⟨2266641714609364466020283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1511094476406242977346855 2266641714609364466020283)
    ·
      refine ⟨3399962571914046699030425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2266641714609364466020283 3399962571914046699030425)
      ·
        refine ⟨2549971928935535024272819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3399962571914046699030425 2549971928935535024272819)
        ·
          refine ⟨3824957893403302536409229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2549971928935535024272819 3824957893403302536409229)
          ·
            refine ⟨1434359210026238451153461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3824957893403302536409229 1434359210026238451153461)
            ·
              refine ⟨134471175939959854795637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1434359210026238451153461 134471175939959854795637)
              ·
                refine ⟨12606672744371236387091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 134471175939959854795637 12606672744371236387091)
                ·
                  rfl

theorem cell21_165722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 5, 5].length) (baseStart_165722 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_165722 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_165722 prefixEnd_165722 := by exact prefixLift 165722
  have htrace : WordTrace (prefixWord ++ tailWord_165722) baseStart_165722 baseEnd_165722 := by
    simpa [prefixWord, tailWord_165722, baseEnd_165722] using wordTrace_append hprefix tailTrace_165722
  have hstable : (prefixWord ++ tailWord_165722).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165722).length < 2 ^ (prefixWord ++ tailWord_165722).sum := by decide
  have hdescent : baseEnd_165722 < baseStart_165722 := by decide
  rcases family_descends (prefixWord ++ tailWord_165722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165736 : List Nat := [2, 1, 4, 2, 1, 1, 1, 2, 7]
def baseStart_165736 : Nat := 118140960795 + 165736 * 2 ^ 59
def prefixEnd_165736 : Nat := 4983230072969 + 3 ^ 40 * 165736 * 2
def baseEnd_165736 : Nat := 37823213223852795927911

theorem tailTrace_165736 : CollatzResearch.WordTrace tailWord_165736 prefixEnd_165736 37823213223852795927911 := by
  unfold tailWord_165736
  simp only [CollatzResearch.WordTrace]
  refine ⟨3022444263787126150198531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4029925685049501533598041 3022444263787126150198531)
  ·
    refine ⟨4533666395680689225297797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3022444263787126150198531 4533666395680689225297797)
    ·
      refine ⟨850062449190129229743337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4533666395680689225297797 850062449190129229743337)
      ·
        refine ⟨637546836892596922307503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 850062449190129229743337 637546836892596922307503)
        ·
          refine ⟨956320255338895383461255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 637546836892596922307503 956320255338895383461255)
          ·
            refine ⟨1434480383008343075191883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 956320255338895383461255 1434480383008343075191883)
            ·
              refine ⟨2151720574512514612787825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1434480383008343075191883 2151720574512514612787825)
              ·
                refine ⟨1613790430884385959590869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2151720574512514612787825 1613790430884385959590869)
                ·
                  refine ⟨37823213223852795927911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1613790430884385959590869 37823213223852795927911)
                  ·
                    rfl

theorem cell21_165736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 7].length) (baseStart_165736 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_165736 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_165736 prefixEnd_165736 := by exact prefixLift 165736
  have htrace : WordTrace (prefixWord ++ tailWord_165736) baseStart_165736 baseEnd_165736 := by
    simpa [prefixWord, tailWord_165736, baseEnd_165736] using wordTrace_append hprefix tailTrace_165736
  have hstable : (prefixWord ++ tailWord_165736).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165736).length < 2 ^ (prefixWord ++ tailWord_165736).sum := by decide
  have hdescent : baseEnd_165736 < baseStart_165736 := by decide
  rcases family_descends (prefixWord ++ tailWord_165736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165753 : List Nat := [1, 2, 1, 3, 2, 2, 1, 6, 3]
def baseStart_165753 : Nat := 118140960795 + 165753 * 2 ^ 59
def prefixEnd_165753 : Nat := 4983230072969 + 3 ^ 40 * 165753 * 2
def baseEnd_165753 : Nat := 37827092855464544144543

theorem tailTrace_165753 : CollatzResearch.WordTrace tailWord_165753 prefixEnd_165753 37827092855464544144543 := by
  unfold tailWord_165753
  simp only [CollatzResearch.WordTrace]
  refine ⟨6045508568512664203765913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4030339045675109469177275 6045508568512664203765913)
  ·
    refine ⟨4534131426384498152824435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6045508568512664203765913 4534131426384498152824435)
    ·
      refine ⟨6801197139576747229236653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4534131426384498152824435 6801197139576747229236653)
      ·
        refine ⟨2550448927341280210963745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6801197139576747229236653 2550448927341280210963745)
        ·
          refine ⟨1912836695505960158222809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2550448927341280210963745 1912836695505960158222809)
          ·
            refine ⟨1434627521629470118667107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1912836695505960158222809 1434627521629470118667107)
            ·
              refine ⟨2151941282444205178000661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1434627521629470118667107 2151941282444205178000661)
              ·
                refine ⟨100872247614572117718781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2151941282444205178000661 100872247614572117718781)
                ·
                  refine ⟨37827092855464544144543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 100872247614572117718781 37827092855464544144543)
                  ·
                    rfl

theorem cell21_165753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 6, 3].length) (baseStart_165753 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_165753 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_165753 prefixEnd_165753 := by exact prefixLift 165753
  have htrace : WordTrace (prefixWord ++ tailWord_165753) baseStart_165753 baseEnd_165753 := by
    simpa [prefixWord, tailWord_165753, baseEnd_165753] using wordTrace_append hprefix tailTrace_165753
  have hstable : (prefixWord ++ tailWord_165753).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165753).length < 2 ^ (prefixWord ++ tailWord_165753).sum := by decide
  have hdescent : baseEnd_165753 < baseStart_165753 := by decide
  rcases family_descends (prefixWord ++ tailWord_165753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165781 : List Nat := [1, 3, 2, 1, 1, 3, 3, 7]
def baseStart_165781 : Nat := 118140960795 + 165781 * 2 ^ 59
def prefixEnd_165781 : Nat := 4983230072969 + 3 ^ 40 * 165781 * 2
def baseEnd_165781 : Nat := 12611160945647572559273

theorem tailTrace_165781 : CollatzResearch.WordTrace tailWord_165781 prefixEnd_165781 12611160945647572559273 := by
  unfold tailWord_165781
  simp only [CollatzResearch.WordTrace]
  refine ⟨6046529812411224985785197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4031019874940816657190131 6046529812411224985785197)
  ·
    refine ⟨2267448679654209369669449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6046529812411224985785197 2267448679654209369669449)
    ·
      refine ⟨1700586509740657027252087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2267448679654209369669449 1700586509740657027252087)
      ·
        refine ⟨2550879764610985540878131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1700586509740657027252087 2550879764610985540878131)
        ·
          refine ⟨3826319646916478311317197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2550879764610985540878131 3826319646916478311317197)
          ·
            refine ⟨1434869867593679366743949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3826319646916478311317197 1434869867593679366743949)
            ·
              refine ⟨538076200347629762528981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1434869867593679366743949 538076200347629762528981)
              ·
                refine ⟨12611160945647572559273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 538076200347629762528981 12611160945647572559273)
                ·
                  rfl

theorem cell21_165781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 7].length) (baseStart_165781 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_165781 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_165781 prefixEnd_165781 := by exact prefixLift 165781
  have htrace : WordTrace (prefixWord ++ tailWord_165781) baseStart_165781 baseEnd_165781 := by
    simpa [prefixWord, tailWord_165781, baseEnd_165781] using wordTrace_append hprefix tailTrace_165781
  have hstable : (prefixWord ++ tailWord_165781).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165781).length < 2 ^ (prefixWord ++ tailWord_165781).sum := by decide
  have hdescent : baseEnd_165781 < baseStart_165781 := by decide
  rcases family_descends (prefixWord ++ tailWord_165781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165936 : List Nat := [2, 1, 1, 1, 2, 6, 3, 1, 4]
def baseStart_165936 : Nat := 118140960795 + 165936 * 2 ^ 59
def prefixEnd_165936 : Nat := 4983230072969 + 3 ^ 40 * 165936 * 2
def baseEnd_165936 : Nat := 37868855948696892594169

theorem tailTrace_165936 : CollatzResearch.WordTrace tailWord_165936 prefixEnd_165936 37868855948696892594169 := by
  unfold tailWord_165936
  simp only [CollatzResearch.WordTrace]
  refine ⟨3026091563424843228838831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4034788751233124305118441 3026091563424843228838831)
  ·
    refine ⟨4539137345137264843258247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3026091563424843228838831 4539137345137264843258247)
    ·
      refine ⟨6808706017705897264887371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4539137345137264843258247 6808706017705897264887371)
      ·
        refine ⟨10213059026558845897331057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6808706017705897264887371 10213059026558845897331057)
        ·
          refine ⟨7659794269919134422998293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10213059026558845897331057 7659794269919134422998293)
          ·
            refine ⟨359052856402459426078045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 7659794269919134422998293 359052856402459426078045)
            ·
              refine ⟨134644821150922284779267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 359052856402459426078045 134644821150922284779267)
              ·
                refine ⟨201967231726383427168901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134644821150922284779267 201967231726383427168901)
                ·
                  refine ⟨37868855948696892594169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 201967231726383427168901 37868855948696892594169)
                  ·
                    rfl

theorem cell21_165936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 3, 1, 4].length) (baseStart_165936 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_165936 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_165936 prefixEnd_165936 := by exact prefixLift 165936
  have htrace : WordTrace (prefixWord ++ tailWord_165936) baseStart_165936 baseEnd_165936 := by
    simpa [prefixWord, tailWord_165936, baseEnd_165936] using wordTrace_append hprefix tailTrace_165936
  have hstable : (prefixWord ++ tailWord_165936).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165936).length < 2 ^ (prefixWord ++ tailWord_165936).sum := by decide
  have hdescent : baseEnd_165936 < baseStart_165936 := by decide
  rcases family_descends (prefixWord ++ tailWord_165936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165978 : List Nat := [3, 1, 1, 2, 1, 1, 3, 3, 6]
def baseStart_165978 : Nat := 118140960795 + 165978 * 2 ^ 59
def prefixEnd_165978 : Nat := 4983230072969 + 3 ^ 40 * 165978 * 2
def baseEnd_165978 : Nat := 37878440920914152894083

theorem tailTrace_165978 : CollatzResearch.WordTrace tailWord_165978 prefixEnd_165978 37878440920914152894083 := by
  unfold tailWord_165978
  simp only [CollatzResearch.WordTrace]
  refine ⟨1513428748174381907676647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4035809995131685087137725 1513428748174381907676647)
  ·
    refine ⟨2270143122261572861514971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1513428748174381907676647 2270143122261572861514971)
    ·
      refine ⟨3405214683392359292272457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2270143122261572861514971 3405214683392359292272457)
      ·
        refine ⟨2553911012544269469204343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3405214683392359292272457 2553911012544269469204343)
        ·
          refine ⟨3830866518816404203806515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2553911012544269469204343 3830866518816404203806515)
          ·
            refine ⟨5746299778224606305709773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3830866518816404203806515 5746299778224606305709773)
            ·
              refine ⟨2154862416834227364641165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5746299778224606305709773 2154862416834227364641165)
              ·
                refine ⟨808073406312835261740437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2154862416834227364641165 808073406312835261740437)
                ·
                  refine ⟨37878440920914152894083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 808073406312835261740437 37878440920914152894083)
                  ·
                    rfl

theorem cell21_165978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 3, 6].length) (baseStart_165978 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_165978 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_165978 prefixEnd_165978 := by exact prefixLift 165978
  have htrace : WordTrace (prefixWord ++ tailWord_165978) baseStart_165978 baseEnd_165978 := by
    simpa [prefixWord, tailWord_165978, baseEnd_165978] using wordTrace_append hprefix tailTrace_165978
  have hstable : (prefixWord ++ tailWord_165978).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165978).length < 2 ^ (prefixWord ++ tailWord_165978).sum := by decide
  have hdescent : baseEnd_165978 < baseStart_165978 := by decide
  rcases family_descends (prefixWord ++ tailWord_165978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166009 : List Nat := [1, 2, 1, 3, 4, 1, 2, 7]
def baseStart_166009 : Nat := 118140960795 + 166009 * 2 ^ 59
def prefixEnd_166009 : Nat := 4983230072969 + 3 ^ 40 * 166009 * 2
def baseEnd_166009 : Nat := 12628505181088329292451

theorem tailTrace_166009 : CollatzResearch.WordTrace tailWord_166009 prefixEnd_166009 12628505181088329292451 := by
  unfold tailWord_166009
  simp only [CollatzResearch.WordTrace]
  refine ⟨6054845655585219925085081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4036563770390146616723387 6054845655585219925085081)
  ·
    refine ⟨4541134241688914943813811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6054845655585219925085081 4541134241688914943813811)
    ·
      refine ⟨6811701362533372415720717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4541134241688914943813811 6811701362533372415720717)
      ·
        refine ⟨2554388010950014655895269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6811701362533372415720717 2554388010950014655895269)
        ·
          refine ⟨478947752053127747980363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2554388010950014655895269 478947752053127747980363)
          ·
            refine ⟨718421628079691621970545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 478947752053127747980363 718421628079691621970545)
            ·
              refine ⟨538816221059768716477909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 718421628079691621970545 538816221059768716477909)
              ·
                refine ⟨12628505181088329292451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 538816221059768716477909 12628505181088329292451)
                ·
                  rfl

theorem cell21_166009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 7].length) (baseStart_166009 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_166009 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_166009 prefixEnd_166009 := by exact prefixLift 166009
  have htrace : WordTrace (prefixWord ++ tailWord_166009) baseStart_166009 baseEnd_166009 := by
    simpa [prefixWord, tailWord_166009, baseEnd_166009] using wordTrace_append hprefix tailTrace_166009
  have hstable : (prefixWord ++ tailWord_166009).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166009).length < 2 ^ (prefixWord ++ tailWord_166009).sum := by decide
  have hdescent : baseEnd_166009 < baseStart_166009 := by decide
  rcases family_descends (prefixWord ++ tailWord_166009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166119 : List Nat := [1, 1, 5, 3, 1, 3, 2, 5]
def baseStart_166119 : Nat := 118140960795 + 166119 * 2 ^ 59
def prefixEnd_166119 : Nat := 4983230072969 + 3 ^ 40 * 166119 * 2
def baseEnd_166119 : Nat := 12636873013976413681265

theorem tailTrace_166119 : CollatzResearch.WordTrace tailWord_166119 prefixEnd_166119 12636873013976413681265 := by
  unfold tailWord_166119
  simp only [CollatzResearch.WordTrace]
  refine ⟨6058857685186708711589411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4039238456791139141059607 6058857685186708711589411)
  ·
    refine ⟨9088286527780063067384117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6058857685186708711589411 9088286527780063067384117)
    ·
      refine ⟨852026861979380912567261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9088286527780063067384117 852026861979380912567261)
      ·
        refine ⟨319510073242267842212723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 852026861979380912567261 319510073242267842212723)
        ·
          refine ⟨479265109863401763319085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 319510073242267842212723 479265109863401763319085)
          ·
            refine ⟨179724416198775661244657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 479265109863401763319085 179724416198775661244657)
            ·
              refine ⟨134793312149081745933493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 179724416198775661244657 134793312149081745933493)
              ·
                refine ⟨12636873013976413681265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 134793312149081745933493 12636873013976413681265)
                ·
                  rfl

theorem cell21_166119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 2, 5].length) (baseStart_166119 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_166119 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_166119 prefixEnd_166119 := by exact prefixLift 166119
  have htrace : WordTrace (prefixWord ++ tailWord_166119) baseStart_166119 baseEnd_166119 := by
    simpa [prefixWord, tailWord_166119, baseEnd_166119] using wordTrace_append hprefix tailTrace_166119
  have hstable : (prefixWord ++ tailWord_166119).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166119).length < 2 ^ (prefixWord ++ tailWord_166119).sum := by decide
  have hdescent : baseEnd_166119 < baseStart_166119 := by decide
  rcases family_descends (prefixWord ++ tailWord_166119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166144 : List Nat := [2, 1, 1, 2, 1, 1, 13]
def baseStart_166144 : Nat := 118140960795 + 166144 * 2 ^ 59
def prefixEnd_166144 : Nat := 4983230072969 + 3 ^ 40 * 166144 * 2
def baseEnd_166144 : Nat := 4212924931392750347453

theorem tailTrace_166144 : CollatzResearch.WordTrace tailWord_166144 prefixEnd_166144 4212924931392750347453 := by
  unfold tailWord_166144
  simp only [CollatzResearch.WordTrace]
  refine ⟨3029884755048068990624743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4039846340064091987499657 3029884755048068990624743)
  ·
    refine ⟨4544827132572103485937115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3029884755048068990624743 4544827132572103485937115)
    ·
      refine ⟨6817240698858155228905673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4544827132572103485937115 6817240698858155228905673)
      ·
        refine ⟨5112930524143616421679255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6817240698858155228905673 5112930524143616421679255)
        ·
          refine ⟨7669395786215424632518883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5112930524143616421679255 7669395786215424632518883)
          ·
            refine ⟨11504093679323136948778325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7669395786215424632518883 11504093679323136948778325)
            ·
              refine ⟨4212924931392750347453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 11504093679323136948778325 4212924931392750347453)
              ·
                rfl

theorem cell21_166144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 13].length) (baseStart_166144 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_166144 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_166144 prefixEnd_166144 := by exact prefixLift 166144
  have htrace : WordTrace (prefixWord ++ tailWord_166144) baseStart_166144 baseEnd_166144 := by
    simpa [prefixWord, tailWord_166144, baseEnd_166144] using wordTrace_append hprefix tailTrace_166144
  have hstable : (prefixWord ++ tailWord_166144).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166144).length < 2 ^ (prefixWord ++ tailWord_166144).sum := by decide
  have hdescent : baseEnd_166144 < baseStart_166144 := by decide
  rcases family_descends (prefixWord ++ tailWord_166144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166161 : List Nat := [1, 2, 2, 1, 1, 6, 2, 6]
def baseStart_166161 : Nat := 118140960795 + 166161 * 2 ^ 59
def prefixEnd_166161 : Nat := 4983230072969 + 3 ^ 40 * 166161 * 2
def baseEnd_166161 : Nat := 12640068004715500447903

theorem tailTrace_166161 : CollatzResearch.WordTrace tailWord_166161 prefixEnd_166161 12640068004715500447903 := by
  unfold tailWord_166161
  simp only [CollatzResearch.WordTrace]
  refine ⟨6060389551034549884618337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4040259700689699923078891 6060389551034549884618337)
  ·
    refine ⟨4545292163275912413463753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6060389551034549884618337 4545292163275912413463753)
    ·
      refine ⟨3408969122456934310097815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4545292163275912413463753 3408969122456934310097815)
      ·
        refine ⟨5113453683685401465146723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3408969122456934310097815 5113453683685401465146723)
        ·
          refine ⟨7670180525528102197720085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5113453683685401465146723 7670180525528102197720085)
          ·
            refine ⟨359539712134129790518129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 7670180525528102197720085 359539712134129790518129)
            ·
              refine ⟨269654784100597342888597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 359539712134129790518129 269654784100597342888597)
              ·
                refine ⟨12640068004715500447903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 269654784100597342888597 12640068004715500447903)
                ·
                  rfl

theorem cell21_166161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 6].length) (baseStart_166161 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_166161 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_166161 prefixEnd_166161 := by exact prefixLift 166161
  have htrace : WordTrace (prefixWord ++ tailWord_166161) baseStart_166161 baseEnd_166161 := by
    simpa [prefixWord, tailWord_166161, baseEnd_166161] using wordTrace_append hprefix tailTrace_166161
  have hstable : (prefixWord ++ tailWord_166161).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166161).length < 2 ^ (prefixWord ++ tailWord_166161).sum := by decide
  have hdescent : baseEnd_166161 < baseStart_166161 := by decide
  rcases family_descends (prefixWord ++ tailWord_166161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166212 : List Nat := [2, 3, 4, 1, 3, 1, 1, 6]
def baseStart_166212 : Nat := 118140960795 + 166212 * 2 ^ 59
def prefixEnd_166212 : Nat := 4983230072969 + 3 ^ 40 * 166212 * 2
def baseEnd_166212 : Nat := 12643947636327248664535

theorem tailTrace_166212 : CollatzResearch.WordTrace tailWord_166212 prefixEnd_166212 12643947636327248664535 := by
  unfold tailWord_166212
  simp only [CollatzResearch.WordTrace]
  refine ⟨3031124836924892797362445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4041499782566523729816593 3031124836924892797362445)
  ·
    refine ⟨1136671813846834799010917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3031124836924892797362445 1136671813846834799010917)
    ·
      refine ⟨213125965096281524814547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1136671813846834799010917 213125965096281524814547)
      ·
        refine ⟨319688947644422287221821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213125965096281524814547 319688947644422287221821)
        ·
          refine ⟨119883355366658357708183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 319688947644422287221821 119883355366658357708183)
          ·
            refine ⟨179825033049987536562275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119883355366658357708183 179825033049987536562275)
            ·
              refine ⟨269737549574981304843413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 179825033049987536562275 269737549574981304843413)
              ·
                refine ⟨12643947636327248664535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 269737549574981304843413 12643947636327248664535)
                ·
                  rfl

theorem cell21_166212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 6].length) (baseStart_166212 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_166212 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_166212 prefixEnd_166212 := by exact prefixLift 166212
  have htrace : WordTrace (prefixWord ++ tailWord_166212) baseStart_166212 baseEnd_166212 := by
    simpa [prefixWord, tailWord_166212, baseEnd_166212] using wordTrace_append hprefix tailTrace_166212
  have hstable : (prefixWord ++ tailWord_166212).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166212).length < 2 ^ (prefixWord ++ tailWord_166212).sum := by decide
  have hdescent : baseEnd_166212 < baseStart_166212 := by decide
  rcases family_descends (prefixWord ++ tailWord_166212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166274 : List Nat := [3, 4, 2, 1, 2, 1, 3, 1, 4]
def baseStart_166274 : Nat := 118140960795 + 166274 * 2 ^ 59
def prefixEnd_166274 : Nat := 4983230072969 + 3 ^ 40 * 166274 * 2
def baseEnd_166274 : Nat := 37945992153683415960145

theorem tailTrace_166274 : CollatzResearch.WordTrace tailWord_166274 prefixEnd_166274 37945992153683415960145 := by
  unfold tailWord_166274
  simp only [CollatzResearch.WordTrace]
  refine ⟨1516127749906292545870469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4043007333083446788987917 1516127749906292545870469)
  ·
    refine ⟨284273953107429852350713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1516127749906292545870469 284273953107429852350713)
    ·
      refine ⟨213205464830572389263035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 284273953107429852350713 213205464830572389263035)
      ·
        refine ⟨319808197245858583894553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213205464830572389263035 319808197245858583894553)
        ·
          refine ⟨239856147934393937920915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 319808197245858583894553 239856147934393937920915)
          ·
            refine ⟨359784221901590906881373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239856147934393937920915 359784221901590906881373)
            ·
              refine ⟨134919083213096590080515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 359784221901590906881373 134919083213096590080515)
              ·
                refine ⟨202378624819644885120773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134919083213096590080515 202378624819644885120773)
                ·
                  refine ⟨37945992153683415960145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 202378624819644885120773 37945992153683415960145)
                  ·
                    rfl

theorem cell21_166274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_166274 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_166274 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_166274 prefixEnd_166274 := by exact prefixLift 166274
  have htrace : WordTrace (prefixWord ++ tailWord_166274) baseStart_166274 baseEnd_166274 := by
    simpa [prefixWord, tailWord_166274, baseEnd_166274] using wordTrace_append hprefix tailTrace_166274
  have hstable : (prefixWord ++ tailWord_166274).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166274).length < 2 ^ (prefixWord ++ tailWord_166274).sum := by decide
  have hdescent : baseEnd_166274 < baseStart_166274 := by decide
  rcases family_descends (prefixWord ++ tailWord_166274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166294 : List Nat := [5, 3, 1, 2, 2, 1, 1, 3, 3]
def baseStart_166294 : Nat := 118140960795 + 166294 * 2 ^ 59
def prefixEnd_166294 : Nat := 4983230072969 + 3 ^ 40 * 166294 * 2
def baseEnd_166294 : Nat := 37950556426167825626771

theorem tailTrace_166294 : CollatzResearch.WordTrace tailWord_166294 prefixEnd_166294 37950556426167825626771 := by
  unfold tailWord_166294
  simp only [CollatzResearch.WordTrace]
  refine ⟨379077528722044599950621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4043493639701809066139957 379077528722044599950621)
  ·
    refine ⟨142154073270766724981483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 379077528722044599950621 142154073270766724981483)
    ·
      refine ⟨213231109906150087472225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142154073270766724981483 213231109906150087472225)
      ·
        refine ⟨159923332429612565604169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213231109906150087472225 159923332429612565604169)
        ·
          refine ⟨119942499322209424203127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159923332429612565604169 119942499322209424203127)
          ·
            refine ⟨179913748983314136304691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119942499322209424203127 179913748983314136304691)
            ·
              refine ⟨269870623474971204457037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 179913748983314136304691 269870623474971204457037)
              ·
                refine ⟨101201483803114201671389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 269870623474971204457037 101201483803114201671389)
                ·
                  refine ⟨37950556426167825626771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 101201483803114201671389 37950556426167825626771)
                  ·
                    rfl

theorem cell21_166294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_166294 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_166294 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_166294 prefixEnd_166294 := by exact prefixLift 166294
  have htrace : WordTrace (prefixWord ++ tailWord_166294) baseStart_166294 baseEnd_166294 := by
    simpa [prefixWord, tailWord_166294, baseEnd_166294] using wordTrace_append hprefix tailTrace_166294
  have hstable : (prefixWord ++ tailWord_166294).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166294).length < 2 ^ (prefixWord ++ tailWord_166294).sum := by decide
  have hdescent : baseEnd_166294 < baseStart_166294 := by decide
  rcases family_descends (prefixWord ++ tailWord_166294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166375 : List Nat := [1, 1, 5, 2, 1, 1, 4, 2, 4]
def baseStart_166375 : Nat := 118140960795 + 166375 * 2 ^ 59
def prefixEnd_166375 : Nat := 4983230072969 + 3 ^ 40 * 166375 * 2
def baseEnd_166375 : Nat := 37969041729729684776605

theorem tailTrace_166375 : CollatzResearch.WordTrace tailWord_166375 prefixEnd_166375 37969041729729684776605 := by
  unfold tailWord_166375
  simp only [CollatzResearch.WordTrace]
  refine ⟨6068194772259264432908579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4045463181506176288605719 6068194772259264432908579)
  ·
    refine ⟨9102292158388896649362869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6068194772259264432908579 9102292158388896649362869)
    ·
      refine ⟨853339889848959060877769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9102292158388896649362869 853339889848959060877769)
      ·
        refine ⟨640004917386719295658327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 853339889848959060877769 640004917386719295658327)
        ·
          refine ⟨960007376080078943487491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 640004917386719295658327 960007376080078943487491)
          ·
            refine ⟨1440011064120118415231237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 960007376080078943487491 1440011064120118415231237)
            ·
              refine ⟨270002074522522202855857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1440011064120118415231237 270002074522522202855857)
              ·
                refine ⟨202501555891891652141893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 270002074522522202855857 202501555891891652141893)
                ·
                  refine ⟨37969041729729684776605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 202501555891891652141893 37969041729729684776605)
                  ·
                    rfl

theorem cell21_166375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 2, 4].length) (baseStart_166375 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_166375 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_166375 prefixEnd_166375 := by exact prefixLift 166375
  have htrace : WordTrace (prefixWord ++ tailWord_166375) baseStart_166375 baseEnd_166375 := by
    simpa [prefixWord, tailWord_166375, baseEnd_166375] using wordTrace_append hprefix tailTrace_166375
  have hstable : (prefixWord ++ tailWord_166375).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166375).length < 2 ^ (prefixWord ++ tailWord_166375).sum := by decide
  have hdescent : baseEnd_166375 < baseStart_166375 := by decide
  rcases family_descends (prefixWord ++ tailWord_166375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166378 : List Nat := [3, 1, 3, 1, 3, 1, 4, 2, 3]
def baseStart_166378 : Nat := 118140960795 + 166378 * 2 ^ 59
def prefixEnd_166378 : Nat := 4983230072969 + 3 ^ 40 * 166378 * 2
def baseEnd_166378 : Nat := 37969726370602346226599

theorem tailTrace_166378 : CollatzResearch.WordTrace tailWord_166378 prefixEnd_166378 37969726370602346226599 := by
  unfold tailWord_166378
  simp only [CollatzResearch.WordTrace]
  refine ⟨1517076047812098986316947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4045536127498930630178525 1517076047812098986316947)
  ·
    refine ⟨2275614071718148479475421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1517076047812098986316947 2275614071718148479475421)
    ·
      refine ⟨853355276894305679803283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2275614071718148479475421 853355276894305679803283)
      ·
        refine ⟨1280032915341458519704925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 853355276894305679803283 1280032915341458519704925)
        ·
          refine ⟨480012343253046944889347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1280032915341458519704925 480012343253046944889347)
          ·
            refine ⟨720018514879570417334021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 480012343253046944889347 720018514879570417334021)
            ·
              refine ⟨135003471539919453250129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 720018514879570417334021 135003471539919453250129)
              ·
                refine ⟨101252603654939589937597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 135003471539919453250129 101252603654939589937597)
                ·
                  refine ⟨37969726370602346226599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 101252603654939589937597 37969726370602346226599)
                  ·
                    rfl

theorem cell21_166378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 4, 2, 3].length) (baseStart_166378 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_166378 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_166378 prefixEnd_166378 := by exact prefixLift 166378
  have htrace : WordTrace (prefixWord ++ tailWord_166378) baseStart_166378 baseEnd_166378 := by
    simpa [prefixWord, tailWord_166378, baseEnd_166378] using wordTrace_append hprefix tailTrace_166378
  have hstable : (prefixWord ++ tailWord_166378).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166378).length < 2 ^ (prefixWord ++ tailWord_166378).sum := by decide
  have hdescent : baseEnd_166378 < baseStart_166378 := by decide
  rcases family_descends (prefixWord ++ tailWord_166378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166403 : List Nat := [1, 1, 1, 3, 2, 1, 5, 2, 5]
def baseStart_166403 : Nat := 118140960795 + 166403 * 2 ^ 59
def prefixEnd_166403 : Nat := 4983230072969 + 3 ^ 40 * 166403 * 2
def baseEnd_166403 : Nat := 37975431711207858309881

theorem tailTrace_166403 : CollatzResearch.WordTrace tailWord_166403 prefixEnd_166403 37975431711207858309881 := by
  unfold tailWord_166403
  simp only [CollatzResearch.WordTrace]
  refine ⟨6069216016157825214927863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4046144010771883476618575 6069216016157825214927863)
  ·
    refine ⟨9103824024236737822391795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6069216016157825214927863 9103824024236737822391795)
    ·
      refine ⟨13655736036355106733587693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9103824024236737822391795 13655736036355106733587693)
      ·
        refine ⟨5120901013633165025095385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13655736036355106733587693 5120901013633165025095385)
        ·
          refine ⟨3840675760224873768821539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5120901013633165025095385 3840675760224873768821539)
          ·
            refine ⟨5761013640337310653232309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3840675760224873768821539 5761013640337310653232309)
            ·
              refine ⟨540095028781622873740529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5761013640337310653232309 540095028781622873740529)
              ·
                refine ⟨405071271586217155305397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 540095028781622873740529 405071271586217155305397)
                ·
                  refine ⟨37975431711207858309881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 405071271586217155305397 37975431711207858309881)
                  ·
                    rfl

theorem cell21_166403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 2, 5].length) (baseStart_166403 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_166403 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_166403 prefixEnd_166403 := by exact prefixLift 166403
  have htrace : WordTrace (prefixWord ++ tailWord_166403) baseStart_166403 baseEnd_166403 := by
    simpa [prefixWord, tailWord_166403, baseEnd_166403] using wordTrace_append hprefix tailTrace_166403
  have hstable : (prefixWord ++ tailWord_166403).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166403).length < 2 ^ (prefixWord ++ tailWord_166403).sum := by decide
  have hdescent : baseEnd_166403 < baseStart_166403 := by decide
  rcases family_descends (prefixWord ++ tailWord_166403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166451 : List Nat := [1, 1, 1, 2, 4, 2, 5, 1, 4]
def baseStart_166451 : Nat := 118140960795 + 166451 * 2 ^ 59
def prefixEnd_166451 : Nat := 4983230072969 + 3 ^ 40 * 166451 * 2
def baseEnd_166451 : Nat := 37986385965170441509783

theorem tailTrace_166451 : CollatzResearch.WordTrace tailWord_166451 prefixEnd_166451 37986385965170441509783 := by
  unfold tailWord_166451
  simp only [CollatzResearch.WordTrace]
  refine ⟨6070966719983929412675207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4047311146655952941783471 6070966719983929412675207)
  ·
    refine ⟨9106450079975894119012811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6070966719983929412675207 9106450079975894119012811)
    ·
      refine ⟨13659675119963841178519217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9106450079975894119012811 13659675119963841178519217)
      ·
        refine ⟨10244756339972880883889413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13659675119963841178519217 10244756339972880883889413)
        ·
          refine ⟨1920891813744915165729265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10244756339972880883889413 1920891813744915165729265)
          ·
            refine ⟨1440668860308686374296949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1920891813744915165729265 1440668860308686374296949)
            ·
              refine ⟨135062705653939347590339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1440668860308686374296949 135062705653939347590339)
              ·
                refine ⟨202594058480909021385509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 135062705653939347590339 202594058480909021385509)
                ·
                  refine ⟨37986385965170441509783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 202594058480909021385509 37986385965170441509783)
                  ·
                    rfl

theorem cell21_166451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 5, 1, 4].length) (baseStart_166451 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_166451 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_166451 prefixEnd_166451 := by exact prefixLift 166451
  have htrace : WordTrace (prefixWord ++ tailWord_166451) baseStart_166451 baseEnd_166451 := by
    simpa [prefixWord, tailWord_166451, baseEnd_166451] using wordTrace_append hprefix tailTrace_166451
  have hstable : (prefixWord ++ tailWord_166451).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166451).length < 2 ^ (prefixWord ++ tailWord_166451).sum := by decide
  have hdescent : baseEnd_166451 < baseStart_166451 := by decide
  rcases family_descends (prefixWord ++ tailWord_166451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166465 : List Nat := [1, 2, 5, 1, 1, 3, 1, 7]
def baseStart_166465 : Nat := 118140960795 + 166465 * 2 ^ 59
def prefixEnd_166465 : Nat := 4983230072969 + 3 ^ 40 * 166465 * 2
def baseEnd_166465 : Nat := 12663193651969842758807

theorem tailTrace_166465 : CollatzResearch.WordTrace tailWord_166465 prefixEnd_166465 12663193651969842758807 := by
  unfold tailWord_166465
  simp only [CollatzResearch.WordTrace]
  refine ⟨6071477341933209803684849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4047651561288806535789899 6071477341933209803684849)
  ·
    refine ⟨4553608006449907352763637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6071477341933209803684849 4553608006449907352763637)
    ·
      refine ⟨426900750604678814321591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4553608006449907352763637 426900750604678814321591)
      ·
        refine ⟨640351125907018221482387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 426900750604678814321591 640351125907018221482387)
        ·
          refine ⟨960526688860527332223581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 640351125907018221482387 960526688860527332223581)
          ·
            refine ⟨360197508322697749583843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 960526688860527332223581 360197508322697749583843)
            ·
              refine ⟨540296262484046624375765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 360197508322697749583843 540296262484046624375765)
              ·
                refine ⟨12663193651969842758807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 540296262484046624375765 12663193651969842758807)
                ·
                  rfl

theorem cell21_166465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 7].length) (baseStart_166465 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_166465 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_166465 prefixEnd_166465 := by exact prefixLift 166465
  have htrace : WordTrace (prefixWord ++ tailWord_166465) baseStart_166465 baseEnd_166465 := by
    simpa [prefixWord, tailWord_166465, baseEnd_166465] using wordTrace_append hprefix tailTrace_166465
  have hstable : (prefixWord ++ tailWord_166465).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166465).length < 2 ^ (prefixWord ++ tailWord_166465).sum := by decide
  have hdescent : baseEnd_166465 < baseStart_166465 := by decide
  rcases family_descends (prefixWord ++ tailWord_166465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166496 : List Nat := [2, 1, 1, 3, 2, 1, 2, 6, 3]
def baseStart_166496 : Nat := 118140960795 + 166496 * 2 ^ 59
def prefixEnd_166496 : Nat := 4983230072969 + 3 ^ 40 * 166496 * 2
def baseEnd_166496 : Nat := 37996655578260363259691

theorem tailTrace_166496 : CollatzResearch.WordTrace tailWord_166496 prefixEnd_166496 37996655578260363259691 := by
  unfold tailWord_166496
  simp only [CollatzResearch.WordTrace]
  refine ⟨3036304002410451049031671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4048405336547268065375561 3036304002410451049031671)
  ·
    refine ⟨4554456003615676573547507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3036304002410451049031671 4554456003615676573547507)
    ·
      refine ⟨6831684005423514860321261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4554456003615676573547507 6831684005423514860321261)
      ·
        refine ⟨2561881502033818072620473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6831684005423514860321261 2561881502033818072620473)
        ·
          refine ⟨1921411126525363554465355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2561881502033818072620473 1921411126525363554465355)
          ·
            refine ⟨2882116689788045331698033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1921411126525363554465355 2882116689788045331698033)
            ·
              refine ⟨2161587517341033998773525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2882116689788045331698033 2161587517341033998773525)
              ·
                refine ⟨101324414875360968692509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2161587517341033998773525 101324414875360968692509)
                ·
                  refine ⟨37996655578260363259691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 101324414875360968692509 37996655578260363259691)
                  ·
                    rfl

theorem cell21_166496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 6, 3].length) (baseStart_166496 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_166496 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_166496 prefixEnd_166496 := by exact prefixLift 166496
  have htrace : WordTrace (prefixWord ++ tailWord_166496) baseStart_166496 baseEnd_166496 := by
    simpa [prefixWord, tailWord_166496, baseEnd_166496] using wordTrace_append hprefix tailTrace_166496
  have hstable : (prefixWord ++ tailWord_166496).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166496).length < 2 ^ (prefixWord ++ tailWord_166496).sum := by decide
  have hdescent : baseEnd_166496 < baseStart_166496 := by decide
  rcases family_descends (prefixWord ++ tailWord_166496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166524 : List Nat := [2, 2, 2, 1, 1, 2, 4, 7]
def baseStart_166524 : Nat := 118140960795 + 166524 * 2 ^ 59
def prefixEnd_166524 : Nat := 4983230072969 + 3 ^ 40 * 166524 * 2
def baseEnd_166524 : Nat := 12667681853246178930989

theorem tailTrace_166524 : CollatzResearch.WordTrace tailWord_166524 prefixEnd_166524 12667681853246178930989 := by
  unfold tailWord_166524
  simp only [CollatzResearch.WordTrace]
  refine ⟨3036814624359731440041313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4049086165812975253388417 3036814624359731440041313)
  ·
    refine ⟨2277610968269798580030985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3036814624359731440041313 2277610968269798580030985)
    ·
      refine ⟨1708208226202348935023239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2277610968269798580030985 1708208226202348935023239)
      ·
        refine ⟨2562312339303523402534859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1708208226202348935023239 2562312339303523402534859)
        ·
          refine ⟨3843468508955285103802289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2562312339303523402534859 3843468508955285103802289)
          ·
            refine ⟨2882601381716463827851717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3843468508955285103802289 2882601381716463827851717)
            ·
              refine ⟨540487759071836967722197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2882601381716463827851717 540487759071836967722197)
              ·
                refine ⟨12667681853246178930989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 540487759071836967722197 12667681853246178930989)
                ·
                  rfl

theorem cell21_166524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 7].length) (baseStart_166524 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_166524 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_166524 prefixEnd_166524 := by exact prefixLift 166524
  have htrace : WordTrace (prefixWord ++ tailWord_166524) baseStart_166524 baseEnd_166524 := by
    simpa [prefixWord, tailWord_166524, baseEnd_166524] using wordTrace_append hprefix tailTrace_166524
  have hstable : (prefixWord ++ tailWord_166524).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166524).length < 2 ^ (prefixWord ++ tailWord_166524).sum := by decide
  have hdescent : baseEnd_166524 < baseStart_166524 := by decide
  rcases family_descends (prefixWord ++ tailWord_166524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166589 : List Nat := [1, 4, 1, 2, 1, 4, 2, 3, 3]
def baseStart_166589 : Nat := 118140960795 + 166589 * 2 ^ 59
def prefixEnd_166589 : Nat := 4983230072969 + 3 ^ 40 * 166589 * 2
def baseEnd_166589 : Nat := 38017879445312868209501

theorem tailTrace_166589 : CollatzResearch.WordTrace tailWord_166589 prefixEnd_166589 38017879445312868209501 := by
  unfold tailWord_166589
  simp only [CollatzResearch.WordTrace]
  refine ⟨6075999993483978981198821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4050666662322652654132547 6075999993483978981198821)
  ·
    refine ⟨1139249998778246058974779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6075999993483978981198821 1139249998778246058974779)
    ·
      refine ⟨1708874998167369088462169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1139249998778246058974779 1708874998167369088462169)
      ·
        refine ⟨1281656248625526816346627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1708874998167369088462169 1281656248625526816346627)
        ·
          refine ⟨1922484372938290224519941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1281656248625526816346627 1922484372938290224519941)
          ·
            refine ⟨360465819925929417097489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1922484372938290224519941 360465819925929417097489)
            ·
              refine ⟨270349364944447062823117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 360465819925929417097489 270349364944447062823117)
              ·
                refine ⟨101381011854167648558669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 270349364944447062823117 101381011854167648558669)
                ·
                  refine ⟨38017879445312868209501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 101381011854167648558669 38017879445312868209501)
                  ·
                    rfl

theorem cell21_166589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 3, 3].length) (baseStart_166589 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_166589 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_166589 prefixEnd_166589 := by exact prefixLift 166589
  have htrace : WordTrace (prefixWord ++ tailWord_166589) baseStart_166589 baseEnd_166589 := by
    simpa [prefixWord, tailWord_166589, baseEnd_166589] using wordTrace_append hprefix tailTrace_166589
  have hstable : (prefixWord ++ tailWord_166589).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166589).length < 2 ^ (prefixWord ++ tailWord_166589).sum := by decide
  have hdescent : baseEnd_166589 < baseStart_166589 := by decide
  rcases family_descends (prefixWord ++ tailWord_166589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166600 : List Nat := [2, 1, 3, 1, 2, 4, 8]
def baseStart_166600 : Nat := 118140960795 + 166600 * 2 ^ 59
def prefixEnd_166600 : Nat := 4983230072969 + 3 ^ 40 * 166600 * 2
def baseEnd_166600 : Nat := 4224487755019921502905

theorem tailTrace_166600 : CollatzResearch.WordTrace tailWord_166600 prefixEnd_166600 4224487755019921502905 := by
  unfold tailWord_166600
  simp only [CollatzResearch.WordTrace]
  refine ⟨3038200598222063929924627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4050934130962751906566169 3038200598222063929924627)
  ·
    refine ⟨4557300897333095894886941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3038200598222063929924627 4557300897333095894886941)
    ·
      refine ⟨1708987836499910960582603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4557300897333095894886941 1708987836499910960582603)
      ·
        refine ⟨2563481754749866440873905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1708987836499910960582603 2563481754749866440873905)
        ·
          refine ⟨1922611316062399830655429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2563481754749866440873905 1922611316062399830655429)
          ·
            refine ⟨360489621761699968247893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1922611316062399830655429 360489621761699968247893)
            ·
              refine ⟨4224487755019921502905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 360489621761699968247893 4224487755019921502905)
              ·
                rfl

theorem cell21_166600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 8].length) (baseStart_166600 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_166600 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_166600 prefixEnd_166600 := by exact prefixLift 166600
  have htrace : WordTrace (prefixWord ++ tailWord_166600) baseStart_166600 baseEnd_166600 := by
    simpa [prefixWord, tailWord_166600, baseEnd_166600] using wordTrace_append hprefix tailTrace_166600
  have hstable : (prefixWord ++ tailWord_166600).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166600).length < 2 ^ (prefixWord ++ tailWord_166600).sum := by decide
  have hdescent : baseEnd_166600 < baseStart_166600 := by decide
  rcases family_descends (prefixWord ++ tailWord_166600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166679 : List Nat := [1, 1, 3, 4, 3, 1, 1, 3, 4]
def baseStart_166679 : Nat := 118140960795 + 166679 * 2 ^ 59
def prefixEnd_166679 : Nat := 4983230072969 + 3 ^ 40 * 166679 * 2
def baseEnd_166679 : Nat := 38038418671492711709317

theorem tailTrace_166679 : CollatzResearch.WordTrace tailWord_166679 prefixEnd_166679 38038418671492711709317 := by
  unfold tailWord_166679
  simp only [CollatzResearch.WordTrace]
  refine ⟨6079282563157924351975091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4052855042105282901316727 6079282563157924351975091)
  ·
    refine ⟨9118923844736886527962637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6079282563157924351975091 9118923844736886527962637)
    ·
      refine ⟨3419596441776332447985989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9118923844736886527962637 3419596441776332447985989)
      ·
        refine ⟨641174332833062333997373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3419596441776332447985989 641174332833062333997373)
        ·
          refine ⟨240440374812398375249015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 641174332833062333997373 240440374812398375249015)
          ·
            refine ⟨360660562218597562873523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240440374812398375249015 360660562218597562873523)
            ·
              refine ⟨540990843327896344310285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 360660562218597562873523 540990843327896344310285)
              ·
                refine ⟨202871566247961129116357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 540990843327896344310285 202871566247961129116357)
                ·
                  refine ⟨38038418671492711709317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 202871566247961129116357 38038418671492711709317)
                  ·
                    rfl

theorem cell21_166679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 3, 4].length) (baseStart_166679 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_166679 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_166679 prefixEnd_166679 := by exact prefixLift 166679
  have htrace : WordTrace (prefixWord ++ tailWord_166679) baseStart_166679 baseEnd_166679 := by
    simpa [prefixWord, tailWord_166679, baseEnd_166679] using wordTrace_append hprefix tailTrace_166679
  have hstable : (prefixWord ++ tailWord_166679).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166679).length < 2 ^ (prefixWord ++ tailWord_166679).sum := by decide
  have hdescent : baseEnd_166679 < baseStart_166679 := by decide
  rcases family_descends (prefixWord ++ tailWord_166679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166710 : List Nat := [5, 1, 2, 2, 3, 8]
def baseStart_166710 : Nat := 118140960795 + 166710 * 2 ^ 59
def prefixEnd_166710 : Nat := 4983230072969 + 3 ^ 40 * 166710 * 2
def baseEnd_166710 : Nat := 1409092344216427655281

theorem tailTrace_166710 : CollatzResearch.WordTrace tailWord_166710 prefixEnd_166710 1409092344216427655281 := by
  unfold tailWord_166710
  simp only [CollatzResearch.WordTrace]
  refine ⟨380025826627851040397099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4053608817363744430902389 380025826627851040397099)
  ·
    refine ⟨570038739941776560595649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 380025826627851040397099 570038739941776560595649)
    ·
      refine ⟨427529054956332420446737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 570038739941776560595649 427529054956332420446737)
      ·
        refine ⟨320646791217249315335053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 427529054956332420446737 320646791217249315335053)
        ·
          refine ⟨120242546706468493250645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 320646791217249315335053 120242546706468493250645)
          ·
            refine ⟨1409092344216427655281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 120242546706468493250645 1409092344216427655281)
            ·
              rfl

theorem cell21_166710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 8].length) (baseStart_166710 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_166710 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_166710 prefixEnd_166710 := by exact prefixLift 166710
  have htrace : WordTrace (prefixWord ++ tailWord_166710) baseStart_166710 baseEnd_166710 := by
    simpa [prefixWord, tailWord_166710, baseEnd_166710] using wordTrace_append hprefix tailTrace_166710
  have hstable : (prefixWord ++ tailWord_166710).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166710).length < 2 ^ (prefixWord ++ tailWord_166710).sum := by decide
  have hdescent : baseEnd_166710 < baseStart_166710 := by decide
  rcases family_descends (prefixWord ++ tailWord_166710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166738 : List Nat := [3, 2, 2, 1, 1, 2, 1, 5, 4]
def baseStart_166738 : Nat := 118140960795 + 166738 * 2 ^ 59
def prefixEnd_166738 : Nat := 4983230072969 + 3 ^ 40 * 166738 * 2
def baseEnd_166738 : Nat := 38051883275321720225863

theorem tailTrace_166738 : CollatzResearch.WordTrace tailWord_166738 prefixEnd_166738 38051883275321720225863 := by
  unfold tailWord_166738
  simp only [CollatzResearch.WordTrace]
  refine ⟨1520358617486044357093217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4054289646629451618915245 1520358617486044357093217)
  ·
    refine ⟨1140268963114533267819913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1520358617486044357093217 1140268963114533267819913)
    ·
      refine ⟨855201722335899950864935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1140268963114533267819913 855201722335899950864935)
      ·
        refine ⟨1282802583503849926297403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 855201722335899950864935 1282802583503849926297403)
        ·
          refine ⟨1924203875255774889446105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1282802583503849926297403 1924203875255774889446105)
          ·
            refine ⟨1443152906441831167084579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1924203875255774889446105 1443152906441831167084579)
            ·
              refine ⟨2164729359662746750626869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1443152906441831167084579 2164729359662746750626869)
              ·
                refine ⟨202943377468382507871269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2164729359662746750626869 202943377468382507871269)
                ·
                  refine ⟨38051883275321720225863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 202943377468382507871269 38051883275321720225863)
                  ·
                    rfl

theorem cell21_166738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 5, 4].length) (baseStart_166738 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_166738 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_166738 prefixEnd_166738 := by exact prefixLift 166738
  have htrace : WordTrace (prefixWord ++ tailWord_166738) baseStart_166738 baseEnd_166738 := by
    simpa [prefixWord, tailWord_166738, baseEnd_166738] using wordTrace_append hprefix tailTrace_166738
  have hstable : (prefixWord ++ tailWord_166738).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166738).length < 2 ^ (prefixWord ++ tailWord_166738).sum := by decide
  have hdescent : baseEnd_166738 < baseStart_166738 := by decide
  rcases family_descends (prefixWord ++ tailWord_166738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166817 : List Nat := [1, 2, 3, 4, 1, 1, 3, 3, 3]
def baseStart_166817 : Nat := 118140960795 + 166817 * 2 ^ 59
def prefixEnd_166817 : Nat := 4983230072969 + 3 ^ 40 * 166817 * 2
def baseEnd_166817 : Nat := 38069912151635138409035

theorem tailTrace_166817 : CollatzResearch.WordTrace tailWord_166817 prefixEnd_166817 38069912151635138409035 := by
  unfold tailWord_166817
  simp only [CollatzResearch.WordTrace]
  refine ⟨6084315836657973920498705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4056210557771982613665803 6084315836657973920498705)
  ·
    refine ⟨4563236877493480440374029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6084315836657973920498705 4563236877493480440374029)
    ·
      refine ⟨1711213829060055165140261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4563236877493480440374029 1711213829060055165140261)
      ·
        refine ⟨320852592948760343463799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1711213829060055165140261 320852592948760343463799)
        ·
          refine ⟨481278889423140515195699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 320852592948760343463799 481278889423140515195699)
          ·
            refine ⟨721918334134710772793549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 481278889423140515195699 721918334134710772793549)
            ·
              refine ⟨270719375300516539797581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 721918334134710772793549 270719375300516539797581)
              ·
                refine ⟨101519765737693702424093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 270719375300516539797581 101519765737693702424093)
                ·
                  refine ⟨38069912151635138409035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 101519765737693702424093 38069912151635138409035)
                  ·
                    rfl

theorem cell21_166817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 3, 3].length) (baseStart_166817 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_166817 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_166817 prefixEnd_166817 := by exact prefixLift 166817
  have htrace : WordTrace (prefixWord ++ tailWord_166817) baseStart_166817 baseEnd_166817 := by
    simpa [prefixWord, tailWord_166817, baseEnd_166817] using wordTrace_append hprefix tailTrace_166817
  have hstable : (prefixWord ++ tailWord_166817).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166817).length < 2 ^ (prefixWord ++ tailWord_166817).sum := by decide
  have hdescent : baseEnd_166817 < baseStart_166817 := by decide
  rcases family_descends (prefixWord ++ tailWord_166817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166845 : List Nat := [1, 4, 1, 2, 4, 1, 2, 6]
def baseStart_166845 : Nat := 118140960795 + 166845 * 2 ^ 59
def prefixEnd_166845 : Nat := 4983230072969 + 3 ^ 40 * 166845 * 2
def baseEnd_166845 : Nat := 12692100711037770647437

theorem tailTrace_166845 : CollatzResearch.WordTrace tailWord_166845 prefixEnd_166845 12692100711037770647437 := by
  unfold tailWord_166845
  simp only [CollatzResearch.WordTrace]
  refine ⟨6085337080556534702517989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4056891387037689801678659 6085337080556534702517989)
  ·
    refine ⟨1141000702604350256722123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6085337080556534702517989 1141000702604350256722123)
    ·
      refine ⟨1711501053906525385083185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1141000702604350256722123 1711501053906525385083185)
      ·
        refine ⟨1283625790429894038812389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1711501053906525385083185 1283625790429894038812389)
        ·
          refine ⟨240679835705605132277323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1283625790429894038812389 240679835705605132277323)
          ·
            refine ⟨361019753558407698415985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240679835705605132277323 361019753558407698415985)
            ·
              refine ⟨270764815168805773811989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 361019753558407698415985 270764815168805773811989)
              ·
                refine ⟨12692100711037770647437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 270764815168805773811989 12692100711037770647437)
                ·
                  rfl

theorem cell21_166845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 6].length) (baseStart_166845 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_166845 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_166845 prefixEnd_166845 := by exact prefixLift 166845
  have htrace : WordTrace (prefixWord ++ tailWord_166845) baseStart_166845 baseEnd_166845 := by
    simpa [prefixWord, tailWord_166845, baseEnd_166845] using wordTrace_append hprefix tailTrace_166845
  have hstable : (prefixWord ++ tailWord_166845).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166845).length < 2 ^ (prefixWord ++ tailWord_166845).sum := by decide
  have hdescent : baseEnd_166845 < baseStart_166845 := by decide
  rcases family_descends (prefixWord ++ tailWord_166845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166890 : List Nat := [3, 1, 3, 1, 2, 2, 1, 4, 4]
def baseStart_166890 : Nat := 118140960795 + 166890 * 2 ^ 59
def prefixEnd_166890 : Nat := 4983230072969 + 3 ^ 40 * 166890 * 2
def baseEnd_166890 : Nat := 38086571746203233692219

theorem tailTrace_166890 : CollatzResearch.WordTrace tailWord_166890 prefixEnd_166890 38086571746203233692219 := by
  unfold tailWord_166890
  simp only [CollatzResearch.WordTrace]
  refine ⟨1521744591348376846976531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4057985576929004925270749 1521744591348376846976531)
  ·
    refine ⟨2282616887022565270464797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1521744591348376846976531 2282616887022565270464797)
    ·
      refine ⟨855981332633461976424299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2282616887022565270464797 855981332633461976424299)
      ·
        refine ⟨1283971998950192964636449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 855981332633461976424299 1283971998950192964636449)
        ·
          refine ⟨962978999212644723477337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1283971998950192964636449 962978999212644723477337)
          ·
            refine ⟨722234249409483542608003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 962978999212644723477337 722234249409483542608003)
            ·
              refine ⟨1083351374114225313912005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 722234249409483542608003 1083351374114225313912005)
              ·
                refine ⟨203128382646417246358501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1083351374114225313912005 203128382646417246358501)
                ·
                  refine ⟨38086571746203233692219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 203128382646417246358501 38086571746203233692219)
                  ·
                    rfl

theorem cell21_166890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 4, 4].length) (baseStart_166890 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_166890 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_166890 prefixEnd_166890 := by exact prefixLift 166890
  have htrace : WordTrace (prefixWord ++ tailWord_166890) baseStart_166890 baseEnd_166890 := by
    simpa [prefixWord, tailWord_166890, baseEnd_166890] using wordTrace_append hprefix tailTrace_166890
  have hstable : (prefixWord ++ tailWord_166890).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166890).length < 2 ^ (prefixWord ++ tailWord_166890).sum := by decide
  have hdescent : baseEnd_166890 < baseStart_166890 := by decide
  rcases family_descends (prefixWord ++ tailWord_166890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166949 : List Nat := [1, 3, 1, 2, 2, 2, 3, 1, 6]
def baseStart_166949 : Nat := 118140960795 + 166949 * 2 ^ 59
def prefixEnd_166949 : Nat := 4983230072969 + 3 ^ 40 * 166949 * 2
def baseEnd_166949 : Nat := 38100036350032242208765

theorem tailTrace_166949 : CollatzResearch.WordTrace tailWord_166949 prefixEnd_166949 38100036350032242208765 := by
  unfold tailWord_166949
  simp only [CollatzResearch.WordTrace]
  refine ⟨6089130272179760464303901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4059420181453173642869267 6089130272179760464303901)
  ·
    refine ⟨2283423852067410174113963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6089130272179760464303901 2283423852067410174113963)
    ·
      refine ⟨3425135778101115261170945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2283423852067410174113963 3425135778101115261170945)
      ·
        refine ⟨2568851833575836445878209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3425135778101115261170945 2568851833575836445878209)
        ·
          refine ⟨1926638875181877334408657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2568851833575836445878209 1926638875181877334408657)
          ·
            refine ⟨1444979156386408000806493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1926638875181877334408657 1444979156386408000806493)
            ·
              refine ⟨541867183644903000302435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1444979156386408000806493 541867183644903000302435)
              ·
                refine ⟨812800775467354500453653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 541867183644903000302435 812800775467354500453653)
                ·
                  refine ⟨38100036350032242208765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 812800775467354500453653 38100036350032242208765)
                  ·
                    rfl

theorem cell21_166949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 1, 6].length) (baseStart_166949 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_166949 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_166949 prefixEnd_166949 := by exact prefixLift 166949
  have htrace : WordTrace (prefixWord ++ tailWord_166949) baseStart_166949 baseEnd_166949 := by
    simpa [prefixWord, tailWord_166949, baseEnd_166949] using wordTrace_append hprefix tailTrace_166949
  have hstable : (prefixWord ++ tailWord_166949).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166949).length < 2 ^ (prefixWord ++ tailWord_166949).sum := by decide
  have hdescent : baseEnd_166949 < baseStart_166949 := by decide
  rcases family_descends (prefixWord ++ tailWord_166949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166963 : List Nat := [1, 1, 1, 2, 4, 1, 1, 10]
def baseStart_166963 : Nat := 118140960795 + 166963 * 2 ^ 59
def prefixEnd_166963 : Nat := 4983230072969 + 3 ^ 40 * 166963 * 2
def baseEnd_166963 : Nat := 12701077113590442991801

theorem tailTrace_166963 : CollatzResearch.WordTrace tailWord_166963 prefixEnd_166963 12701077113590442991801 := by
  unfold tailWord_166963
  simp only [CollatzResearch.WordTrace]
  refine ⟨6089640894129040855313543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4059760596086027236875695 6089640894129040855313543)
  ·
    refine ⟨9134461341193561282970315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6089640894129040855313543 9134461341193561282970315)
    ·
      refine ⟨13701692011790341924455473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9134461341193561282970315 13701692011790341924455473)
      ·
        refine ⟨10276269008842756443341605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13701692011790341924455473 10276269008842756443341605)
        ·
          refine ⟨1926800439158016833126551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10276269008842756443341605 1926800439158016833126551)
          ·
            refine ⟨2890200658737025249689827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1926800439158016833126551 2890200658737025249689827)
            ·
              refine ⟨4335300988105537874534741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2890200658737025249689827 4335300988105537874534741)
              ·
                refine ⟨12701077113590442991801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 4335300988105537874534741 12701077113590442991801)
                ·
                  rfl

theorem cell21_166963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 10].length) (baseStart_166963 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_166963 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_166963 prefixEnd_166963 := by exact prefixLift 166963
  have htrace : WordTrace (prefixWord ++ tailWord_166963) baseStart_166963 baseEnd_166963 := by
    simpa [prefixWord, tailWord_166963, baseEnd_166963] using wordTrace_append hprefix tailTrace_166963
  have hstable : (prefixWord ++ tailWord_166963).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166963).length < 2 ^ (prefixWord ++ tailWord_166963).sum := by decide
  have hdescent : baseEnd_166963 < baseStart_166963 := by decide
  rcases family_descends (prefixWord ++ tailWord_166963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167110 : List Nat := [6, 1, 2, 2, 1, 2, 1, 2, 4]
def baseStart_167110 : Nat := 118140960795 + 167110 * 2 ^ 59
def prefixEnd_167110 : Nat := 4983230072969 + 3 ^ 40 * 167110 * 2
def baseEnd_167110 : Nat := 38136778743531740025103

theorem tailTrace_167110 : CollatzResearch.WordTrace tailWord_167110 prefixEnd_167110 38136778743531740025103 := by
  unfold tailWord_167110
  simp only [CollatzResearch.WordTrace]
  refine ⟨190468825768640155028587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 4063334949730989973943189 190468825768640155028587)
  ·
    refine ⟨285703238652960232542881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190468825768640155028587 285703238652960232542881)
    ·
      refine ⟨214277428989720174407161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 285703238652960232542881 214277428989720174407161)
      ·
        refine ⟨160708071742290130805371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 214277428989720174407161 160708071742290130805371)
        ·
          refine ⟨241062107613435196208057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160708071742290130805371 241062107613435196208057)
          ·
            refine ⟨180796580710076397156043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 241062107613435196208057 180796580710076397156043)
            ·
              refine ⟨271194871065114595734065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 180796580710076397156043 271194871065114595734065)
              ·
                refine ⟨203396153298835946800549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 271194871065114595734065 203396153298835946800549)
                ·
                  refine ⟨38136778743531740025103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 203396153298835946800549 38136778743531740025103)
                  ·
                    rfl

theorem cell21_167110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_167110 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_167110 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_167110 prefixEnd_167110 := by exact prefixLift 167110
  have htrace : WordTrace (prefixWord ++ tailWord_167110) baseStart_167110 baseEnd_167110 := by
    simpa [prefixWord, tailWord_167110, baseEnd_167110] using wordTrace_append hprefix tailTrace_167110
  have hstable : (prefixWord ++ tailWord_167110).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167110).length < 2 ^ (prefixWord ++ tailWord_167110).sum := by decide
  have hdescent : baseEnd_167110 < baseStart_167110 := by decide
  rcases family_descends (prefixWord ++ tailWord_167110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167118 : List Nat := [4, 1, 1, 1, 5, 1, 1, 1, 6]
def baseStart_167118 : Nat := 118140960795 + 167118 * 2 ^ 59
def prefixEnd_167118 : Nat := 4983230072969 + 3 ^ 40 * 167118 * 2
def baseEnd_167118 : Nat := 38138604452525503891753

theorem tailTrace_167118 : CollatzResearch.WordTrace tailWord_167118 prefixEnd_167118 38138604452525503891753 := by
  unfold tailWord_167118
  simp only [CollatzResearch.WordTrace]
  refine ⟨761911776070937790900751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4063529472378334884804005 761911776070937790900751)
  ·
    refine ⟨1142867664106406686351127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 761911776070937790900751 1142867664106406686351127)
    ·
      refine ⟨1714301496159610029526691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1142867664106406686351127 1714301496159610029526691)
      ·
        refine ⟨2571452244239415044290037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1714301496159610029526691 2571452244239415044290037)
        ·
          refine ⟨241073647897445160402191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2571452244239415044290037 241073647897445160402191)
          ·
            refine ⟨361610471846167740603287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241073647897445160402191 361610471846167740603287)
            ·
              refine ⟨542415707769251610904931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 361610471846167740603287 542415707769251610904931)
              ·
                refine ⟨813623561653877416357397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 542415707769251610904931 813623561653877416357397)
                ·
                  refine ⟨38138604452525503891753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 813623561653877416357397 38138604452525503891753)
                  ·
                    rfl

theorem cell21_167118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 1, 6].length) (baseStart_167118 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_167118 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_167118 prefixEnd_167118 := by exact prefixLift 167118
  have htrace : WordTrace (prefixWord ++ tailWord_167118) baseStart_167118 baseEnd_167118 := by
    simpa [prefixWord, tailWord_167118, baseEnd_167118] using wordTrace_append hprefix tailTrace_167118
  have hstable : (prefixWord ++ tailWord_167118).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167118).length < 2 ^ (prefixWord ++ tailWord_167118).sum := by decide
  have hdescent : baseEnd_167118 < baseStart_167118 := by decide
  rcases family_descends (prefixWord ++ tailWord_167118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167149 : List Nat := [1, 5, 1, 2, 2, 1, 4, 5]
def baseStart_167149 : Nat := 118140960795 + 167149 * 2 ^ 59
def prefixEnd_167149 : Nat := 4983230072969 + 3 ^ 40 * 167149 * 2
def baseEnd_167149 : Nat := 12715226358292112958341

theorem tailTrace_167149 : CollatzResearch.WordTrace tailWord_167149 prefixEnd_167149 12715226358292112958341 := by
  unfold tailWord_167149
  simp only [CollatzResearch.WordTrace]
  refine ⟨6096424871455194621584501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4064283247636796414389667 6096424871455194621584501)
  ·
    refine ⟨571539831698924495773547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6096424871455194621584501 571539831698924495773547)
    ·
      refine ⟨857309747548386743660321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 571539831698924495773547 857309747548386743660321)
      ·
        refine ⟨642982310661290057745241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 857309747548386743660321 642982310661290057745241)
        ·
          refine ⟨482236732995967543308931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 642982310661290057745241 482236732995967543308931)
          ·
            refine ⟨723355099493951314963397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 482236732995967543308931 723355099493951314963397)
            ·
              refine ⟨135629081155115871555637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 723355099493951314963397 135629081155115871555637)
              ·
                refine ⟨12715226358292112958341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 135629081155115871555637 12715226358292112958341)
                ·
                  rfl

theorem cell21_167149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 4, 5].length) (baseStart_167149 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_167149 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_167149 prefixEnd_167149 := by exact prefixLift 167149
  have htrace : WordTrace (prefixWord ++ tailWord_167149) baseStart_167149 baseEnd_167149 := by
    simpa [prefixWord, tailWord_167149, baseEnd_167149] using wordTrace_append hprefix tailTrace_167149
  have hstable : (prefixWord ++ tailWord_167149).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167149).length < 2 ^ (prefixWord ++ tailWord_167149).sum := by decide
  have hdescent : baseEnd_167149 < baseStart_167149 := by decide
  rcases family_descends (prefixWord ++ tailWord_167149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167177 : List Nat := [1, 2, 1, 1, 3, 3, 2, 4, 4]
def baseStart_167177 : Nat := 118140960795 + 167177 * 2 ^ 59
def prefixEnd_167177 : Nat := 4983230072969 + 3 ^ 40 * 167177 * 2
def baseEnd_167177 : Nat := 38152069056354512408299

theorem tailTrace_167177 : CollatzResearch.WordTrace tailWord_167177 prefixEnd_167177 38152069056354512408299 := by
  unfold tailWord_167177
  simp only [CollatzResearch.WordTrace]
  refine ⟨6097446115353755403603785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4064964076902503602402523 6097446115353755403603785)
  ·
    refine ⟨4573084586515316552702839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6097446115353755403603785 4573084586515316552702839)
    ·
      refine ⟨6859626879772974829054259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4573084586515316552702839 6859626879772974829054259)
      ·
        refine ⟨10289440319659462243581389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6859626879772974829054259 10289440319659462243581389)
        ·
          refine ⟨3858540119872298341343021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10289440319659462243581389 3858540119872298341343021)
          ·
            refine ⟨1446952544952111878003633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3858540119872298341343021 1446952544952111878003633)
            ·
              refine ⟨1085214408714083908502725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1446952544952111878003633 1085214408714083908502725)
              ·
                refine ⟨203477701633890732844261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1085214408714083908502725 203477701633890732844261)
                ·
                  refine ⟨38152069056354512408299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 203477701633890732844261 38152069056354512408299)
                  ·
                    rfl

theorem cell21_167177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 4, 4].length) (baseStart_167177 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_167177 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_167177 prefixEnd_167177 := by exact prefixLift 167177
  have htrace : WordTrace (prefixWord ++ tailWord_167177) baseStart_167177 baseEnd_167177 := by
    simpa [prefixWord, tailWord_167177, baseEnd_167177] using wordTrace_append hprefix tailTrace_167177
  have hstable : (prefixWord ++ tailWord_167177).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167177).length < 2 ^ (prefixWord ++ tailWord_167177).sum := by decide
  have hdescent : baseEnd_167177 < baseStart_167177 := by decide
  rcases family_descends (prefixWord ++ tailWord_167177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167186 : List Nat := [3, 2, 4, 2, 2, 1, 2, 1, 4]
def baseStart_167186 : Nat := 118140960795 + 167186 * 2 ^ 59
def prefixEnd_167186 : Nat := 4983230072969 + 3 ^ 40 * 167186 * 2
def baseEnd_167186 : Nat := 38154122978972496758281

theorem tailTrace_167186 : CollatzResearch.WordTrace tailWord_167186 prefixEnd_167186 38154122978972496758281 := by
  unfold tailWord_167186
  simp only [CollatzResearch.WordTrace]
  refine ⟨1524443593080287485170353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4065182914880766627120941 1524443593080287485170353)
  ·
    refine ⟨1143332694810215613877765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1524443593080287485170353 1143332694810215613877765)
    ·
      refine ⟨214374880276915427602081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1143332694810215613877765 214374880276915427602081)
      ·
        refine ⟨160781160207686570701561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 214374880276915427602081 160781160207686570701561)
        ·
          refine ⟨120585870155764928026171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160781160207686570701561 120585870155764928026171)
          ·
            refine ⟨180878805233647392039257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120585870155764928026171 180878805233647392039257)
            ·
              refine ⟨135659103925235544029443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 180878805233647392039257 135659103925235544029443)
              ·
                refine ⟨203488655887853316044165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 135659103925235544029443 203488655887853316044165)
                ·
                  refine ⟨38154122978972496758281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 203488655887853316044165 38154122978972496758281)
                  ·
                    rfl

theorem cell21_167186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 2, 1, 4].length) (baseStart_167186 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_167186 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_167186 prefixEnd_167186 := by exact prefixLift 167186
  have htrace : WordTrace (prefixWord ++ tailWord_167186) baseStart_167186 baseEnd_167186 := by
    simpa [prefixWord, tailWord_167186, baseEnd_167186] using wordTrace_append hprefix tailTrace_167186
  have hstable : (prefixWord ++ tailWord_167186).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167186).length < 2 ^ (prefixWord ++ tailWord_167186).sum := by decide
  have hdescent : baseEnd_167186 < baseStart_167186 := by decide
  rcases family_descends (prefixWord ++ tailWord_167186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167194 : List Nat := [3, 1, 1, 3, 3, 2, 1, 3, 4]
def baseStart_167194 : Nat := 118140960795 + 167194 * 2 ^ 59
def prefixEnd_167194 : Nat := 4983230072969 + 3 ^ 40 * 167194 * 2
def baseEnd_167194 : Nat := 38155948687966260624931

theorem tailTrace_167194 : CollatzResearch.WordTrace tailWord_167194 prefixEnd_167194 38155948687966260624931 := by
  unfold tailWord_167194
  simp only [CollatzResearch.WordTrace]
  refine ⟨1524516539073041826743159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4065377437528111537981757 1524516539073041826743159)
  ·
    refine ⟨2286774808609562740114739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1524516539073041826743159 2286774808609562740114739)
    ·
      refine ⟨3430162212914344110172109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2286774808609562740114739 3430162212914344110172109)
      ·
        refine ⟨1286310829842879041314541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3430162212914344110172109 1286310829842879041314541)
        ·
          refine ⟨482366561191079640492953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1286310829842879041314541 482366561191079640492953)
          ·
            refine ⟨361774920893309730369715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 482366561191079640492953 361774920893309730369715)
            ·
              refine ⟨542662381339964595554573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 361774920893309730369715 542662381339964595554573)
              ·
                refine ⟨203498393002486723332965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 542662381339964595554573 203498393002486723332965)
                ·
                  refine ⟨38155948687966260624931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 203498393002486723332965 38155948687966260624931)
                  ·
                    rfl

theorem cell21_167194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 3, 4].length) (baseStart_167194 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_167194 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_167194 prefixEnd_167194 := by exact prefixLift 167194
  have htrace : WordTrace (prefixWord ++ tailWord_167194) baseStart_167194 baseEnd_167194 := by
    simpa [prefixWord, tailWord_167194, baseEnd_167194] using wordTrace_append hprefix tailTrace_167194
  have hstable : (prefixWord ++ tailWord_167194).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167194).length < 2 ^ (prefixWord ++ tailWord_167194).sum := by decide
  have hdescent : baseEnd_167194 < baseStart_167194 := by decide
  rcases family_descends (prefixWord ++ tailWord_167194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167208 : List Nat := [2, 1, 5, 1, 2, 1, 2, 7]
def baseStart_167208 : Nat := 118140960795 + 167208 * 2 ^ 59
def prefixEnd_167208 : Nat := 4983230072969 + 3 ^ 40 * 167208 * 2
def baseEnd_167208 : Nat := 12719714559568449130523

theorem tailTrace_167208 : CollatzResearch.WordTrace tailWord_167208 prefixEnd_167208 12719714559568449130523 := by
  unfold tailWord_167208
  simp only [CollatzResearch.WordTrace]
  refine ⟨3049288389120723848991139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4065717852160965131988185 3049288389120723848991139)
  ·
    refine ⟨4573932583681085773486709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3049288389120723848991139 4573932583681085773486709)
    ·
      refine ⟨428806179720101791264379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4573932583681085773486709 428806179720101791264379)
      ·
        refine ⟨643209269580152686896569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 428806179720101791264379 643209269580152686896569)
        ·
          refine ⟨482406952185114515172427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 643209269580152686896569 482406952185114515172427)
          ·
            refine ⟨723610428277671772758641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 482406952185114515172427 723610428277671772758641)
            ·
              refine ⟨542707821208253829568981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 723610428277671772758641 542707821208253829568981)
              ·
                refine ⟨12719714559568449130523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 542707821208253829568981 12719714559568449130523)
                ·
                  rfl

theorem cell21_167208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 7].length) (baseStart_167208 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_167208 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_167208 prefixEnd_167208 := by exact prefixLift 167208
  have htrace : WordTrace (prefixWord ++ tailWord_167208) baseStart_167208 baseEnd_167208 := by
    simpa [prefixWord, tailWord_167208, baseEnd_167208] using wordTrace_append hprefix tailTrace_167208
  have hstable : (prefixWord ++ tailWord_167208).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167208).length < 2 ^ (prefixWord ++ tailWord_167208).sum := by decide
  have hdescent : baseEnd_167208 < baseStart_167208 := by decide
  rcases family_descends (prefixWord ++ tailWord_167208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167349 : List Nat := [1, 3, 3, 2, 2, 2, 3, 2, 3]
def baseStart_167349 : Nat := 118140960795 + 167349 * 2 ^ 59
def prefixEnd_167349 : Nat := 4983230072969 + 3 ^ 40 * 167349 * 2
def baseEnd_167349 : Nat := 38191321799720435541281

theorem tailTrace_167349 : CollatzResearch.WordTrace tailWord_167349 prefixEnd_167349 38191321799720435541281 := by
  unfold tailWord_167349
  simp only [CollatzResearch.WordTrace]
  refine ⟨6103719470730628778865101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4069146313820419185910067 6103719470730628778865101)
  ·
    refine ⟨2288894801523985792074413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6103719470730628778865101 2288894801523985792074413)
    ·
      refine ⟨858335550571494672027905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2288894801523985792074413 858335550571494672027905)
      ·
        refine ⟨643751662928621004020929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 858335550571494672027905 643751662928621004020929)
        ·
          refine ⟨482813747196465753015697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 643751662928621004020929 482813747196465753015697)
          ·
            refine ⟨362110310397349314761773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 482813747196465753015697 362110310397349314761773)
            ·
              refine ⟨135791366399005993035665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 362110310397349314761773 135791366399005993035665)
              ·
                refine ⟨101843524799254494776749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 135791366399005993035665 101843524799254494776749)
                ·
                  refine ⟨38191321799720435541281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 101843524799254494776749 38191321799720435541281)
                  ·
                    rfl

theorem cell21_167349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 3, 2, 3].length) (baseStart_167349 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_167349 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_167349 prefixEnd_167349 := by exact prefixLift 167349
  have htrace : WordTrace (prefixWord ++ tailWord_167349) baseStart_167349 baseEnd_167349 := by
    simpa [prefixWord, tailWord_167349, baseEnd_167349] using wordTrace_append hprefix tailTrace_167349
  have hstable : (prefixWord ++ tailWord_167349).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167349).length < 2 ^ (prefixWord ++ tailWord_167349).sum := by decide
  have hdescent : baseEnd_167349 < baseStart_167349 := by decide
  rcases family_descends (prefixWord ++ tailWord_167349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167374 : List Nat := [4, 1, 1, 1, 2, 1, 2, 4, 5]
def baseStart_167374 : Nat := 118140960795 + 167374 * 2 ^ 59
def prefixEnd_167374 : Nat := 4983230072969 + 3 ^ 40 * 167374 * 2
def baseEnd_167374 : Nat := 38197027140325947624563

theorem tailTrace_167374 : CollatzResearch.WordTrace tailWord_167374 prefixEnd_167374 38197027140325947624563 := by
  unfold tailWord_167374
  simp only [CollatzResearch.WordTrace]
  refine ⟨763078911955007256065647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4069754197093372032350117 763078911955007256065647)
  ·
    refine ⟨1144618367932510884098471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 763078911955007256065647 1144618367932510884098471)
    ·
      refine ⟨1716927551898766326147707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1144618367932510884098471 1716927551898766326147707)
      ·
        refine ⟨2575391327848149489221561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1716927551898766326147707 2575391327848149489221561)
        ·
          refine ⟨1931543495886112116916171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2575391327848149489221561 1931543495886112116916171)
          ·
            refine ⟨2897315243829168175374257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1931543495886112116916171 2897315243829168175374257)
            ·
              refine ⟨2172986432871876131530693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2897315243829168175374257 2172986432871876131530693)
              ·
                refine ⟨407434956163476774662005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2172986432871876131530693 407434956163476774662005)
                ·
                  refine ⟨38197027140325947624563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 407434956163476774662005 38197027140325947624563)
                  ·
                    rfl

theorem cell21_167374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 4, 5].length) (baseStart_167374 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_167374 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_167374 prefixEnd_167374 := by exact prefixLift 167374
  have htrace : WordTrace (prefixWord ++ tailWord_167374) baseStart_167374 baseEnd_167374 := by
    simpa [prefixWord, tailWord_167374, baseEnd_167374] using wordTrace_append hprefix tailTrace_167374
  have hstable : (prefixWord ++ tailWord_167374).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167374).length < 2 ^ (prefixWord ++ tailWord_167374).sum := by decide
  have hdescent : baseEnd_167374 < baseStart_167374 := by decide
  rcases family_descends (prefixWord ++ tailWord_167374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167391 : List Nat := [1, 1, 2, 3, 3, 1, 2, 5, 3]
def baseStart_167391 : Nat := 118140960795 + 167391 * 2 ^ 59
def prefixEnd_167391 : Nat := 4983230072969 + 3 ^ 40 * 167391 * 2
def baseEnd_167391 : Nat := 38200906771937695841195

theorem tailTrace_167391 : CollatzResearch.WordTrace tailWord_167391 prefixEnd_167391 38200906771937695841195 := by
  unfold tailWord_167391
  simp only [CollatzResearch.WordTrace]
  refine ⟨6105251336578469951894027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4070167557718979967929351 6105251336578469951894027)
  ·
    refine ⟨9157877004867704927841041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6105251336578469951894027 9157877004867704927841041)
    ·
      refine ⟨6868407753650778695880781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9157877004867704927841041 6868407753650778695880781)
      ·
        refine ⟨2575652907619042010955293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6868407753650778695880781 2575652907619042010955293)
        ·
          refine ⟨965869840357140754108235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2575652907619042010955293 965869840357140754108235)
          ·
            refine ⟨1448804760535711131162353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 965869840357140754108235 1448804760535711131162353)
            ·
              refine ⟨1086603570401783348371765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1448804760535711131162353 1086603570401783348371765)
              ·
                refine ⟨101869084725167188909853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1086603570401783348371765 101869084725167188909853)
                ·
                  refine ⟨38200906771937695841195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 101869084725167188909853 38200906771937695841195)
                  ·
                    rfl

theorem cell21_167391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 5, 3].length) (baseStart_167391 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_167391 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_167391 prefixEnd_167391 := by exact prefixLift 167391
  have htrace : WordTrace (prefixWord ++ tailWord_167391) baseStart_167391 baseEnd_167391 := by
    simpa [prefixWord, tailWord_167391, baseEnd_167391] using wordTrace_append hprefix tailTrace_167391
  have hstable : (prefixWord ++ tailWord_167391).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167391).length < 2 ^ (prefixWord ++ tailWord_167391).sum := by decide
  have hdescent : baseEnd_167391 < baseStart_167391 := by decide
  rcases family_descends (prefixWord ++ tailWord_167391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167408 : List Nat := [2, 1, 1, 1, 3, 4, 4, 2, 3]
def baseStart_167408 : Nat := 118140960795 + 167408 * 2 ^ 59
def prefixEnd_167408 : Nat := 4983230072969 + 3 ^ 40 * 167408 * 2
def baseEnd_167408 : Nat := 38204786403549444057827

theorem tailTrace_167408 : CollatzResearch.WordTrace tailWord_167408 prefixEnd_167408 38204786403549444057827 := by
  unfold tailWord_167408
  simp only [CollatzResearch.WordTrace]
  refine ⟨3052935688758440927631439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4070580918344587903508585 3052935688758440927631439)
  ·
    refine ⟨4579403533137661391447159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3052935688758440927631439 4579403533137661391447159)
    ·
      refine ⟨6869105299706492087170739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4579403533137661391447159 6869105299706492087170739)
      ·
        refine ⟨10303657949559738130756109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6869105299706492087170739 10303657949559738130756109)
        ·
          refine ⟨3863871731084901799033541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10303657949559738130756109 3863871731084901799033541)
          ·
            refine ⟨724475949578419087318789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3863871731084901799033541 724475949578419087318789)
            ·
              refine ⟨135839240545953578872273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 724475949578419087318789 135839240545953578872273)
              ·
                refine ⟨101879430409465184154205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 135839240545953578872273 101879430409465184154205)
                ·
                  refine ⟨38204786403549444057827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 101879430409465184154205 38204786403549444057827)
                  ·
                    rfl

theorem cell21_167408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 4, 2, 3].length) (baseStart_167408 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_167408 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_167408 prefixEnd_167408 := by exact prefixLift 167408
  have htrace : WordTrace (prefixWord ++ tailWord_167408) baseStart_167408 baseEnd_167408 := by
    simpa [prefixWord, tailWord_167408, baseEnd_167408] using wordTrace_append hprefix tailTrace_167408
  have hstable : (prefixWord ++ tailWord_167408).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167408).length < 2 ^ (prefixWord ++ tailWord_167408).sum := by decide
  have hdescent : baseEnd_167408 < baseStart_167408 := by decide
  rcases family_descends (prefixWord ++ tailWord_167408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167588 : List Nat := [2, 3, 1, 2, 2, 4, 1, 6]
def baseStart_167588 : Nat := 118140960795 + 167588 * 2 ^ 59
def prefixEnd_167588 : Nat := 4983230072969 + 3 ^ 40 * 167588 * 2
def baseEnd_167588 : Nat := 12748621618636377019153

theorem tailTrace_167588 : CollatzResearch.WordTrace tailWord_167588 prefixEnd_167588 12748621618636377019153 := by
  unfold tailWord_167588
  simp only [CollatzResearch.WordTrace]
  refine ⟨3056218258432386298407709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4074957677909848397876945 3056218258432386298407709)
  ·
    refine ⟨1146081846912144861902891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3056218258432386298407709 1146081846912144861902891)
    ·
      refine ⟨1719122770368217292854337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1146081846912144861902891 1719122770368217292854337)
      ·
        refine ⟨1289342077776162969640753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1719122770368217292854337 1289342077776162969640753)
        ·
          refine ⟨967006558332122227230565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1289342077776162969640753 967006558332122227230565)
          ·
            refine ⟨181313729687272917605731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 967006558332122227230565 181313729687272917605731)
            ·
              refine ⟨271970594530909376408597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 181313729687272917605731 271970594530909376408597)
              ·
                refine ⟨12748621618636377019153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 271970594530909376408597 12748621618636377019153)
                ·
                  rfl

theorem cell21_167588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 6].length) (baseStart_167588 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_167588 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_167588 prefixEnd_167588 := by exact prefixLift 167588
  have htrace : WordTrace (prefixWord ++ tailWord_167588) baseStart_167588 baseEnd_167588 := by
    simpa [prefixWord, tailWord_167588, baseEnd_167588] using wordTrace_append hprefix tailTrace_167588
  have hstable : (prefixWord ++ tailWord_167588).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167588).length < 2 ^ (prefixWord ++ tailWord_167588).sum := by decide
  have hdescent : baseEnd_167588 < baseStart_167588 := by decide
  rcases family_descends (prefixWord ++ tailWord_167588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167605 : List Nat := [1, 3, 3, 3, 2, 1, 3, 5]
def baseStart_167605 : Nat := 118140960795 + 167605 * 2 ^ 59
def prefixEnd_167605 : Nat := 4983230072969 + 3 ^ 40 * 167605 * 2
def baseEnd_167605 : Nat := 12749914829173626424697

theorem tailTrace_167605 : CollatzResearch.WordTrace tailWord_167605 prefixEnd_167605 12749914829173626424697 := by
  unfold tailWord_167605
  simp only [CollatzResearch.WordTrace]
  refine ⟨6113056557803184500184269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4075371038535456333456179 6113056557803184500184269)
  ·
    refine ⟨2292396209176194187569101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6113056557803184500184269 2292396209176194187569101)
    ·
      refine ⟨859648578441072820338413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2292396209176194187569101 859648578441072820338413)
      ·
        refine ⟨322368216915402307626905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 859648578441072820338413 322368216915402307626905)
        ·
          refine ⟨241776162686551730720179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 322368216915402307626905 241776162686551730720179)
          ·
            refine ⟨362664244029827596080269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241776162686551730720179 362664244029827596080269)
            ·
              refine ⟨135999091511185348530101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 362664244029827596080269 135999091511185348530101)
              ·
                refine ⟨12749914829173626424697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 135999091511185348530101 12749914829173626424697)
                ·
                  rfl

theorem cell21_167605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 3, 5].length) (baseStart_167605 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_167605 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_167605 prefixEnd_167605 := by exact prefixLift 167605
  have htrace : WordTrace (prefixWord ++ tailWord_167605) baseStart_167605 baseEnd_167605 := by
    simpa [prefixWord, tailWord_167605, baseEnd_167605] using wordTrace_append hprefix tailTrace_167605
  have hstable : (prefixWord ++ tailWord_167605).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167605).length < 2 ^ (prefixWord ++ tailWord_167605).sum := by decide
  have hdescent : baseEnd_167605 < baseStart_167605 := by decide
  rcases family_descends (prefixWord ++ tailWord_167605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167616 : List Nat := [2, 1, 1, 2, 4, 1, 2, 2, 6]
def baseStart_167616 : Nat := 118140960795 + 167616 * 2 ^ 59
def prefixEnd_167616 : Nat := 4983230072969 + 3 ^ 40 * 167616 * 2
def baseEnd_167616 : Nat := 38252254837387304590735

theorem tailTrace_167616 : CollatzResearch.WordTrace tailWord_167616 prefixEnd_167616 38252254837387304590735 := by
  unfold tailWord_167616
  simp only [CollatzResearch.WordTrace]
  refine ⟨3056728880381666689417351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4075638507175555585889801 3056728880381666689417351)
  ·
    refine ⟨4585093320572500034126027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3056728880381666689417351 4585093320572500034126027)
    ·
      refine ⟨6877639980858750051189041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4585093320572500034126027 6877639980858750051189041)
      ·
        refine ⟨5158229985644062538391781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6877639980858750051189041 5158229985644062538391781)
        ·
          refine ⟨967168122308261725948459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5158229985644062538391781 967168122308261725948459)
          ·
            refine ⟨1450752183462392588922689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 967168122308261725948459 1450752183462392588922689)
            ·
              refine ⟨1088064137596794441692017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1450752183462392588922689 1088064137596794441692017)
              ·
                refine ⟨816048103197595831269013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1088064137596794441692017 816048103197595831269013)
                ·
                  refine ⟨38252254837387304590735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 816048103197595831269013 38252254837387304590735)
                  ·
                    rfl

theorem cell21_167616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 2, 6].length) (baseStart_167616 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_167616 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_167616 prefixEnd_167616 := by exact prefixLift 167616
  have htrace : WordTrace (prefixWord ++ tailWord_167616) baseStart_167616 baseEnd_167616 := by
    simpa [prefixWord, tailWord_167616, baseEnd_167616] using wordTrace_append hprefix tailTrace_167616
  have hstable : (prefixWord ++ tailWord_167616).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167616).length < 2 ^ (prefixWord ++ tailWord_167616).sum := by decide
  have hdescent : baseEnd_167616 < baseStart_167616 := by decide
  rcases family_descends (prefixWord ++ tailWord_167616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167633 : List Nat := [1, 2, 2, 1, 2, 4, 3, 2, 4]
def baseStart_167633 : Nat := 118140960795 + 167633 * 2 ^ 59
def prefixEnd_167633 : Nat := 4983230072969 + 3 ^ 40 * 167633 * 2
def baseEnd_167633 : Nat := 38256134468999052807367

theorem tailTrace_167633 : CollatzResearch.WordTrace tailWord_167633 prefixEnd_167633 38256134468999052807367 := by
  unfold tailWord_167633
  simp only [CollatzResearch.WordTrace]
  refine ⟨6114077801701745282203553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4076051867801163521469035 6114077801701745282203553)
  ·
    refine ⟨4585558351276308961652665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6114077801701745282203553 4585558351276308961652665)
    ·
      refine ⟨3439168763457231721239499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4585558351276308961652665 3439168763457231721239499)
      ·
        refine ⟨5158753145185847581859249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3439168763457231721239499 5158753145185847581859249)
        ·
          refine ⟨3869064858889385686394437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5158753145185847581859249 3869064858889385686394437)
          ·
            refine ⟨725449661041759816198957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3869064858889385686394437 725449661041759816198957)
            ·
              refine ⟨272043622890659931074609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 725449661041759816198957 272043622890659931074609)
              ·
                refine ⟨204032717167994948305957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 272043622890659931074609 204032717167994948305957)
                ·
                  refine ⟨38256134468999052807367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 204032717167994948305957 38256134468999052807367)
                  ·
                    rfl

theorem cell21_167633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 2, 4].length) (baseStart_167633 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_167633 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_167633 prefixEnd_167633 := by exact prefixLift 167633
  have htrace : WordTrace (prefixWord ++ tailWord_167633) baseStart_167633 baseEnd_167633 := by
    simpa [prefixWord, tailWord_167633, baseEnd_167633] using wordTrace_append hprefix tailTrace_167633
  have hstable : (prefixWord ++ tailWord_167633).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167633).length < 2 ^ (prefixWord ++ tailWord_167633).sum := by decide
  have hdescent : baseEnd_167633 < baseStart_167633 := by decide
  rcases family_descends (prefixWord ++ tailWord_167633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167636 : List Nat := [2, 4, 1, 3, 1, 1, 2, 4, 3]
def baseStart_167636 : Nat := 118140960795 + 167636 * 2 ^ 59
def prefixEnd_167636 : Nat := 4983230072969 + 3 ^ 40 * 167636 * 2
def baseEnd_167636 : Nat := 38256819109871714257361

theorem tailTrace_167636 : CollatzResearch.WordTrace tailWord_167636 prefixEnd_167636 38256819109871714257361 := by
  unfold tailWord_167636
  simp only [CollatzResearch.WordTrace]
  refine ⟨3057093610345438397281381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4076124813793917863041841 3057093610345438397281381)
  ·
    refine ⟨573205051939769699490259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3057093610345438397281381 573205051939769699490259)
    ·
      refine ⟨859807577909654549235389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 573205051939769699490259 859807577909654549235389)
      ·
        refine ⟨322427841716120455963271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 859807577909654549235389 322427841716120455963271)
        ·
          refine ⟨483641762574180683944907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 322427841716120455963271 483641762574180683944907)
          ·
            refine ⟨725462643861271025917361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 483641762574180683944907 725462643861271025917361)
            ·
              refine ⟨544096982895953269438021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 725462643861271025917361 544096982895953269438021)
              ·
                refine ⟨102018184292991238019629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 544096982895953269438021 102018184292991238019629)
                ·
                  refine ⟨38256819109871714257361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 102018184292991238019629 38256819109871714257361)
                  ·
                    rfl

theorem cell21_167636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 4, 3].length) (baseStart_167636 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_167636 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_167636 prefixEnd_167636 := by exact prefixLift 167636
  have htrace : WordTrace (prefixWord ++ tailWord_167636) baseStart_167636 baseEnd_167636 := by
    simpa [prefixWord, tailWord_167636, baseEnd_167636] using wordTrace_append hprefix tailTrace_167636
  have hstable : (prefixWord ++ tailWord_167636).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167636).length < 2 ^ (prefixWord ++ tailWord_167636).sum := by decide
  have hdescent : baseEnd_167636 < baseStart_167636 := by decide
  rcases family_descends (prefixWord ++ tailWord_167636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167692 : List Nat := [2, 2, 1, 2, 2, 1, 4, 1, 6]
def baseStart_167692 : Nat := 118140960795 + 167692 * 2 ^ 59
def prefixEnd_167692 : Nat := 4983230072969 + 3 ^ 40 * 167692 * 2
def baseEnd_167692 : Nat := 38269599072828061323913

theorem tailTrace_167692 : CollatzResearch.WordTrace tailWord_167692 prefixEnd_167692 38269599072828061323913 := by
  unfold tailWord_167692
  simp only [CollatzResearch.WordTrace]
  refine ⟨3058114854243999179300665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4077486472325332239067553 3058114854243999179300665)
  ·
    refine ⟨2293586140682999384475499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3058114854243999179300665 2293586140682999384475499)
    ·
      refine ⟨3440379211024499076713249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2293586140682999384475499 3440379211024499076713249)
      ·
        refine ⟨2580284408268374307534937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3440379211024499076713249 2580284408268374307534937)
        ·
          refine ⟨1935213306201280730651203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2580284408268374307534937 1935213306201280730651203)
          ·
            refine ⟨2902819959301921095976805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1935213306201280730651203 2902819959301921095976805)
            ·
              refine ⟨544278742369110205495651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2902819959301921095976805 544278742369110205495651)
              ·
                refine ⟨816418113553665308243477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 544278742369110205495651 816418113553665308243477)
                ·
                  refine ⟨38269599072828061323913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 816418113553665308243477 38269599072828061323913)
                  ·
                    rfl

theorem cell21_167692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 1, 6].length) (baseStart_167692 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_167692 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_167692 prefixEnd_167692 := by exact prefixLift 167692
  have htrace : WordTrace (prefixWord ++ tailWord_167692) baseStart_167692 baseEnd_167692 := by
    simpa [prefixWord, tailWord_167692, baseEnd_167692] using wordTrace_append hprefix tailTrace_167692
  have hstable : (prefixWord ++ tailWord_167692).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167692).length < 2 ^ (prefixWord ++ tailWord_167692).sum := by decide
  have hdescent : baseEnd_167692 < baseStart_167692 := by decide
  rcases family_descends (prefixWord ++ tailWord_167692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167757 : List Nat := [1, 6, 1, 2, 1, 3, 1, 6]
def baseStart_167757 : Nat := 118140960795 + 167757 * 2 ^ 59
def prefixEnd_167757 : Nat := 4983230072969 + 3 ^ 40 * 167757 * 2
def baseEnd_167757 : Nat := 12761477652800797580149

theorem tailTrace_167757 : CollatzResearch.WordTrace tailWord_167757 prefixEnd_167757 12761477652800797580149 := by
  unfold tailWord_167757
  simp only [CollatzResearch.WordTrace]
  refine ⟨6118600453252514459717525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4079066968835009639811683 6118600453252514459717525)
  ·
    refine ⟨286809396246211615299259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 6118600453252514459717525 286809396246211615299259)
    ·
      refine ⟨430214094369317422948889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286809396246211615299259 430214094369317422948889)
      ·
        refine ⟨322660570776988067211667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 430214094369317422948889 322660570776988067211667)
        ·
          refine ⟨483990856165482100817501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 322660570776988067211667 483990856165482100817501)
          ·
            refine ⟨181496571062055787806563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 483990856165482100817501 181496571062055787806563)
            ·
              refine ⟨272244856593083681709845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 181496571062055787806563 272244856593083681709845)
              ·
                refine ⟨12761477652800797580149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 272244856593083681709845 12761477652800797580149)
                ·
                  rfl

theorem cell21_167757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 6].length) (baseStart_167757 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_167757 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_167757 prefixEnd_167757 := by exact prefixLift 167757
  have htrace : WordTrace (prefixWord ++ tailWord_167757) baseStart_167757 baseEnd_167757 := by
    simpa [prefixWord, tailWord_167757, baseEnd_167757] using wordTrace_append hprefix tailTrace_167757
  have hstable : (prefixWord ++ tailWord_167757).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167757).length < 2 ^ (prefixWord ++ tailWord_167757).sum := by decide
  have hdescent : baseEnd_167757 < baseStart_167757 := by decide
  rcases family_descends (prefixWord ++ tailWord_167757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167844 : List Nat := [2, 3, 1, 2, 1, 3, 1, 2, 6]
def baseStart_167844 : Nat := 118140960795 + 167844 * 2 ^ 59
def prefixEnd_167844 : Nat := 4983230072969 + 3 ^ 40 * 167844 * 2
def baseEnd_167844 : Nat := 38304287543709574790269

theorem tailTrace_167844 : CollatzResearch.WordTrace tailWord_167844 prefixEnd_167844 38304287543709574790269 := by
  unfold tailWord_167844
  simp only [CollatzResearch.WordTrace]
  refine ⟨3060886801968664159067293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4081182402624885545423057 3060886801968664159067293)
  ·
    refine ⟨1147832550738249059650235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3060886801968664159067293 1147832550738249059650235)
    ·
      refine ⟨1721748826107373589475353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1147832550738249059650235 1721748826107373589475353)
      ·
        refine ⟨1291311619580530192106515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1721748826107373589475353 1291311619580530192106515)
        ·
          refine ⟨1936967429370795288159773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1291311619580530192106515 1936967429370795288159773)
          ·
            refine ⟨726362786014048233059915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1936967429370795288159773 726362786014048233059915)
            ·
              refine ⟨1089544179021072349589873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 726362786014048233059915 1089544179021072349589873)
              ·
                refine ⟨817158134265804262192405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1089544179021072349589873 817158134265804262192405)
                ·
                  refine ⟨38304287543709574790269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 817158134265804262192405 38304287543709574790269)
                  ·
                    rfl

theorem cell21_167844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 2, 6].length) (baseStart_167844 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_167844 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_167844 prefixEnd_167844 := by exact prefixLift 167844
  have htrace : WordTrace (prefixWord ++ tailWord_167844) baseStart_167844 baseEnd_167844 := by
    simpa [prefixWord, tailWord_167844, baseEnd_167844] using wordTrace_append hprefix tailTrace_167844
  have hstable : (prefixWord ++ tailWord_167844).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167844).length < 2 ^ (prefixWord ++ tailWord_167844).sum := by decide
  have hdescent : baseEnd_167844 < baseStart_167844 := by decide
  rcases family_descends (prefixWord ++ tailWord_167844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167920 : List Nat := [2, 1, 1, 1, 3, 2, 3, 4, 4]
def baseStart_167920 : Nat := 118140960795 + 167920 * 2 ^ 59
def prefixEnd_167920 : Nat := 4983230072969 + 3 ^ 40 * 167920 * 2
def baseEnd_167920 : Nat := 38321631779150331523447

theorem tailTrace_167920 : CollatzResearch.WordTrace tailWord_167920 prefixEnd_167920 38321631779150331523447 := by
  unfold tailWord_167920
  simp only [CollatzResearch.WordTrace]
  refine ⟨3062272775830996648950607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4083030367774662198600809 3062272775830996648950607)
  ·
    refine ⟨4593409163746494973425911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3062272775830996648950607 4593409163746494973425911)
    ·
      refine ⟨6890113745619742460138867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4593409163746494973425911 6890113745619742460138867)
      ·
        refine ⟨10335170618429613690208301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6890113745619742460138867 10335170618429613690208301)
        ·
          refine ⟨3875688981911105133828113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10335170618429613690208301 3875688981911105133828113)
          ·
            refine ⟨2906766736433328850371085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3875688981911105133828113 2906766736433328850371085)
            ·
              refine ⟨1090037526162498318889157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2906766736433328850371085 1090037526162498318889157)
              ·
                refine ⟨204382036155468434791717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1090037526162498318889157 204382036155468434791717)
                ·
                  refine ⟨38321631779150331523447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 204382036155468434791717 38321631779150331523447)
                  ·
                    rfl

theorem cell21_167920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 4, 4].length) (baseStart_167920 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_167920 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_167920 prefixEnd_167920 := by exact prefixLift 167920
  have htrace : WordTrace (prefixWord ++ tailWord_167920) baseStart_167920 baseEnd_167920 := by
    simpa [prefixWord, tailWord_167920, baseEnd_167920] using wordTrace_append hprefix tailTrace_167920
  have hstable : (prefixWord ++ tailWord_167920).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167920).length < 2 ^ (prefixWord ++ tailWord_167920).sum := by decide
  have hdescent : baseEnd_167920 < baseStart_167920 := by decide
  rcases family_descends (prefixWord ++ tailWord_167920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167982 : List Nat := [4, 1, 3, 1, 1, 2, 1, 3, 5]
def baseStart_167982 : Nat := 118140960795 + 167982 * 2 ^ 59
def prefixEnd_167982 : Nat := 4983230072969 + 3 ^ 40 * 167982 * 2
def baseEnd_167982 : Nat := 38335781023852001489987

theorem tailTrace_167982 : CollatzResearch.WordTrace tailWord_167982 prefixEnd_167982 38335781023852001489987 := by
  unfold tailWord_167982
  simp only [CollatzResearch.WordTrace]
  refine ⟨765850859679672235832275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4084537918291585257772133 765850859679672235832275)
  ·
    refine ⟨1148776289519508353748413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 765850859679672235832275 1148776289519508353748413)
    ·
      refine ⟨430791108569815632655655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1148776289519508353748413 430791108569815632655655)
      ·
        refine ⟨646186662854723448983483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 430791108569815632655655 646186662854723448983483)
        ·
          refine ⟨969279994282085173475225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 646186662854723448983483 969279994282085173475225)
          ·
            refine ⟨726959995711563880106419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 969279994282085173475225 726959995711563880106419)
            ·
              refine ⟨1090439993567345820159629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 726959995711563880106419 1090439993567345820159629)
              ·
                refine ⟨408914997587754682559861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1090439993567345820159629 408914997587754682559861)
                ·
                  refine ⟨38335781023852001489987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 408914997587754682559861 38335781023852001489987)
                  ·
                    rfl

theorem cell21_167982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 3, 5].length) (baseStart_167982 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_167982 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_167982 prefixEnd_167982 := by exact prefixLift 167982
  have htrace : WordTrace (prefixWord ++ tailWord_167982) baseStart_167982 baseEnd_167982 := by
    simpa [prefixWord, tailWord_167982, baseEnd_167982] using wordTrace_append hprefix tailTrace_167982
  have hstable : (prefixWord ++ tailWord_167982).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167982).length < 2 ^ (prefixWord ++ tailWord_167982).sum := by decide
  have hdescent : baseEnd_167982 < baseStart_167982 := by decide
  rcases family_descends (prefixWord ++ tailWord_167982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168196 : List Nat := [2, 3, 2, 2, 4, 1, 7]
def baseStart_168196 : Nat := 118140960795 + 168196 * 2 ^ 59
def prefixEnd_168196 : Nat := 4983230072969 + 3 ^ 40 * 168196 * 2
def baseEnd_168196 : Nat := 4264957637715020546987

theorem tailTrace_168196 : CollatzResearch.WordTrace tailWord_168196 prefixEnd_168196 4264957637715020546987 := by
  unfold tailWord_168196
  simp only [CollatzResearch.WordTrace]
  refine ⟨3067306049331046217474221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4089741399108061623298961 3067306049331046217474221)
  ·
    refine ⟨1150239768499142331552833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3067306049331046217474221 1150239768499142331552833)
    ·
      refine ⟨862679826374356748664625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1150239768499142331552833 862679826374356748664625)
      ·
        refine ⟨647009869780767561498469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 862679826374356748664625 647009869780767561498469)
        ·
          refine ⟨121314350583893917780963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 647009869780767561498469 121314350583893917780963)
          ·
            refine ⟨181971525875840876671445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121314350583893917780963 181971525875840876671445)
            ·
              refine ⟨4264957637715020546987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 181971525875840876671445 4264957637715020546987)
              ·
                rfl

theorem cell21_168196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 7].length) (baseStart_168196 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_168196 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_168196 prefixEnd_168196 := by exact prefixLift 168196
  have htrace : WordTrace (prefixWord ++ tailWord_168196) baseStart_168196 baseEnd_168196 := by
    simpa [prefixWord, tailWord_168196, baseEnd_168196] using wordTrace_append hprefix tailTrace_168196
  have hstable : (prefixWord ++ tailWord_168196).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168196).length < 2 ^ (prefixWord ++ tailWord_168196).sum := by decide
  have hdescent : baseEnd_168196 < baseStart_168196 := by decide
  rcases family_descends (prefixWord ++ tailWord_168196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168317 : List Nat := [1, 4, 1, 1, 2, 5, 1, 2, 4]
def baseStart_168317 : Nat := 118140960795 + 168317 * 2 ^ 59
def prefixEnd_168317 : Nat := 4983230072969 + 3 ^ 40 * 168317 * 2
def baseEnd_168317 : Nat := 38412232587965863405969

theorem tailTrace_168317 : CollatzResearch.WordTrace tailWord_168317 prefixEnd_168317 38412232587965863405969 := by
  unfold tailWord_168317
  simp only [CollatzResearch.WordTrace]
  refine ⟨6139025331223730100103205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4092683554149153400068803 6139025331223730100103205)
  ·
    refine ⟨1151067249604449393769351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6139025331223730100103205 1151067249604449393769351)
    ·
      refine ⟨1726600874406674090654027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1151067249604449393769351 1726600874406674090654027)
      ·
        refine ⟨2589901311610011135981041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1726600874406674090654027 2589901311610011135981041)
        ·
          refine ⟨1942425983707508351985781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2589901311610011135981041 1942425983707508351985781)
          ·
            refine ⟨182102435972578907998667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1942425983707508351985781 182102435972578907998667)
            ·
              refine ⟨273153653958868361998001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 182102435972578907998667 273153653958868361998001)
              ·
                refine ⟨204865240469151271498501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 273153653958868361998001 204865240469151271498501)
                ·
                  refine ⟨38412232587965863405969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 204865240469151271498501 38412232587965863405969)
                  ·
                    rfl

theorem cell21_168317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 2, 4].length) (baseStart_168317 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_168317 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_168317 prefixEnd_168317 := by exact prefixLift 168317
  have htrace : WordTrace (prefixWord ++ tailWord_168317) baseStart_168317 baseEnd_168317 := by
    simpa [prefixWord, tailWord_168317, baseEnd_168317] using wordTrace_append hprefix tailTrace_168317
  have hstable : (prefixWord ++ tailWord_168317).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168317).length < 2 ^ (prefixWord ++ tailWord_168317).sum := by decide
  have hdescent : baseEnd_168317 < baseStart_168317 := by decide
  rcases family_descends (prefixWord ++ tailWord_168317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168334 : List Nat := [4, 1, 1, 4, 1, 2, 3, 1, 4]
def baseStart_168334 : Nat := 118140960795 + 168334 * 2 ^ 59
def prefixEnd_168334 : Nat := 4983230072969 + 3 ^ 40 * 168334 * 2
def baseEnd_168334 : Nat := 38416112219577611622601

theorem tailTrace_168334 : CollatzResearch.WordTrace tailWord_168334 prefixEnd_168334 38416112219577611622601 := by
  unfold tailWord_168334
  simp only [CollatzResearch.WordTrace]
  refine ⟨767455671520267750434007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4093096914774761335648037 767455671520267750434007)
  ·
    refine ⟨1151183507280401625651011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 767455671520267750434007 1151183507280401625651011)
    ·
      refine ⟨1726775260920602438476517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1151183507280401625651011 1726775260920602438476517)
      ·
        refine ⟨323770361422612957214347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1726775260920602438476517 323770361422612957214347)
        ·
          refine ⟨485655542133919435821521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 323770361422612957214347 485655542133919435821521)
          ·
            refine ⟨364241656600439576866141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 485655542133919435821521 364241656600439576866141)
            ·
              refine ⟨136590621225164841324803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 364241656600439576866141 136590621225164841324803)
              ·
                refine ⟨204885931837747261987205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136590621225164841324803 204885931837747261987205)
                ·
                  refine ⟨38416112219577611622601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 204885931837747261987205 38416112219577611622601)
                  ·
                    rfl

theorem cell21_168334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 3, 1, 4].length) (baseStart_168334 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_168334 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_168334 prefixEnd_168334 := by exact prefixLift 168334
  have htrace : WordTrace (prefixWord ++ tailWord_168334) baseStart_168334 baseEnd_168334 := by
    simpa [prefixWord, tailWord_168334, baseEnd_168334] using wordTrace_append hprefix tailTrace_168334
  have hstable : (prefixWord ++ tailWord_168334).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168334).length < 2 ^ (prefixWord ++ tailWord_168334).sum := by decide
  have hdescent : baseEnd_168334 < baseStart_168334 := by decide
  rcases family_descends (prefixWord ++ tailWord_168334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168385 : List Nat := [1, 2, 7, 1, 2, 1, 2, 1, 4]
def baseStart_168385 : Nat := 118140960795 + 168385 * 2 ^ 59
def prefixEnd_168385 : Nat := 4983230072969 + 3 ^ 40 * 168385 * 2
def baseEnd_168385 : Nat := 38427751114412856272497

theorem tailTrace_168385 : CollatzResearch.WordTrace tailWord_168385 prefixEnd_168385 38427751114412856272497 := by
  unfold tailWord_168385
  simp only [CollatzResearch.WordTrace]
  refine ⟨6141505494977377713578609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4094336996651585142385739 6141505494977377713578609)
  ·
    refine ⟨4606129121233033285183957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6141505494977377713578609 4606129121233033285183957)
    ·
      refine ⟨107956151278899217621499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 4606129121233033285183957 107956151278899217621499)
      ·
        refine ⟨161934226918348826432249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107956151278899217621499 161934226918348826432249)
        ·
          refine ⟨121450670188761619824187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161934226918348826432249 121450670188761619824187)
          ·
            refine ⟨182176005283142429736281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121450670188761619824187 182176005283142429736281)
            ·
              refine ⟨136632003962356822302211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 182176005283142429736281 136632003962356822302211)
              ·
                refine ⟨204948005943535233453317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136632003962356822302211 204948005943535233453317)
                ·
                  refine ⟨38427751114412856272497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 204948005943535233453317 38427751114412856272497)
                  ·
                    rfl

theorem cell21_168385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 2, 1, 4].length) (baseStart_168385 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_168385 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_168385 prefixEnd_168385 := by exact prefixLift 168385
  have htrace : WordTrace (prefixWord ++ tailWord_168385) baseStart_168385 baseEnd_168385 := by
    simpa [prefixWord, tailWord_168385, baseEnd_168385] using wordTrace_append hprefix tailTrace_168385
  have hstable : (prefixWord ++ tailWord_168385).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168385).length < 2 ^ (prefixWord ++ tailWord_168385).sum := by decide
  have hdescent : baseEnd_168385 < baseStart_168385 := by decide
  rcases family_descends (prefixWord ++ tailWord_168385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
